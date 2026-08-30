#!/usr/bin/env python3
"""Fast, dependency-free checks for the public repository surface."""

from __future__ import annotations

import hashlib
import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PUBLIC_MATH_DOCS = (
    ROOT / "README.md",
    ROOT / "paper" / "arxiv" / "README.md",
    ROOT / "paper" / "arxiv" / "PROOF-AUDIT.md",
)
FORBIDDEN_LEAN = re.compile(
    r"\bsorry\b|\badmit\b|\bsorryAx\b|\bnative_decide\b|"
    r"\bunsafe\b|^\s*axiom\b",
    re.MULTILINE,
)
TABLE_SEPARATOR = re.compile(r"^:?-{3,}:?$")


def fail(errors: list[str], message: str) -> None:
    errors.append(message)


def markdown_cells(line: str) -> list[str]:
    """Split a GitHub Markdown table row at unescaped pipe characters."""
    cells: list[str] = []
    start = 0
    for index, char in enumerate(line):
        if char != "|":
            continue
        backslashes = 0
        cursor = index - 1
        while cursor >= 0 and line[cursor] == "\\":
            backslashes += 1
            cursor -= 1
        if backslashes % 2 == 0:
            cells.append(line[start:index].strip())
            start = index + 1
    cells.append(line[start:].strip())
    if cells and cells[0] == "":
        cells.pop(0)
    if cells and cells[-1] == "":
        cells.pop()
    return cells


def check_markdown_tables(errors: list[str]) -> int:
    table_count = 0
    for path in sorted(ROOT.rglob("*.md")):
        if ".git" in path.parts or ".lake" in path.parts:
            continue
        lines = path.read_text(encoding="utf-8").splitlines()
        for index in range(1, len(lines)):
            if "|" not in lines[index]:
                continue
            separator = markdown_cells(lines[index])
            if not separator or not all(TABLE_SEPARATOR.fullmatch(cell) for cell in separator):
                continue
            expected = len(separator)
            header = markdown_cells(lines[index - 1])
            table_count += 1
            if len(header) != expected:
                fail(
                    errors,
                    f"{path.relative_to(ROOT)}:{index}: table header has "
                    f"{len(header)} cells; expected {expected}",
                )
            row_index = index + 1
            while row_index < len(lines) and "|" in lines[row_index] and lines[row_index].strip():
                cells = markdown_cells(lines[row_index])
                if len(cells) != expected:
                    fail(
                        errors,
                        f"{path.relative_to(ROOT)}:{row_index + 1}: table row has "
                        f"{len(cells)} cells; expected {expected}",
                    )
                row_index += 1
    return table_count


def check_math_delimiters(errors: list[str]) -> None:
    for path in PUBLIC_MATH_DOCS:
        text = path.read_text(encoding="utf-8")
        for token in (r"\(", r"\)", r"\[", r"\]"):
            if token in text:
                fail(errors, f"{path.relative_to(ROOT)} uses unsupported GitHub math delimiter {token!r}")
        for line_number, line in enumerate(text.splitlines(), 1):
            if line.strip() == "$":
                fail(
                    errors,
                    f"{path.relative_to(ROOT)}:{line_number}: display math must use $$, not a lone $",
                )


def check_lean_sources(errors: list[str]) -> int:
    source_count = 0
    for path in sorted(ROOT.rglob("*.lean")):
        if ".lake" in path.parts:
            continue
        source_count += 1
        text = path.read_text(encoding="utf-8")
        match = FORBIDDEN_LEAN.search(text)
        if match:
            line = text.count("\n", 0, match.start()) + 1
            fail(
                errors,
                f"{path.relative_to(ROOT)}:{line}: forbidden declaration/token {match.group(0)!r}",
            )
    return source_count


def check_toolchain_pin(errors: list[str]) -> None:
    toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    match = re.search(
        r'\[\[require\]\]\s*name\s*=\s*"mathlib".*?rev\s*=\s*"([^"]+)"',
        (ROOT / "lakefile.toml").read_text(encoding="utf-8"),
        re.DOTALL,
    )
    if not match:
        fail(errors, "lakefile.toml: cannot find the pinned mathlib revision")
        return
    expected = toolchain.rsplit(":", 1)[-1]
    if match.group(1) != expected:
        fail(
            errors,
            f"toolchain mismatch: lean-toolchain has {expected}, mathlib has {match.group(1)}",
        )


def check_paper_manifest(errors: list[str]) -> int:
    paper_dir = ROOT / "paper" / "arxiv"
    manifest = paper_dir / "MANIFEST.sha256"
    checked = 0
    for line_number, line in enumerate(manifest.read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip():
            continue
        try:
            expected, relative = line.split(None, 1)
        except ValueError:
            fail(errors, f"{manifest.relative_to(ROOT)}:{line_number}: malformed manifest row")
            continue
        target = paper_dir / relative.strip()
        if not target.is_file():
            fail(errors, f"{manifest.relative_to(ROOT)}:{line_number}: missing {relative.strip()}")
            continue
        actual = hashlib.sha256(target.read_bytes()).hexdigest()
        checked += 1
        if actual != expected:
            fail(errors, f"{target.relative_to(ROOT)}: SHA-256 mismatch")
    return checked


def main() -> int:
    errors: list[str] = []
    lean_count = check_lean_sources(errors)
    table_count = check_markdown_tables(errors)
    check_math_delimiters(errors)
    check_toolchain_pin(errors)
    manifest_count = check_paper_manifest(errors)

    if errors:
        print("Repository surface checks failed:", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print(
        f"Repository surface checks passed: {lean_count} Lean sources, "
        f"{table_count} Markdown tables, {manifest_count} paper manifest entries."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
