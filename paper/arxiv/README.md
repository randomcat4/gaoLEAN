# ArXiv manuscript rewrite

This directory contains the paper-first rewrite of the candidate proof

\[
E\bigl(A\rtimes_{-1}C_2\bigr)=2|A|+D(A)
\]

for nontrivial finite abelian `p`-groups `A`, with `p` odd.

The manuscript is deliberately limited to this theorem. It does not claim a mixed-prime extension, an inverse theorem, a reusable general descent theorem, or a larger verification of the Zhuang-Gao conjecture. It also makes no priority claim.

## Files

- `main.tex` - master LaTeX source.
- `sections/*.tex` - section sources.
- `references.bib` - bibliography rebuilt from publisher, DOI, or arXiv metadata.
- `PROOF-AUDIT.md` - explicit proof obligations and all five GMO instances.
- `INDEPENDENT-VERIFICATION.md` - instructions for an independent verifier.
- `REVISION-REPORT.md` - record of material changes from the Claude revision.
- `BUILD-REPORT.md` - exact local build facts and the checked PDF checksum.
- `Makefile` - reproducible local build commands.

## Build

A standard TeX Live installation with `pdflatex`, `bibtex`, `natbib`,
`cleveref`, `aliascnt`, and Latin Modern fonts is sufficient.

```bash
make pdf
```

Equivalent commands are:

```bash
pdflatex -interaction=nonstopmode -halt-on-error main.tex
bibtex main
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

A local build produced a 13-page PDF with resolved references and citations, no
overfull or underfull boxes, and no broken glyphs observed in a page-by-page
render. GitHub Actions failed before executing any job step and supplied no job
log, so this repository does not represent the remote runner as a successful or
failed LaTeX check. The source and Makefile are the reproducible build surface.

## Status and reading order

The result remains a **candidate natural-language proof**, not an independently
certified theorem in this repository. The existence of source files, a compiled
PDF, prior model reviews, or partial formalization is not evidence of correctness.

An independent reviewer should build `main.pdf` from the source, read it without
using the repository navigation or Lean materials, and then check
`PROOF-AUDIT.md` against the original sources. The required audit is described
in `INDEPENDENT-VERIFICATION.md` and issue #8.

The author field is intentionally blank because no author metadata was supplied
for this editing task. It must be completed by the authors before public
submission.
