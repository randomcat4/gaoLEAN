# ArXiv manuscript

This directory contains the self-contained 13-page manuscript proving

$$
E\bigl(A\rtimes_{-1}C_2\bigr)=2|A|+D(A)
$$

for nontrivial finite abelian `p`-groups `A`, with `p` odd. The checked PDF is
available as [`main.pdf`](main.pdf); the complete LaTeX source is stored beside
it and remains the authoritative build input.

The theorem is deliberately limited to this family. It does not claim a
mixed-prime extension, a `2`-group result, an inverse theorem, or a proof of the
Zhuang--Gao conjecture for every finite group.

## Files

- `main.pdf` - directly readable 13-page paper.
- `main.tex` - master LaTeX source.
- `sections/*.tex` - section sources.
- `references.bib` - bibliography.
- `PROOF-AUDIT.md` - explicit natural-language proof obligations.
- `INDEPENDENT-VERIFICATION.md` - instructions for an independent verifier.
- `BUILD-REPORT.md` - reproducible build facts and PDF checksums.
- `MANIFEST.sha256` - integrity manifest for the public paper bundle.
- `Makefile` - reproducible local build commands.

## Build

A standard TeX installation with `pdflatex`, `bibtex`, `natbib`, `cleveref`,
`aliascnt`, and Latin Modern fonts is sufficient.

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

The public PDF was rebuilt from the committed sources as 13 pages with all
citations and cross-references resolved and with no matched overfull or
underfull box warning. See `BUILD-REPORT.md` for exact tool and hash details.

## Certification

The repository root contains the Lean 4 development and its axiom audit. The
final generalized-dihedral Gao theorem stated in this manuscript has an
unconditional Lean endpoint. The repository-wide verdict nevertheless remains
`PARTIALLY_VERIFIED`, because the manuscript also states a general arbitrary-
weight GMO theorem whose full source range is still being formalized. The root
README and the [manuscript-to-Lean evidence map](../../docs/manuscript-lean-map.md)
record this boundary precisely.

The author field is intentionally blank because author metadata has not been
supplied. It must be completed before an external arXiv submission.
