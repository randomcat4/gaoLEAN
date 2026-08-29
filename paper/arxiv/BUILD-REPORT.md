# Local build report

## Status

This report records a reproducible local build; it is not a mathematical
correctness certificate.

## Build facts

- Build date: 2026-08-24.
- Command: `make clean pdf` in `paper/arxiv/`.
- PDF producer: `pdfTeX-1.40.26`.
- Output: 13 pages, 349826 bytes.
- SHA-256 of the checked PDF:

  ```text
  51ca4d4ca3fd56390451ecbcca78fdc85859ef1d4444457ef48f2e381de5a60f  main.pdf
  ```

- Citations and cross-references resolved after the BibTeX and repeated
  `pdflatex` passes.
- The final log contained no unresolved-reference, unresolved-citation,
  overfull-box, or underfull-box warning matched by the release scan.
- The PDF was rendered page by page and inspected for broken equations,
  clipped material, missing glyphs, and visibly blank or duplicated pages.

## Remote runner note

A GitHub Actions runner was attempted twice, but each attempt failed before any
job step ran and produced no readable job log. This cannot be interpreted as a
LaTeX failure or success. The non-starting workflow was removed from the pull
request. The authoritative reproducible build surface is the source plus
`Makefile`.

The generated PDF is supplied with the delivery bundle but is not tracked in the
Git repository. Independent reviewers should rebuild it themselves before
checking the paper.
