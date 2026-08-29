# PDF build report

This report records reproducible document builds. A successful PDF build is a
document-integrity check, not a mathematical correctness certificate.

## Public repository PDF

- Build date: 2026-08-29.
- Commands: `pdflatex`, `bibtex`, `pdflatex`, `pdflatex` as listed in README.
- PDF producer: MiKTeX `pdfTeX-1.40.29`.
- Output: 13 pages, 392918 bytes.
- SHA-256:

  ```text
  056fb5eb460368a7a5fcc75a2f5397ff9a8c5356233ff7cf453244a5431e0f65  main.pdf
  ```

- The final log contained no matched unresolved-reference,
  unresolved-citation, overfull-box, or underfull-box warning.
- This PDF is tracked so a visitor can read the paper directly from the
  repository. The LaTeX source remains authoritative.

## Earlier independent TeX Live build

- Build date: 2026-08-24.
- Command: `make clean pdf`.
- PDF producer: `pdfTeX-1.40.26`.
- Output: 13 pages, 349826 bytes.
- SHA-256:

  ```text
  51ca4d4ca3fd56390451ecbcca78fdc85859ef1d4444457ef48f2e381de5a60f  main.pdf
  ```

The byte-level difference between the two PDFs reflects the TeX environment;
the committed manuscript sources are unchanged. Independent reviewers should
rebuild the PDF before checking the natural-language proof and then compare the
paper with the Lean evidence map.
