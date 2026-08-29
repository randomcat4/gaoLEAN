PDFLATEX ?= pdflatex
BIBTEX := $(shell command -v bibtex 2>/dev/null || command -v bibtex.original 2>/dev/null)

.PHONY: pdf clean

pdf:
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error main.tex
	$(BIBTEX) main
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error main.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error main.tex

clean:
	rm -f main.aux main.bbl main.blg main.fdb_latexmk main.fls main.log main.out main.pdf
