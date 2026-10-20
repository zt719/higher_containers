.PHONY: main

main:
	pdflatex main.tex
	bibtex main.aux
	pdflatex main.tex
	pdflatex main.tex

agda:
	agda --latex --latex-dir=. code.lagda
