# Builds the IsaLibs technical guide (needs a TeX Live with latexmk).

DOC = IsaLibs_comandos

all: $(DOC).pdf

$(DOC).pdf: $(DOC).tex
	latexmk -pdf -interaction=nonstopmode -halt-on-error $(DOC).tex

clean:
	latexmk -c $(DOC).tex

.PHONY: all clean
