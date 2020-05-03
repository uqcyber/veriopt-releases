.PHONY: all theory document

TEX=pdflatex
DOCUMENT=main.tex
JUNK=comment.cut main.aux main.bbl main.blg main.log main.pdf main.toc

all:
	make theory
	# make document

clean:
	rm $(JUNK) || true
	rm *~ || true
	rm -r generated/

theory:
	isabelle build -d . rewrite

document: $(THESIS_DIR)
	$(TEX) $(DOCUMENT)
	bibtex main
	$(TEX) $(DOCUMENT)
	$(TEX) $(DOCUMENT)

upload:
	scp -r ~/.isabelle/Isabelle2018/browser_info/Graal/* uqcloud:/var/www/htdocs/thesis
