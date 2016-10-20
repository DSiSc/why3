all:	run_test

F = test

run_test: $(F).lmlw
	./why3literate.opt $(F).lmlw
	rubber -d $(F).tex
	why3 prove --type-only $(F).mlw
	okular $(F).pdf &

clean::
	rm -f $(F).mlw $(F).tex $(F).log $(F).pdf $(F).aux $(F).log *~
	rm -rf $(F)
	rm -f why3lang.sty

FF = main

run_main: $(FF).lmlw
	./why3literate.opt $(FF).lmlw
	#rubber -d $(FF).tex
	pdflatex $(FF).tex
	bibtex $(FF)
	pdflatex $(FF).tex
	pdflatex $(FF).tex
	why3 prove --type-only $(FF).mlw
	okular $(FF).pdf &

clean::
	rm -f $(FF).mlw $(FF).tex $(FF).log $(FF).pdf $(FF).aux $(FF).log \
	  *~ $(FF).bbl $(FF).blg $(FF).out
	rm -rf $(FF)
	rm -f why3lang.sty
