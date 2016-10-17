all:	run_test

F = test

run_test: $(F).lmlw
	./why3literate.opt $(F).lmlw
	rubber -d $(F).tex
	why3 prove --type-only $(F).mlw
	okular $(F).pdf &

clean:
	rm -f test.mlw test.tex test.log test.pdf test.aux test.log *~
	rm -rf test
