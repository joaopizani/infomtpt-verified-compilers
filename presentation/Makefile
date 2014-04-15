.PHONY: clean view

view: main.pdf
	xdg-open main.pdf 2> /dev/null 1> /dev/null

main.pdf: section1.tex section2.tex section3.tex
	latexmk -pdf -f main.tex

clean:
	latexmk -c main.tex
	rm -f *.nav *.snm *.vrb *.pyg *.out.pyg *.ptb

veryclean: clean
	rm -f main.pdf
	rm -f agda/tex/*.tex
	rm -f agda/*.agdai
