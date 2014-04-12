view: main.pdf
	xdg-open main.pdf 2> /dev/null 1> /dev/null

main.pdf: section1.tex section2.tex section3.tex
	latexmk -quiet -pdf -f main.tex

section%.tex: section%.md ; pandoc $< -t beamer -o $@

clean:
	latexmk -c main.tex
	rm -f *.nav *.snm *.vrb *.pyg *.out.pyg

veryclean: clean
	rm -f main.pdf
	rm -f section*.tex
