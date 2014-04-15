.PHONY: clean view agda

view: main.pdf
	xdg-open main.pdf 2> /dev/null 1> /dev/null

main.pdf: section1.tex section2.tex section3.tex agda
	latexmk -quiet -pdf -f main.tex

agda:
	cd agda; for f in *.lagda; do agda -i "${HOME}/build/agda/lib/current/src" -i "." --latex --latex-dir="tex" "$${f}"; done

clean:
	latexmk -c main.tex
	rm -f *.nav *.snm *.vrb *.pyg *.out.pyg *.ptb

veryclean: clean
	rm -f main.pdf
	rm -f agda/tex/*.tex
	rm -f agda/*.agdai
