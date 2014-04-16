#!/usr/bin/env bash

latexmk -c -pdf main.tex

rm *.aux *.fdb_latexmk *.fls *.log *.nav *.out *.pyg *.snm *.toc *.vrb
rm agda/*.agdai
rm agda/tex/*.tex

rm main.pdf

