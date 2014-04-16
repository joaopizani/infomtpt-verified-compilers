#!/usr/bin/env bash

AGDA_STD_LIB_DEFAULT="${HOME}/build/agda/lib/current/src"
AGDA_STD_LIB="${1:-"${AGDA_STD_LIB_DEFAULT}"}"

cd agda
agda -i "${AGDA_STD_LIB}" -i "." --latex --latex-dir="tex" Report.lagda
cd ..

latexmk -pdf -f main.tex

