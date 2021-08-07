#!/usr/bin/env bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
cd "$DIR"
node extract.js LaTeX.Entrypoint.fst > ../main.tex
cd ..
latexrun --latex-args="-shell-escape -synctex=1" main.tex
cp "$DIR/../latex.out/main.synctex.gz" "$DIR/../main.synctex.gz"

