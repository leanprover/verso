#!/usr/bin/env bash
set -euo pipefail

./generate.sh
cp _out/tex/main.pdf ./manual.pdf
cp -r _out/html-multi html-multi
cp README-html.md html-multi/README.md
zip -r html-manual.zip html-multi
