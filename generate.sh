#!/bin/bash

set -e

echo "Building the user's guide as TeX and HTML"
lake exe usersguide --delay-html-multi multi.json --delay-html-single single.json --with-tex
lake exe usersguide --resume-html-multi multi.json --resume-html-single single.json

echo "Building the user's guide as PDF"
mkdir -p _out/tex
pushd _out/tex
lualatex main
lualatex main
lualatex main
popd

echo "User's guide PDF is at:"
readlink -f _out/tex/main.pdf

echo "HTML is at:"
readlink -f _out/html-single/index.html
readlink -f _out/html-multi/index.html
