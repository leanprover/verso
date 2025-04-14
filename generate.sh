#!/bin/bash

set -e

echo "Building the user's guide as TeX and HTML"
lake exe usersguide --with-html-multi --with-html-single --with-tex

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
