#!/bin/bash

echo "Building the user's guide as TeX and HTML"
lake exe usersguide

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
