#!/bin/bash

echo "Building the user's guide as TeX"
lake exe usersguide

echo "Building the user's guide as PDF"
pushd _out/tex
lualatex main
lualatex main
lualatex main
popd

echo "User's guide PDF is at:"
readlink -f _out/tex/main.pdf
