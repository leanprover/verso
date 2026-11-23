#!/usr/bin/env bash

# Build the user's guide.
#
#   generate.sh       build the HTML and the PDF
#   generate.sh html  build the HTML and the TeX source of the PDF
#   generate.sh pdf   build the PDF from the TeX source that `generate.sh html` wrote

set -e

find_inkscape() {
  if ! command -v inkscape >/dev/null 2>&1; then
    if [ -f "/Applications/Inkscape.app/Contents/MacOS/inkscape" ]; then
      PATH="$PATH:/Applications/Inkscape.app/Contents/MacOS"
    else
      echo "Error: Could not find 'inkscape' in \$PATH or in the macOS Applications directory" >&2
      exit 1
    fi
  fi
}

build_html() {
  echo "Building the user's guide as TeX and HTML"
  lake run versoMain UsersGuideMain.lean --delay-html-multi multi.json --delay-html-single single.json --with-tex
  lake run versoMain UsersGuideMain.lean --resume-html-multi multi.json --resume-html-single single.json

  echo "HTML is at:"
  readlink -f _out/html-single/index.html
  readlink -f _out/html-multi/index.html
}

build_pdf() {
  echo "Building the user's guide as PDF"
  mkdir -p _out/tex
  pushd _out/tex
  lualatex -shell-escape main
  lualatex -shell-escape main
  lualatex -shell-escape main
  popd

  echo "User's guide PDF is at:"
  readlink -f _out/tex/main.pdf
}

case "${1:-all}" in
  all)
    find_inkscape
    build_html
    build_pdf
    ;;
  html)
    build_html
    ;;
  pdf)
    find_inkscape
    build_pdf
    ;;
  *)
    echo "usage: $0 [html | pdf]" >&2
    exit 1
    ;;
esac
