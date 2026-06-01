#!/bin/bash

set -e

html_only=false
for arg in "$@"; do
  case "$arg" in
    --html)
      html_only=true
      ;;
    *)
      echo "Unknown argument: $arg" >&2
      echo "Usage: $0 [--html]" >&2
      exit 2
      ;;
  esac
done

if [ "$html_only" = false ] && ! command -v inkscape >/dev/null 2>&1; then
  if [ -f "/Applications/Inkscape.app/Contents/MacOS/inkscape" ]; then
    PATH="$PATH:/Applications/Inkscape.app/Contents/MacOS"
  else
    echo "Error: Could not find 'inkscape' in \$PATH or in the macOS Applications directory" >&2
    exit 1
  fi
fi

if [ "$html_only" = true ]; then
  echo "Building the user's guide as HTML"
  lake exe usersguide
else
  echo "Building the user's guide as TeX and HTML"
  lake exe usersguide --delay-html-multi multi.json --delay-html-single single.json --with-tex
  lake exe usersguide --resume-html-multi multi.json --resume-html-single single.json

  echo "Building the user's guide as PDF"
  mkdir -p _out/tex
  pushd _out/tex
  lualatex -shell-escape main
  lualatex -shell-escape main
  lualatex -shell-escape main
  popd

  echo "User's guide PDF is at:"
  readlink -f _out/tex/main.pdf
fi

echo "HTML is at:"
readlink -f _out/html-single/index.html
readlink -f _out/html-multi/index.html
