# Search bar for Verso manuals

To type check: `tsc -p ./jsconfig.json`.

## Libraries

I've added a few libraries to develop faster.

I picked up `fuzzysort` for fuzzy sorting from the github page
(https://github.com/farzher/fuzzysort) where he has a minified version next to
the implementation.

I picked up `unicode-input.min.js` from the esm.sh CDN, which serves npm
packages as browser-compatible ESM bundles. It's a dependency of
`unicode-input-component.min.js`. See "Updating the unicode input libraries"
below for how to refresh both files.

I picked up `unicode-input-component.min.js` by compiling the TypeScript source
from
https://github.com/leanprover/vscode-lean4/blob/master/lean4-unicode-input-component/src/index.ts
with esbuild, after replacing its `@leanprover/unicode-input` import with
`./unicode-input.min.js` so the browser can resolve it locally.

# Research

The Lean search bar has some properties that make it hard to use already
existing libraries for search bars directly. Almost all online search bars
require multiple libraries - I haven't been able to find one that didn't. And we
don't want dependents on this component to have to install node/npm/tons of
libraries in order to use it. It should be simple.

Additionally, the data is in a complex format, and has to be able to run
locally, so doing serverside search is off the table.

## Fuzzy search js library investigation

Looking at fuzzy search libraries. The important things are:

- Size - it should be small.
- Correctness - it should work.
- Single word/multiword?
- Offload to web worker?

#### https://www.npmjs.com/package/fuzzysort

Looks slick. Same kind of search as in Sublime Text. Probably makes more sense
for programming things than the other things here.

## Combobox libraries

Maybe have a look at
https://www.digitala11y.com/accessible-ui-component-libraries-roundup/

https://webaim.org/ is a good place to look

### https://www.w3.org/WAI/ARIA/apg/patterns/combobox/examples/combobox-autocomplete-both/

I've found this w3 aria example, which I'm going to use and adjust to our needs.
That's a good place to start.

# Updating the Unicode Input Libraries

The search bar vendors two libraries for Unicode abbreviation input:
`unicode-input.min.js` and `unicode-input-component.min.js`. When a new version
of `@leanprover/unicode-input` is published to `npm`, or when the component source
in the `vscode-lean4` repository is updated, both files should be refreshed
together.

## Updating `unicode-input.min.js`

The file `unicode-input.min.js` is the `@leanprover/unicode-input` NPM package
bundled as a self-contained ESM file by the esm.sh CDN. To update it, fetch the
new version's bundle (replacing `0.1.9` with the desired version), strip the
trailing source-map comment (which would cause browser console errors because
the map file is not vendored), and save the result over the existing file:

```
$ curl -sS https://esm.sh/@leanprover/unicode-input@0.1.9/es2022/unicode-input.mjs \
  | sed '/^\/\/# sourceMappingURL=/d' \
  > static-web/search/unicode-input.min.js
```

## Updating `unicode-input-component.min.js`

The component is compiled from
https://github.com/leanprover/vscode-lean4/blob/master/lean4-unicode-input-component/src/index.ts.
That file imports from `@leanprover/unicode-input` by package name, which the
browser cannot resolve, so the import must be rewritten to point at the local
file before compiling. The steps are as follows.

First, fetch the TypeScript source and rewrite the import:

```
curl -sS https://raw.githubusercontent.com/leanprover/vscode-lean4/master/lean4-unicode-input-component/src/index.ts \
  | sed "s|from '@leanprover/unicode-input'|from './unicode-input.min.js'|g" \
  > /tmp/index.ts
```

Then compile with `esbuild`, marking the local dependency as external so that it
is kept as a bare import in the output rather than inlined:

```
$ npm install --save-dev esbuild @leanprover/unicode-input@0.1.9
$ npx esbuild /tmp/index.ts \
  --bundle --format=esm --minify \
  --external:'./unicode-input.min.js' \
  --outfile=static-web/search/unicode-input-component.min.js
```
The `@leanprover/unicode-input` package must be installed locally so that
`esbuild` can resolve the TypeScript types it imports, even though the package
itself is not bundled into the output.

After updating either file, rebuild the site and run the browser tests to confirm
that Unicode abbreviation input still works:

```
lake exe usersguide --delay-html-multi multi.json --delay-html-single single.json
lake exe usersguide --resume-html-multi multi.json --resume-html-single single.json
uv run --project browser-tests --extra test pytest browser-tests/test_search.py -v
```
