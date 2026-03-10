# Search bar for Verso manuals

To type check: `tsc -p ./jsconfig.json`.

## Libraries

I've added a few libraries to develop faster.

I picked up `fuzzysort` for fuzzy sorting from the github page
(https://github.com/farzher/fuzzysort) where he has a minified version next to
the implementation.

I picked up `unicode-input.min.js` from
https://cdn.skypack.dev/@leanprover/unicode-input - had to download it from the
network tab in the browser. It's a dependency of `unicode-input-component.js`.

I picked up `unicode-input-component.js` from
https://github.com/leanprover/vscode-lean4/blob/master/lean4-unicode-input-component/src/index.ts,
but that needs to changed some in order for it to work without compiling, so if
it needs to be updated look at the diff to understand what's required.

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
