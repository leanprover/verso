# Literate Config Test Project

This is a test project for Verso's simple literate programming system.
It is a small, self-contained Lean project that exercises
the literate features: module docstrings rendered as prose, syntax
highlighting, cross-references, and image copying.

## How the Test Suite Uses This Project

Running `lake test` from the Verso repository root invokes three test
suites against this project:

1. **Literate config tests** validate the planning stage, which
   determines which modules to include in the generated site.
2. **Literate HTML tests** build each module's JSON and then check the
   generated HTML for correct structure, content, and links.
3. **Literate browser tests** generate a complete HTML site into a
   temporary directory and run Playwright assertions against it.

All three suites build their output into temporary directories that
are cleaned up automatically. No persistent output is produced by
`lake test`.

## Running the Site by Hand

To generate the literate site and inspect the output yourself, run the
following from this directory:

```
lake build :literateHtml
```

This runs the full pipeline (JSON extraction, planning, and HTML
generation) and writes the resulting site to
`.lake/build/literate-html/`.
