# Errata Widget Test Project

This project holds the tests that the browser tests of Errata's
run-test widget run from the widget. The browser tests live in
`browser-tests/errata-widget`. They start a Lean language server in
this directory, show the real InfoView in a browser connected to that
server, and use the widget on the tests in `WidgetFixtures` as a
person would.

Some of these tests fail on purpose, and
`WidgetFixtures/BuildError.lean` fails to build, so this project is a
Lake workspace of its own. Its `errata.toml` gives the setting
`greeting` a value in the default profile, which the widget's settings
fields start from.

Each browser test writes a scratch module of its own,
`WidgetFixtures/Scratch_KEY.lean`, and deletes it afterwards. The
tests open copies of the fixture modules in lanes,
`WidgetFixtures/LaneN/`. Each lane serves one test at a time, so
tests that run at once share one Lean server and each has documents
of its own. The suite removes the lanes when it ends.

## Running the Browser Tests

The browser tests load the InfoView from npm. They are marked with the
pytest marker `errata_widget`, and pytest runs them only when
`-m errata_widget` selects them. CI runs them in a step of their own.
To run them locally, build Verso, install the InfoView with `npm ci`
in the repository root, then run:

```
uv run --project browser-tests --extra test pytest browser-tests/errata-widget -m errata_widget -v
```
