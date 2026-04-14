/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.DocString.Syntax
import VersoManual
import VersoBlog

open Verso Genre Manual

open InlineLean
open Verso.Doc

#doc (Manual) "Literate Programming" =>
%%%
tag := "literate"
htmlSplit := .never
%%%

Lean code, including Verso-format docstrings, can be rendered as a Web page without any further configuration.
Only two steps are necessary:
1. Add a dependency to Verso to your Lake configuration
2. Run `lake query :literateHtml`.
  Using `lake query` instead of `lake build` means that after the HTML is built, its path is printed to the console.

# HTML Output

By default, HTML is generated for all of the current package's default targets.
The resulting website includes a search box that can search both defined names and documentation and a navigation bar with a hierarchical overview of all included modules.
Both Markdown and Verso docstrings are rendered to HTML, though Verso docstrings have more features due the the greater available metadata.
The site has both light and dark mode themes.

# Configuration

The default site can be customized by placing a `literate.toml` file at the workspace root.
The following aspects can be customized:
 * The set of modules that are included
 * Each module's title
 * The order in which the modules are listed

# Configuration File Reference
%%%
tag := "literate-config-ref"
%%%

All configuration is optional.
An empty `literate.toml` file is equivalent to having no file at all.

## Targets
%%%
tag := "literate-targets"
%%%

By default, all libraries and executables that are default build targets are included.
To override this, specify explicit targets using `[[targets]]` entries.
When `targets` is specified, only the listed libraries and modules are included, replacing the default targets entirely.

Each `[[targets]]` entry has the following keys:

 * `library` — the name of a library; all modules belonging to it are included
 * `module` — the name of a single module

An entry may specify `library` alone, `module` alone, or both (in which case the module must belong to the named library).

```
# Include all modules in a library
[[targets]]
library = "MyLib"

# Include a specific module
[[targets]]
module = "MyLib.Special.Page"
```

## Exclusion
%%%
tag := "literate-exclude"
%%%

Modules can be excluded from the site.
Exclusion is recursive: the named module and all its children are removed.

```
exclude = ["MyLib.Internal", "MyLib.Deprecated"]
```

If both `targets` and `exclude` are specified, exclusion further narrows the target set.

## Ordering
%%%
tag := "literate-ordering"
%%%

By default, modules appear in the navigation bar in hierarchical alphabetical order.
The `order` key specifies an ordering for top-level siblings: listed modules appear first in the given order, and unlisted modules follow alphabetically.

```
order = ["MyLib.Introduction", "MyLib.Core"]
```

To order children within a namespace, use `[order_children]`:

```
[order_children]
"MyLib.Core" = ["MyLib.Core.Basic", "MyLib.Core.Syntax"]
```

This is safe by default: newly added modules appear automatically in the alphabetical tail without requiring configuration changes.

## Landing Page
%%%
tag := "literate-landing-page"
%%%

By default, the landing page is an auto-generated table of contents listing all included modules.
To replace it with the rendered content of a specific module:

```
landing_page = "MyLib.Introduction"
```

The module remains in its normal position in the navigation bar.

## Command Visibility
%%%
tag := "literate-hide-commands"
%%%

Commands are identified by their leading keywords.
Each pattern is matched against the first keyword tokens that appear in the command; for example, `"def"` matches `def` commands and `"#eval"` matches `#eval` commands.
Multi-word patterns like `"#print axioms"` match commands whose leading keywords start with that sequence.
By default, everything except the module header is shown (the module header is present but collapsed by default).

```
hide_commands = ["import", "open", "set_option"]
```

Because matching uses only the leading keywords, `#eval` and `#eval in` are both matched by the pattern `"#eval"`.

This can be scoped per module prefix via `[modules]` (see {ref "literate-per-module"}[Per-Module Configuration] below).

## Command Output
%%%
tag := "literate-show-output"
%%%

Some commands produce output (e.g., `#eval`, `#check`).
To make the output visible, the generated HTML will display this output immediately after the command that produced it.
A configurable list controls which commands have their output displayed in the rendered code box.
The default list includes `#eval`, `#check`, `#print`, and `#reduce`.

```
show_output = ["#eval", "#check", "#print", "#reduce"]
```

This can be scoped per module prefix via `[modules]`.

## Imports List
%%%
tag := "literate-imports"
%%%

Each page shows a collapsible list of imports, collapsed by default.
Imports whose modules are included in the site appear as links; the rest appear as plain text.
To disable the imports list:

```
show_imports = false
```

This can be scoped per module prefix via `[modules]`.

## Declaration Docstrings
%%%
tag := "literate-docstrings"
%%%

By default, declaration docstrings (`/-- ... -/`) are shown in code boxes alongside the definitions they document.
If the docstrings are part of the API of the program but are not intended to be shown to readers, then they can be removed.
This can be controlled globally and overridden per declaration:

```
# Hide all declaration docstrings
show_docstrings = false

# ...but still show these specific ones
show_docstrings_for = ["MyLib.Core.mainFunction"]
```

Alternatively, docstrings can be shown by default with specific exceptions hidden:

```
# Show all (this is the default)
show_docstrings = true

# ...but hide these
hide_docstrings_for = ["MyLib.Internal.helper"]
```

### Declaration Docstrings as Text

By default, declaration docstrings render inside code boxes, visually grouped with the code.
However, in some documents, the docstrings should be seen as part of the text.
Setting `docstrings_as_text` causes them to render as prose text between code boxes instead, which is useful when they contain substantial prose or theorem names.

```
docstrings_as_text = true
```

This can be scoped per module prefix via `[modules]`.

## Per-Module Configuration
%%%
tag := "literate-per-module"
%%%

Any top-level setting that controls content rendering can be scoped to a module prefix using `[modules]`.
The most specific matching prefix wins.
Unset keys inherit from the global defaults.

```
# Global defaults
hide_commands = ["import", "open", "set_option"]
show_docstrings = true

# Override for the tutorial subtree
[modules."MyLib.Tutorial"]
hide_commands = ["import"]
show_docstrings = false
show_docstrings_for = ["MyLib.Tutorial.mainExample"]

# Further override for a child module
[modules."MyLib.Tutorial.Namespaces"]
hide_commands = ["import", "set_option"]
```

Per-module entries can also set a page title and URL slug:

```
[modules."MyLib.Core.Basic"]
title = "Getting Started"
url = "getting-started"
```

The full set of keys available under `[modules."..."]`:

: `title`

  Page title and navbar label. The default value is the module's name.

: `url`

  URL path for this module's page. The default is derived from the module name (e.g., `MyLib.Data.Basic` is served at `MyLib/Data/Basic/`).
  When a `url` override is set on a parent module, child modules inherit it as a prefix.
  For example, if `MyLib.Data` has `url = "data-docs"`, then `MyLib.Data.Basic` is served at `data-docs/Basic/` rather than `MyLib/Data/Basic/`.
  To override a child independently, give it its own `[modules]` entry.

: `hide_commands`

  Commands to hide in the output.

: `show_output`

  Commands whose output is shown.

: `show_imports`

  Whether to show the collapsible imports list.

: `show_docstrings`

  Whether to show declaration docstrings

: `show_docstrings_for`

  Declarations whose docstrings should be shown regardless of the `show_docstrings` setting.

: `hide_docstrings_for`

  Declarations whose docstrings should be hidden regardless of the `show_docstrings` setting.

: `docstrings_as_text`

  Wender declaration docstrings as prose text. The default is `false`, causing them to be visually grouped with the code.

Module names are quoted as strings because TOML dot-separated keys would otherwise be ambiguous with config key names.

## Site Metadata
%%%
tag := "literate-metadata"
%%%

Defaults are discovered from the Lake configuration.
Override them in `literate.toml`:

```
[metadata]
title = "My Library"
description = "A Lean library for ..."
favicon = "images/favicon.png"
```

No favicon is included by default.
If `favicon` is set, the file is copied to the output directory and linked from every page.

## Theming
%%%
tag := "literate-theming"
%%%

CSS variables can be overridden under `[theme]`.
Keys are the variable names without the `--verso-` prefix, with hyphens replaced by underscores:

```
[theme]
text_font_family = "Georgia, serif"
code_font_family = "'Fira Code', monospace"
background_color = "#fefefe"
link_color = "#1a6b47"
```

Dark-mode overrides are specified under `[theme.dark]`:

```
[theme.dark]
background_color = "#1a1a2e"
link_color = "#5cb89a"
```

Any variable not overridden retains its default value.

## Extra CSS and JavaScript
%%%
tag := "literate-extra-assets"
%%%

Additional CSS or JavaScript files can be included.
Paths are relative to the project root.
CSS files are added as `<link>` tags and JS files as `<script>` tags in every page:

```
extra_css = ["custom/style.css", "custom/print.css"]
extra_js = ["custom/analytics.js"]
```

These files are copied into the output directory and linked after the default Verso styles, so custom CSS can override any built-in rules.

# Deployment
%%%
tag := "literate-deployment"
%%%

The site generated by `lake build :literateHtml` is a self-contained static site that can be deployed to any static hosting provider.
Running `lake query :literateHtml` builds the HTML and prints its path; this can be combined with a deployment script.
Verso includes tools to automate the setup of deployment to [GitHub Pages](https://docs.github.com/en/pages).

## GitHub Pages

To enable deployment to GitHub Pages, run:

```
lake exe verso setup-literate
```

This generates a GitHub Actions workflow file at `.github/workflows/verso-literate-pages.yml` that automatically builds and deploys the site on every push to `main`.

After generating the workflow:
1. Go to the repository's _Settings → Pages → Source_ and select _GitHub Actions_.
2. Commit and push the generated workflow file.

As usual, make sure that `lake-manifest.json` is committed to the repository.

The first build may be slow because it compiles the full Lean project.
Subsequent builds are faster thanks to `.lake` caching.

When Verso is upgraded, `lake build :literateHtml` will warn if the workflow file is outdated.
Re-running `lake exe verso setup-literate` updates it, saving the previous version as a `.bak` file so that any manual customizations can be merged by hand.
