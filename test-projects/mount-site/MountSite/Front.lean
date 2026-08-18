/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoBlog
open Verso Genre Blog
open scoped Lean.Doc.Syntax

#doc (Page) "A Site That Mounts Rendered HTML Content" =>

This site renders directories of rendered HTML content with its own theme.
The same directory is mounted twice, under different names, so every internal page path occurs once
per mount and the page IDs are namespaced by the mount.

* {page_link fixture}[The fixture, mounted at the top level]
* {page_link fixture.guide}[The fixture's guide]
* {page_link fixture.guide.first}[The fixture's first step]
* {page_link fixture.guide.«step-1»}[A fixture page whose path segment needs guillemets]
* {page_link «fixture-again»}[The same fixture, mounted below the top level]
* {page_link «fixture-again».guide.«step-1»}[The same page under the other mount]

The site's own code and math render alongside the mounted content:
$`\sum_{i=0}^{n} i^2`

```leanInit siteCode
-- This block initializes a Lean context
```

```lean siteCode
def siteExample : Nat := 42
```
