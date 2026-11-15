/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

set_option linter.missingDocs true
set_option doc.verso true

namespace Verso.Markdown

/--
A mapping from Markdown header levels to nesting depths.

The values in the list are Markdown header levels. Their position in the list is the nesting depth,
with the final element being depth 0. For example, the list {lean}`[5, 4, 2, 1]` associates:
- Markdown level 1 to depth 0
- Markdown level 2 to depth 1
- Markdown level 4 to depth 2
- Markdown level 5 to depth 3

Markdown documents often skip header levels or start below level 1. Assigning depths by position
gives each header the depth that matches its place among the headers that enclose it.
-/
public abbrev HeaderMapping := List Nat

/--
Records a header with Markdown level {name}`level` and returns its nesting depth.

The headers whose levels are greater than or equal to {name}`level` are closed. The returned mapping
contains {name}`level` as the innermost open header.
-/
public def HeaderMapping.addHeader (hdrs : HeaderMapping) (level : Nat) : Nat × HeaderMapping :=
  match hdrs with
  | [] => (0, [level])
  | docLevel :: more =>
    if level < docLevel then addHeader more level
    else if level = docLevel then (more.length, hdrs)
    else (hdrs.length, level :: hdrs)
