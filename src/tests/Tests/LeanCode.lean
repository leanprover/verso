/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Rob Simmons
-/
import VersoManual
namespace Verso.LeanCodeTest
set_option guard_msgs.diff true
set_option pp.rawOnError true

open Genre.Manual.InlineLean


#docs (Genre.Manual) fenceEx "Test" :=
:::::::
```lean
def x := 4
```
:::::::

#docs (Genre.Manual) multipleCode "Test" :=
:::::::
Lean like {lean}`x` and {lean}`4 + x`

```lean
def y := "Block"
```

Lean also like {lean}`y.length + x`.

```lean
example := 34 * x
```
:::::::

/--
error: Unknown identifier `z`
---
error: Unknown identifier `z`
---
error: No error expected in code block, one occurred
-/
#guard_msgs in
#docs (Genre.Manual) fail "Test" :=
:::::::
{lean}`z`
:::::::

#docs (Genre.Manual) inspect "Test" :=
:::::::
{lean}`x + 3` is a Lean expression
:::::::

/--
info: (some (Verso.Genre.Manual.InlineLean.Inline.lean, [{"seq":
  {"highlights":
   [{"token":
     {"tok":
      {"kind":
       {"const":
        {"signature": "Verso.LeanCodeTest.x : Nat",
         "name": ["Verso", "LeanCodeTest", "x"],
         "isDef": false,
         "docs": null}},
       "content": "x"}}},
    {"text": {"str": " "}},
    {"token": {"tok": {"kind": "unknown", "content": "+"}}},
    {"text": {"str": " "}},
    {"token":
     {"tok": {"kind": {"withType": {"type": "Nat"}}, "content": "3"}}}]}},
 []]))-/
#guard_msgs in
#eval match inspect.force.content[0]! with
  | .para x => match x[0]! with
    | .other code _ => Option.some (code.name, code.data)
    | _ => .none
  | _ => .none
