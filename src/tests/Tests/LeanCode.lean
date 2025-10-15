/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Rob Simmons
-/
import Verso.CodeTable
import VersoManual
namespace Verso.LeanCodeTest
set_option guard_msgs.diff true
set_option pp.rawOnError true

open Genre.Manual.InlineLean


/- ----- Helper JSON (to be factored out later) ----- -/

inductive PathItem where
| string : String → PathItem
| nat : Nat → PathItem

instance : OfNat PathItem n where
  ofNat := .nat n

instance : Coe Nat PathItem where
  coe := .nat

instance : Coe String PathItem where
  coe := .string

def getPath? (json : Lean.Json) : List PathItem → Except String Lean.Json
  | [] => .ok json
  | .string s :: rest =>
    match json.getObjVal? s with
    | .error m => .error m
    | .ok v => getPath? v rest
  | .nat n :: rest =>
    match json.getArrVal? n with
    | .error m => .error m
    | .ok v => getPath? v rest


/- ----- Inline lean ----- -/

#docs (Genre.Manual) inlineEx "Test" :=
:::::::
Inline lean can be a number like {lean}`4` or a string like {lean}`"hello"`
:::::::
/--
info: [{"para":
  [{"text": "Inline lean can be a number like "},
   {"other":
    {"content": [{"code": "4"}],
     "container":
     {"name": "Verso.Genre.Manual.InlineLean.Inline.lean",
      "id": null,
      "data":
      [{"token":
        {"tok": {"kind": {"withType": {"type": "Nat"}}, "content": "4"}}},
       []]}}},
   {"text": " or a string like "},
   {"other":
    {"content": [{"code": "\"hello\""}],
     "container":
     {"name": "Verso.Genre.Manual.InlineLean.Inline.lean",
      "id": null,
      "data":
      [{"token":
        {"tok":
         {"kind": {"str": {"string": "hello"}}, "content": "\"hello\""}}},
       []]}}}]}]
-/
#guard_msgs in
  #eval inlineEx.content.toJson


/- ----- -/

#docs (Genre.Manual) fenceEx "Test" :=
:::::::
```lean
def x := 4
```
:::::::
/--
info: ok: "def x := 4\n"
-/
#guard_msgs in
  #eval getPath? fenceEx.content.toJson
    [0, "concat", 0, "other", "content", 0, "code"]
/--
info: ok: ["Lean", "Parser", "Command", "definition"]
-/
#guard_msgs in
  #eval
    getPath? fenceEx.content.toJson
      [0, "concat", 0, "other", "container", "data", 0, "seq", "highlights", 0, "token", "tok", "kind", "keyword", "name"]


/- ----- -/

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


/- -----

#docs (Genre.Manual) footnotesAndLinkRefsAndCode "Test" :=
:::::::
There can be {lean}`x` and
[links][linkex] and
footnotes[^footnoteEx]
.

```lean
def z := "And blocks of code"
```

[linkex]: https://example.com
[^footnoteEx]: A footnote containing {lean}`y`
:::::::
-/
