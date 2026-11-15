/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Rob Simmons
-/
import Errata
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
-/
#test_msgs in
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
        {"signatureFormat": null,
         "signature": "Verso.LeanCodeTest.x : Nat",
         "name": ["Verso", "LeanCodeTest", "x"],
         "isDef": false,
         "docs": null}},
       "content": "x"}}},
    {"text": {"str": " "}},
    {"token":
     {"tok":
      {"kind":
       {"operator":
        {"occurrence": "«term_+_»-749",
         "name": ["term_+_"],
         "docs":
         "`a + b` computes the sum of `a` and `b`.\nThe meaning of this notation is type-dependent.\n\nConventions for notations in identifiers:\n\n * The recommended spelling of `+` in identifiers is `add`."}},
       "content": "+"}}},
    {"text": {"str": " "}},
    {"token":
     {"tok":
      {"kind": {"num": {"typeFormat": null, "type": "Nat"}},
       "content": "3"}}}]}},
 []]))
-/
#test_msgs in
#eval match inspect.toPart.content[0]! with
  | .para x => match x[0]! with
    | .other code _ => Option.some (code.name, code.data)
    | _ => .none
  | _ => .none

-- Ensure no spurious unused variable warning for `α`
#docs (Genre.Manual) mutualInductiveTest "Mutual Inductive Test" :=
:::::::
```lean
mutual
  inductive TreeA (α : Type) where
    | leafA : TreeA α
    | nodeA : α → TreeB α → TreeA α

  inductive TreeB (α : Type) where
    | leafB : TreeB α
    | nodeB : α → TreeA α → TreeB α
end
```
:::::::

-- Ensure no spurious unused variable warning for named binders in {lean}`...` inline terms.
-- In term like `(x : Nat) → String`, `x` is a named binder that doesn't appear in the body,
-- but the metalanguage's unused variable linter should not re-fire on the info tree pushed
-- by leanInline.
#test_msgs in
#docs (Genre.Manual) inlineNamedBinderType "Inline Named Binder Type" :=
:::::::
{lean}`(x : Nat) → String`
:::::::


-- Genuinely unused variable in a code block: the inner linter produces a warning that
-- appears in the generated highlighted output (via `nonSilentMsgs` in `elabCommands`).
-- `reportMessages` silences non-error messages, so no build warning is emitted.
#docs (Genre.Manual) unusedVarTest "Unused Var Test" :=
:::::::
```lean (name := unusedVar)
def unusedArgFn (unused : Nat) : Nat := 0
```
```leanOutput unusedVar
Variable name `unused` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _unused

Note: This linter can be disabled with `set_option linter.unusedVariables false`
```
:::::::

/--
error: Didn't match - got: 
  [a
   b
   c]
but expected:
  b
  

Hint: Replace with the actual message:
  information: a̲
  ̲b
  c̲
  ̲
-/
#test_msgs in
#docs (Genre.Manual) allowDiff30 "Not enough allowDiff" :=
:::::::
```lean (name := foo)
#print "a\nb\nc"
```
```leanOutput foo
b
```
:::::::

/--
error: Didn't match even with allowDiff := 1 - got: 
  [a
   b
   c]
but expected:
  b
  

Hint: Replace with the actual message:
  information: a̲
  ̲b
  c̲
  ̲
-/
#test_msgs in
#docs (Genre.Manual) allowDiff31 "Not enough allowDiff" :=
:::::::
```lean (name := foo)
#print "a\nb\nc"
```
```leanOutput foo (allowDiff := 1)
b
```
:::::::

#test_msgs in
#docs (Genre.Manual) allowDiff32 "Enough allowDiff" :=
:::::::
```lean (name := foo)
#print "a\nb\nc"
```
```leanOutput foo (allowDiff := 2)
b
```
:::::::

-- The `inst` role accepts a class that has an instance.
#test_msgs in
#docs (Genre.Manual) instFound "Test" :=
:::::::
There is an instance of {inst}`ToString Nat`.
:::::::

-- The `inst` role reports the error in a term that fails to elaborate.
/--
error: Unknown identifier `NoSuchClass`
-/
#test_msgs in
#docs (Genre.Manual) instUnknownName "Test" :=
:::::::
There is no class named {inst}`NoSuchClass Nat`.
:::::::

-- The `inst` role reports a class that has no instance.
/--
error: failed to synthesize
  ToString (Nat → Nat)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#test_msgs in
#docs (Genre.Manual) instNotFound "Test" :=
:::::::
There is no instance of {inst}`ToString (Nat → Nat)`.
:::::::

-- `leanTerm` blocks report each error once, like a `lean` block.
/--
error: Unknown identifier `z`
-/
#test_msgs in
#docs (Genre.Manual) leanTermFail "Test" :=
:::::::
```leanTerm
z + 1
```
:::::::

-- With `+error`, a `leanTerm` block accepts an error and records it under the provided name.
#test_msgs in
#docs (Genre.Manual) leanTermExpectedError "Test" :=
:::::::
```leanTerm +error (name := noZ)
z + 1
```
```leanOutput noZ
Unknown identifier `z`
```
:::::::

-- With `+error`, a `leanTerm` block without an error is reported.
/--
error: Error expected in code block, but none occurred
-/
#test_msgs in
#docs (Genre.Manual) leanTermNoExpectedError "Test" :=
:::::::
```leanTerm +error
1 + 1
```
:::::::

-- A `leanTerm` block elaborates its term with the names in `universes`.
#test_msgs in
#docs (Genre.Manual) leanTermUniverses "Test" :=
:::::::
```leanTerm (universes := "u")
Type u
```
:::::::

-- With `+error`, the `inst` role accepts both kinds of failure.
#test_msgs in
#docs (Genre.Manual) instExpectedError "Test" :=
:::::::
There is no instance of {inst +error}`ToString (Nat → Nat)`, and no class named
{inst +error}`NoSuchClass Nat`.
:::::::
