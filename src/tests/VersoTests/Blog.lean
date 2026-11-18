/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
Property tests for blog identifier generation. This is a non-`module` file because `VersoBlog`
itself is not part of the module system; the Errata runner imports it through its non-module main.
-/
import VersoBlog
import VersoBlog.LiterateLeanPage
import VersoTests.Arbitrary
import Errata

open Lean
open Verso Genre Blog
open Verso.Multi
open Verso.NameMap
open Plausible Gen Arbitrary
open Errata

def freshIdOk (hint : LetterString) (path : Path) (howMany : Nat) : Bool := Id.run do
  let mut st : TraverseState := { remoteContent := {} }
  let mut ids := #[]
  for _ in 0...howMany do
    let i := st.freshId path hint.sluggify
    st := { st with usedIds := st.usedIds.alter path (fun used? => used?.getD {} |>.insert i) }
    ids := ids.push i
  ids.size == howMany && ids.all (ids.count · == 1)

def freshIdFirstIsHint (hint : LetterString) (path : Path) : Bool := Id.run do
  let st : TraverseState := { remoteContent := {} }
  let i := st.freshId path hint.sluggify
  hint.isEmpty || i == hint.sluggify

def freshIdSecondIsHintWith1 (hint : LetterString) (path : Path) : Bool := Id.run do
  let mut st : TraverseState := { remoteContent := {} }
  let i := st.freshId path hint.sluggify
  st := { st with usedIds := st.usedIds.alter path (fun used? => used?.getD {} |>.insert i) }
  let i' := st.freshId path hint.sluggify
  i != i' && (hint.isEmpty || (i == hint.sluggify && i' == (s!"{hint}1").sluggify))

/-- Identifiers freshly generated within a path are unique. -/
@[test]
def freshIdsAreUnique : Test := property (∀ h p n, freshIdOk h p n)

/-- The first identifier generated for a hint is the hint itself. -/
@[test]
def freshIdFirst : Test := property (∀ h p, freshIdFirstIsHint h p)

/-- The second identifier generated for a hint is the hint with `1` appended. -/
@[test]
def freshIdSecond : Test := property (∀ h p, freshIdSecondIsHintWith1 h p)

/-! ## Compile-time regression tests for the blog genre -/

/-- info: #[(`a.b.c, 1), (`a.c, 4), (`b.c, 6), (`c, 3)] -/
#test_msgs in
#eval NameSuffixMap.empty |>.insert `a.b.c 1 |>.insert `b.c 2 |>.insert `c 3 |>.insert `a.c 4 |>.insert `a.b 5 |>.insert `b.c 6 |>.get `c

-- The deprecated inline Lean role warns. This standalone document asserts the warning, ahead of the
-- streaming blog blocks below that a `#test_msgs` wrapper cannot enclose.
/--
warning: `{leanInline}` is deprecated; use `{lean}` instead.
-/
#test_msgs in
#docs (Post) inlineLeanRoleNamesDeprecated "Inline Lean Role Names (deprecated alias)" :=
:::::::
```leanInit post2
```

Legacy role: {leanInline post2}`Nat.succ 1`.
:::::::

-- Hidden blog Lean blocks elaborate with their show/keep/error flags.
#docs (Post) hiddenLeanBlockFlags "Hidden Lean Block Flags" :=
:::::::
```leanInit post
```

```lean post -show
def base : Nat := 40
```

```lean post -keep
def scratch : Nat := base + 2
```

```lean post
example : base = 40 := rfl
```

```lean post +error
#check scratch
```
:::::::

#test_guard hiddenLeanBlockFlags.toPart.content.size > 0

-- The canonical inline Lean role works without warnings.
#docs (Post) inlineLeanRoleNames "Inline Lean Role Names" :=
:::::::
```leanInit post
```

Canonical role: {lean post}`Nat.succ 1`.
:::::::

#test_guard inlineLeanRoleNames.toPart.content.size > 0
#test_guard inlineLeanRoleNamesDeprecated.toPart.content.size > 0

-- The inline Lean role elaborates terms in the saved example environment.
#docs (Post) roleSeesEnvironment "Role Sees Environment" :=
:::::::
```leanInit env
```

```lean env
def x := 1
```

Role is aware of the environment: {lean env}`x`
:::::::

#test_guard roleSeesEnvironment.toPart.content.size > 0

-- Comment-only initialization and independent code regions retain command state, while a parse
-- error in one region must not put the next region's fresh parser into recovery mode.
#docs (Post) independentParserRegions "Independent parser regions" :=
:::::::
```leanInit parserRegions
-- no imports or prelude
```

Unicode before the code: λ 🐈.

```lean parserRegions +error
def broken := (
```

```lean parserRegions
def café : Nat := 41
```

The saved environment is shared with inline code: {lean parserRegions}`café + 1`.

```lean parserRegions
example : café = 41 := rfl
```
:::::::

#test_guard independentParserRegions.toPart.content.size > 0

-- Forward to the ordinary blog expanders with code that has no original source span.
@[code_block]
meta def generatedLeanInit : Doc.Elab.CodeBlockExpanderOf LeanInitBlockConfig :=
  fun config _ => Blog.leanInit config (Lean.Doc.mkVersoCodeBlockFrom .missing "")

@[role]
meta def generatedLean : Doc.Elab.RoleExpanderOf LeanInlineConfig := fun config args => do
  let #[code] := args | throwError "Expected one inline code element"
  let contents := Lean.Doc.mkVersoCodeFrom .missing "Nat.succ 1"
  Blog.leanCanonical config #[⟨code.raw.setArg 1 contents.raw⟩]

#docs (Post) generatedLeanRegions "Generated Lean regions" :=
:::::::
```generatedLeanInit generated
```

The generated header initializes a context: {lean generated}`Nat.succ 1`.

```leanInit source
```

The role supplies a generated term: {generatedLean source}`unused`.
:::::::

#test_guard generatedLeanRegions.toPart.content.size > 0

-- Make a term parser observe an option that is set in the surrounding document.
private def defaultParserOptionsGuard : Parser.Parser := {
  fn := fun c s =>
    if c.options.getBool `pp.universes false then s.mkError "Expected default parser options"
    else s
}

@[combinator_formatter defaultParserOptionsGuard]
private meta def defaultParserOptionsFormatter : PrettyPrinter.Formatter := pure ()

@[combinator_parenthesizer defaultParserOptionsGuard]
private meta def defaultParserOptionsParenthesizer : PrettyPrinter.Parenthesizer := pure ()

syntax (name := defaultParserOptionTerm) "defaultParserOptionTerm%" defaultParserOptionsGuard : term

@[term_elab defaultParserOptionTerm]
private meta def elabDefaultParserOptionTerm : Elab.Term.TermElab := fun _ _ => pure (mkNatLit 0)

set_option pp.universes true

#docs (Post) defaultInlineParserOptions "Default inline parser options" :=
:::::::
```leanInit example
```

The inline parser uses default options: {lean example}`defaultParserOptionTerm%`.
:::::::

set_option pp.universes false

#test_guard defaultInlineParserOptions.toPart.content.size > 0
