/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/
import Errata
import Verso

namespace Verso.ExtensionResolutionTest
set_option guard_msgs.diff true

open Lean
open Verso.Doc.Elab

/-
Extension resolution has four relevant outcomes:
1. a declaration is registered for the requested extension syntax - good.
2. a declaration can be used as an expander, but is not registered - bad.
3. a declaration exists, but is not registered for the requested extension syntax - bad.
4. a declaration does not exist - unresolved extension name.
-/

namespace RoleCases

@[role]
def registered : RoleExpanderOf Unit
  | (), _ => do
    `(Verso.Doc.Inline.text "registered-role")

#docs (.none) roleRegistered "Registered role" :=
:::::::
{registered}[]
:::::::

/-- info: #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "registered-role"]] -/
#test_msgs in
#eval roleRegistered.toPart.content

@[role_expander legacyRegistered]
def legacyRegistered : RoleExpander
  | _, _ => do
    pure #[← `(Verso.Doc.Inline.text "legacy-role")]

#docs (.none) roleLegacyRegistered "Legacy registered role" :=
:::::::
{legacyRegistered}[]
:::::::

/-- info: #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "legacy-role"]] -/
#test_msgs in
#eval roleLegacyRegistered.toPart.content

def unregistered : RoleExpander
  | _, _ => do
    pure #[← `(Verso.Doc.Inline.text "unregistered-role")]

/--
error: Declaration `unregistered` can be used as a role expander but is not registered as a role. Register it with `@[role]`.
-/
#test_msgs in
#docs (.none) roleUnregistered "Unregistered role" :=
:::::::
{unregistered}[]
:::::::

def wrongType : Nat := 7

/--
error: Declaration `wrongType` was found but is not registered as a role.
-/
#test_msgs in
#docs (.none) roleWrongType "Wrong role type" :=
:::::::
{wrongType}[]
:::::::

/--
error: No registered role `registred`.

Hint: Did you mean role `registered`?
  registe̲red
-/
#test_msgs in
#docs (.none) roleTypo "Role typo" :=
:::::::
{registred}[]
:::::::

/--
error: No registered role `legacyRegistred`.

Hint: Did you mean role `legacyRegistered`?
  legacyRegiste̲red
-/
#test_msgs in
#docs (.none) roleLegacyTypo "Legacy role typo" :=
:::::::
{legacyRegistred}[]
:::::::

/--
error: No registered role `nothereatallzzzz`.
-/
#test_msgs in
#docs (.none) roleNoCloseMatch "No close role match" :=
:::::::
{nothereatallzzzz}[]
:::::::

end RoleCases

namespace DistanceCases

/-
The suggestion cutoff table is:
* input length less than 3: Levenshtein distance at most 1
* input length less than 6: Levenshtein distance at most 2
* otherwise: Levenshtein distance at most 3

The length-1 no-match case appears before this namespace declares a local single-character role,
because any single-character role is within distance 1 of any single-character typo.
-/

/--
error: No registered role `q`.
-/
#test_msgs in
#docs (.none) oneCharDistanceNoMatch "One-character distance no match" :=
:::::::
{q}[]
:::::::

@[role]
def r : RoleExpanderOf Unit
  | (), _ => do
    `(Verso.Doc.Inline.text "one-character-cutoff-role")

@[role]
def ab : RoleExpanderOf Unit
  | (), _ => do
    `(Verso.Doc.Inline.text "short-distance-role")

@[role]
def vvv : RoleExpanderOf Unit
  | (), _ => do
    `(Verso.Doc.Inline.text "three-character-cutoff-role")

@[role]
def distanceRegistered : RoleExpanderOf Unit
  | (), _ => do
    `(Verso.Doc.Inline.text "distance-role")

@[role]
def yyyyy : RoleExpanderOf Unit
  | (), _ => do
    `(Verso.Doc.Inline.text "middle-cutoff-role")

@[role]
def zzzzzz : RoleExpanderOf Unit
  | (), _ => do
    `(Verso.Doc.Inline.text "long-cutoff-role")

@[role]
def multiAlpha : RoleExpanderOf Unit
  | (), _ => do
    `(Verso.Doc.Inline.text "multi-alpha-role")

@[role]
def multiAlphi : RoleExpanderOf Unit
  | (), _ => do
    `(Verso.Doc.Inline.text "multi-alphi-role")

/--
error: No registered role `q`.

Hint: Did you mean role `r`?
  q̵r̲
-/
#test_msgs in
#docs (.none) oneCharDistanceMatch "One-character distance match" :=
:::::::
{q}[]
:::::::

/--
error: No registered role `ac`.

Hint: Did you mean role `ab`?
  ac̵b̲
-/
#test_msgs in
#docs (.none) shortDistanceMatch "Short distance match" :=
:::::::
{ac}[]
:::::::

/--
error: No registered role `zz`.
-/
#test_msgs in
#docs (.none) shortDistanceNoMatch "Short distance no match" :=
:::::::
{zz}[]
:::::::

/--
error: No registered role `vww`.

Hint: Did you mean role `vvv`?
  vw̵w̵v̲v̲
-/
#test_msgs in
#docs (.none) threeCharDistanceMatch "Three-character distance match" :=
:::::::
{vww}[]
:::::::

/--
error: No registered role `www`.
-/
#test_msgs in
#docs (.none) threeCharDistanceNoMatch "Three-character distance no match" :=
:::::::
{www}[]
:::::::

/--
error: No registered role `yyyxx`.

Hint: Did you mean role `yyyyy`?
  yyyx̵x̵y̲y̲
-/
#test_msgs in
#docs (.none) middleDistanceMatch "Middle distance match" :=
:::::::
{yyyxx}[]
:::::::

/--
error: No registered role `yyxxx`.
-/
#test_msgs in
#docs (.none) middleDistanceNoMatch "Middle distance no match" :=
:::::::
{yyxxx}[]
:::::::

/--
error: No registered role `zzzaaa`.

Hint: Did you mean role `zzzzzz`?
  zzza̵a̵a̵z̲z̲z̲
-/
#test_msgs in
#docs (.none) longBoundaryDistanceMatch "Long boundary distance match" :=
:::::::
{zzzaaa}[]
:::::::

/--
error: No registered role `zzaaaa`.
-/
#test_msgs in
#docs (.none) longBoundaryDistanceNoMatch "Long boundary distance no match" :=
:::::::
{zzaaaa}[]
:::::::

/--
error: No registered role `multiAlphx`.

Hint: Did you mean role `multiAlpha`?
  • multiAlphx̵a̲
  • multiAlphx̵i̲
-/
#test_msgs in
#docs (.none) multiDistanceSuggestions "Multiple distance suggestions" :=
:::::::
{multiAlphx}[]
:::::::

/--
error: No registered role `distanceRegistred`.

Hint: Did you mean role `distanceRegistered`?
  distanceRegiste̲red
-/
#test_msgs in
#docs (.none) longDistanceMatch "Long distance match" :=
:::::::
{distanceRegistred}[]
:::::::

/--
error: No registered role `distanceNoMatchzzzz`.
-/
#test_msgs in
#docs (.none) longDistanceNoMatch "Long distance no match" :=
:::::::
{distanceNoMatchzzzz}[]
:::::::

end DistanceCases

namespace ShadowSource

@[role]
def shadowedRegistered : RoleExpanderOf Unit
  | (), _ => do
    `(Verso.Doc.Inline.text "shadowed-role")

end ShadowSource

namespace ShadowUse

def shadowedRegistered : Nat := 0

/-
The registered role's basename is shadowed here by a non-role declaration. Suggestions should
therefore use a qualified name that resolves to the registered role instead of the local declaration.
-/

/--
error: No registered role `ShadowSource.shadowedRegistred`.

Hint: Did you mean role `ShadowSource.shadowedRegistered`?
  ShadowSource.shadowedRegiste̲red
-/
#test_msgs in
#docs (.none) roleShadowedSuggestion "Shadowed role suggestion" :=
:::::::
{ShadowSource.shadowedRegistred}[]
:::::::

/--
error: No registered role `shadowedRegistred`.

Hint: Did you mean role `ShadowSource.shadowedRegistered`?
  s̵h̵a̵d̵o̵w̵e̵d̵R̵e̵g̵i̵s̵t̵r̵e̵d̵S̲h̲a̲d̲o̲w̲S̲o̲u̲r̲c̲e̲.̲s̲h̲a̲d̲o̲w̲e̲d̲R̲e̲g̲i̲s̲t̲e̲r̲e̲d̲
-/
#test_msgs in
#docs (.none) roleUnqualifiedShadowedSuggestion "Unqualified shadowed role suggestion" :=
:::::::
{shadowedRegistred}[]
:::::::

end ShadowUse

namespace CodeBlockCases

@[code_block]
def registeredBlock : CodeBlockExpanderOf Unit
  | (), str => do
    `(Verso.Doc.Block.code $(quote str.getString))

#docs (.none) codeBlockRegistered "Registered code block" :=
:::::::
```registeredBlock
content
```
:::::::

def unregisteredBlock : CodeBlockExpanderOf Unit
  | (), str => do
    `(Verso.Doc.Block.code $(quote str.getString))

/--
error: Declaration `unregisteredBlock` can be used as a code block expander but is not registered as a code block. Register it with `@[code_block]`.
-/
#test_msgs in
#docs (.none) codeBlockUnregistered "Unregistered code block" :=
:::::::
```unregisteredBlock
content
```
:::::::

def wrongBlockType : Nat := 7

/--
error: Declaration `wrongBlockType` was found but is not registered as a code block.
-/
#test_msgs in
#docs (.none) codeBlockWrongType "Wrong code block type" :=
:::::::
```wrongBlockType
content
```
:::::::

/--
error: No registered code block `registeredBlok`.

Hint: Did you mean code block `registeredBlock`?
  registeredBloc̲k
-/
#test_msgs in
#docs (.none) codeBlockTypo "Code block typo" :=
:::::::
```registeredBlok
content
```
:::::::

end CodeBlockCases

namespace DirectiveCases

@[directive]
def registeredDirective : DirectiveExpanderOf Unit
  | (), blocks => do
    let blocks ← blocks.mapM Verso.Doc.Elab.elabBlock
    `(Verso.Doc.Block.concat #[$blocks,*])

#docs (.none) directiveRegistered "Registered directive" :=
:::::::
:::registeredDirective
content
:::
:::::::

def unregisteredDirective : DirectiveExpanderOf Unit
  | (), blocks => do
    let blocks ← blocks.mapM Verso.Doc.Elab.elabBlock
    `(Verso.Doc.Block.concat #[$blocks,*])

/--
error: Declaration `unregisteredDirective` can be used as a directive expander but is not registered as a directive. Register it with `@[directive]`.
-/
#test_msgs in
#docs (.none) directiveUnregistered "Unregistered directive" :=
:::::::
:::unregisteredDirective
content
:::
:::::::

def wrongDirectiveType : Nat := 7

/--
error: Declaration `wrongDirectiveType` was found but is not registered as a directive.
-/
#test_msgs in
#docs (.none) directiveWrongType "Wrong directive type" :=
:::::::
:::wrongDirectiveType
content
:::
:::::::

/--
error: No registered directive `registeredDirektive`.

Hint: Did you mean directive `registeredDirective`?
  registeredDirek̵c̲tive
-/
#test_msgs in
#docs (.none) directiveTypo "Directive typo" :=
:::::::
:::registeredDirektive
content
:::
:::::::

end DirectiveCases

namespace BlockCommandCases

@[block_command]
def registeredCommand : BlockCommandOf Unit
  | () => do
    `(Verso.Doc.Block.para #[Verso.Doc.Inline.text "registered-command"])

#docs (.none) blockCommandRegistered "Registered block command" :=
:::::::
{registeredCommand}
:::::::

/-- info: #[Verso.Doc.Block.concat #[(Verso.Doc.Block.para #[Verso.Doc.Inline.text "registered-command"])]] -/
#test_msgs in
#eval blockCommandRegistered.toPart.content

def fallbackCommand : Verso.Doc.Block Verso.Doc.Genre.none :=
  Verso.Doc.Block.para #[Verso.Doc.Inline.text "fallback-command"]

#docs (.none) blockCommandFallback "Block command declaration fallback" :=
:::::::
{fallbackCommand}
:::::::

/-- info: #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "fallback-command"]] -/
#test_msgs in
#eval blockCommandFallback.toPart.content

/--
error: No registered block command `registeredComand`.

Hint: Did you mean block command `registeredCommand`?
  registeredComm̲and
-/
#test_msgs in
#docs (.none) blockCommandTypo "Block command typo" :=
:::::::
{registeredComand}
:::::::

