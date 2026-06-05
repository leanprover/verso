/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/
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
#guard_msgs in
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
#guard_msgs in
#eval roleLegacyRegistered.toPart.content

def unregistered : RoleExpander
  | _, _ => do
    pure #[← `(Verso.Doc.Inline.text "unregistered-role")]

/--
error: Declaration `unregistered` can be used as a role expander but is not registered as a role. Register it with `@[role]`.
-/
#guard_msgs in
#docs (.none) roleUnregistered "Unregistered role" :=
:::::::
{unregistered}[]
:::::::

def wrongType : Nat := 7

/--
error: Declaration `wrongType` was found but is not registered as a role.
-/
#guard_msgs in
#docs (.none) roleWrongType "Wrong role type" :=
:::::::
{wrongType}[]
:::::::

/--
error: No registered role `registred`.

Hint: Did you mean role `registered`?
  registe̲red
-/
#guard_msgs in
#docs (.none) roleTypo "Role typo" :=
:::::::
{registred}[]
:::::::

/--
error: No registered role `legacyRegistred`.

Hint: Did you mean role `legacyRegistered`?
  legacyRegiste̲red
-/
#guard_msgs in
#docs (.none) roleLegacyTypo "Legacy role typo" :=
:::::::
{legacyRegistred}[]
:::::::

/--
error: No registered role `nothereatallzzzz`.
-/
#guard_msgs in
#docs (.none) roleNoCloseMatch "No close role match" :=
:::::::
{nothereatallzzzz}[]
:::::::

end RoleCases

namespace DistanceCases

@[role]
def ab : RoleExpanderOf Unit
  | (), _ => do
    `(Verso.Doc.Inline.text "short-distance-role")

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

/--
error: No registered role `ac`.

Hint: Did you mean role `ab`?
  ac̵b̲
-/
#guard_msgs in
#docs (.none) shortDistanceMatch "Short distance match" :=
:::::::
{ac}[]
:::::::

/--
error: No registered role `zz`.
-/
#guard_msgs in
#docs (.none) shortDistanceNoMatch "Short distance no match" :=
:::::::
{zz}[]
:::::::

/-
The suggestion cutoff table is:
* input length less than 3: Levenshtein distance at most 1
* input length less than 6: Levenshtein distance at most 2
* otherwise: Levenshtein distance at most 3
-/

/--
error: No registered role `yyyxx`.

Hint: Did you mean role `yyyyy`?
  yyyx̵x̵y̲y̲
-/
#guard_msgs in
#docs (.none) middleDistanceMatch "Middle distance match" :=
:::::::
{yyyxx}[]
:::::::

/--
error: No registered role `yyxxx`.
-/
#guard_msgs in
#docs (.none) middleDistanceNoMatch "Middle distance no match" :=
:::::::
{yyxxx}[]
:::::::

/--
error: No registered role `zzzaaa`.

Hint: Did you mean role `zzzzzz`?
  zzza̵a̵a̵z̲z̲z̲
-/
#guard_msgs in
#docs (.none) longBoundaryDistanceMatch "Long boundary distance match" :=
:::::::
{zzzaaa}[]
:::::::

/--
error: No registered role `zzaaaa`.
-/
#guard_msgs in
#docs (.none) longBoundaryDistanceNoMatch "Long boundary distance no match" :=
:::::::
{zzaaaa}[]
:::::::

/--
error: No registered role `distanceRegistred`.

Hint: Did you mean role `distanceRegistered`?
  distanceRegiste̲red
-/
#guard_msgs in
#docs (.none) longDistanceMatch "Long distance match" :=
:::::::
{distanceRegistred}[]
:::::::

/--
error: No registered role `distanceNoMatchzzzz`.
-/
#guard_msgs in
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
#guard_msgs in
#docs (.none) roleShadowedSuggestion "Shadowed role suggestion" :=
:::::::
{ShadowSource.shadowedRegistred}[]
:::::::

/--
error: No registered role `shadowedRegistred`.

Hint: Did you mean role `ShadowSource.shadowedRegistered`?
  s̵h̵a̵d̵o̵w̵e̵d̵R̵e̵g̵i̵s̵t̵r̵e̵d̵S̲h̲a̲d̲o̲w̲S̲o̲u̲r̲c̲e̲.̲s̲h̲a̲d̲o̲w̲e̲d̲R̲e̲g̲i̲s̲t̲e̲r̲e̲d̲
-/
#guard_msgs in
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
#guard_msgs in
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
#guard_msgs in
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
#guard_msgs in
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
#guard_msgs in
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
#guard_msgs in
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
#guard_msgs in
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
#guard_msgs in
#eval blockCommandRegistered.toPart.content

def fallbackCommand : Verso.Doc.Block Verso.Doc.Genre.none :=
  Verso.Doc.Block.para #[Verso.Doc.Inline.text "fallback-command"]

#docs (.none) blockCommandFallback "Block command declaration fallback" :=
:::::::
{fallbackCommand}
:::::::

/-- info: #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "fallback-command"]] -/
#guard_msgs in
#eval blockCommandFallback.toPart.content

/--
error: No registered block command `registeredComand`.

Hint: Did you mean block command `registeredCommand`?
  registeredComm̲and
-/
#guard_msgs in
#docs (.none) blockCommandTypo "Block command typo" :=
:::::::
{registeredComand}
:::::::

end BlockCommandCases

end Verso.ExtensionResolutionTest
