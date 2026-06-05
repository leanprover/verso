/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/
import Verso
import VersoManual
import VersoBlog

namespace Verso.RoleResolutionTest
set_option guard_msgs.diff true

open Lean
open Verso.Doc.Elab

/-
Role resolution has four relevant outcomes:
1. a declaration is registered as a role - good.
2. a declaration can be used as a role expander, but is not registered - bad.
3. a declaration exists, but is not registered as a role - bad.
4. a declaration does not exist - unresolved role name.
-/

@[role]
def registered : RoleExpanderOf Unit
  | (), _ => do
    `(Verso.Doc.Inline.text "registered-role")

#docs (.none) roleCase1 "Case 1" :=
:::::::
{registered}[]
:::::::

/-- info: #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "registered-role"]] -/
#guard_msgs in
#eval roleCase1.toPart.content

def unregistered : Verso.Doc.Elab.RoleExpander
  | _, _ => do
    pure #[← `(Verso.Doc.Inline.text "unregistered-role")]

/--
error: Declaration `unregistered` can be used as a role expander but is not registered as a role. Register it with `@[role]`.
-/
#guard_msgs in
#docs (.none) roleCase2 "Case 2" :=
:::::::
{unregistered}[]
:::::::

def wrongType : Nat := 7

/--
error: Declaration `wrongType` was found but is not registered as a role.
-/
#guard_msgs in
#docs (.none) roleCase3 "Case 3" :=
:::::::
{wrongType}[]
:::::::

/--
error: No registered role `registred`.

Hint: Did you mean role `registered`?
  registe̲red
-/
#guard_msgs in
#docs (.none) roleCase4 "Case 4" :=
:::::::
{registred}[]
:::::::

/--
error: No registered role `nothereatallzzzz`.
-/
#guard_msgs in
#docs (.none) roleCase5 "Case 5" :=
:::::::
{nothereatallzzzz}[]
:::::::

namespace ManualCases
open Genre Manual

@[role]
def manualRegistered : RoleExpanderOf Unit
  | (), _ => do
    `(Verso.Doc.Inline.text "manual-registered-role")

#docs (Manual) roleCase1 "Manual Case 1" :=
:::::::
{manualRegistered}[]
:::::::

def manualUnregistered : Verso.Doc.Elab.RoleExpander
  | _, _ => do
    pure #[← `(Verso.Doc.Inline.text "manual-unregistered-role")]

/--
error: Declaration `manualUnregistered` can be used as a role expander but is not registered as a role. Register it with `@[role]`.
-/
#guard_msgs in
#docs (Manual) roleCase2 "Manual Case 2" :=
:::::::
{manualUnregistered}[]
:::::::

/--
error: No registered role `manualRegistred`.

Hint: Did you mean role `manualRegistered`?
  manualRegiste̲red
-/
#guard_msgs in
#docs (Manual) roleCase3 "Manual Case 3" :=
:::::::
{manualRegistred}[]
:::::::

end ManualCases

namespace BlogCases
open Genre Blog

@[role]
def blogRegistered : RoleExpanderOf Unit
  | (), _ => do
    `(Verso.Doc.Inline.text "blog-registered-role")

#docs (Blog.Post) roleCase1 "Blog Case 1" :=
:::::::
{blogRegistered}[]
:::::::

def blogUnregistered : Verso.Doc.Elab.RoleExpander
  | _, _ => do
    pure #[← `(Verso.Doc.Inline.text "blog-unregistered-role")]

/--
error: Declaration `blogUnregistered` can be used as a role expander but is not registered as a role. Register it with `@[role]`.
-/
#guard_msgs in
#docs (Blog.Post) roleCase2 "Blog Case 2" :=
:::::::
{blogUnregistered}[]
:::::::

/--
error: No registered role `blogRegistred`.

Hint: Did you mean role `blogRegistered`?
  blogRegiste̲red
-/
#guard_msgs in
#docs (Blog.Post) roleCase3 "Blog Case 3" :=
:::::::
{blogRegistred}[]
:::::::

end BlogCases

namespace ShadowSource

@[role]
def shadowedRegistered : RoleExpanderOf Unit
  | (), _ => do
    `(Verso.Doc.Inline.text "shadowed-role")

end ShadowSource

namespace ShadowUse

def shadowedRegistered : Nat := 0

/--
error: No registered role `ShadowSource.shadowedRegistred`.

Hint: Did you mean role `ShadowSource.shadowedRegistered`?
  ShadowSource.shadowedRegiste̲red
-/
#guard_msgs in
#docs (.none) roleCase6 "Case 6" :=
:::::::
{ShadowSource.shadowedRegistred}[]
:::::::

end ShadowUse

namespace OtherExtensionCases

@[code_block]
def registeredBlock : CodeBlockExpanderOf Unit
  | (), str => do
    `(Verso.Doc.Block.code $(quote str.getString))

def unregisteredBlock : CodeBlockExpanderOf Unit
  | (), str => do
    `(Verso.Doc.Block.code $(quote str.getString))

/--
error: Declaration `unregisteredBlock` can be used as a code block expander but is not registered as a code block. Register it with `@[code_block]`.
-/
#guard_msgs in
#docs (.none) codeBlockCase1 "Code Block Case 1" :=
:::::::
```unregisteredBlock
content
```
:::::::

/--
error: No registered code block `registeredBlok`.

Hint: Did you mean code block `registeredBlock`?
  registeredBloc̲k
-/
#guard_msgs in
#docs (.none) codeBlockCase2 "Code Block Case 2" :=
:::::::
```registeredBlok
content
```
:::::::

@[directive]
def registeredDirective : DirectiveExpanderOf Unit
  | (), blocks => do
    let blocks ← blocks.mapM Verso.Doc.Elab.elabBlock
    `(Verso.Doc.Block.concat #[$blocks,*])

def unregisteredDirective : DirectiveExpanderOf Unit
  | (), blocks => do
    let blocks ← blocks.mapM Verso.Doc.Elab.elabBlock
    `(Verso.Doc.Block.concat #[$blocks,*])

/--
error: Declaration `unregisteredDirective` can be used as a directive expander but is not registered as a directive. Register it with `@[directive]`.
-/
#guard_msgs in
#docs (.none) directiveCase1 "Directive Case 1" :=
:::::::
:::unregisteredDirective
content
:::
:::::::

/--
error: No registered directive `registeredDirektive`.

Hint: Did you mean directive `registeredDirective`?
  registeredDirek̵c̲tive
-/
#guard_msgs in
#docs (.none) directiveCase2 "Directive Case 2" :=
:::::::
:::registeredDirektive
content
:::
:::::::

@[block_command]
def registeredCommand : BlockCommandOf Unit
  | () => do
    `(Verso.Doc.Block.para #[Verso.Doc.Inline.text "registered-command"])

/--
error: No registered block command `registeredComand`.

Hint: Did you mean block command `registeredCommand`?
  registeredComm̲and
-/
#guard_msgs in
#docs (.none) blockCommandCase2 "Block Command Case 2" :=
:::::::
{registeredComand}
:::::::

end OtherExtensionCases

end Verso.RoleResolutionTest
