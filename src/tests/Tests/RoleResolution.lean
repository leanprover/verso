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

/-
Role resolution has four relevant outcomes:
1. role function exists, has type `RoleExpander`, and is registered - good.
2. role function exists, has a role type, but is not registered - bad.
3. role function exists, but has the wrong type - bad.
4. role function does not exist - unresolved role name.
-/

@[role_expander registered]
def registered : Verso.Doc.Elab.RoleExpander
  | _, _ => do
    pure #[← `(Verso.Doc.Inline.text "registered-role")]

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
error: Role function `unregistered` was found but not registered as a role. Register it with `@[role]` or `@[role_expander ...]`.
-/
#guard_msgs in
#docs (.none) roleCase2 "Case 2" :=
:::::::
{unregistered}[]
:::::::

def wrongType : Nat := 7

/--
error: Function `wrongType` was found but likely not a role.
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
error: No registered role `nothereatallzzzz`. Available roles (showing 20 of 40): anchor, anchorError, anchorInfo, anchorName, anchorTerm, anchorWarning, blob, citehere, citep, citet, conv, deftech, draft, htmlSpan, index, inst, label, lean, leanCommand, leanInline
-/
#guard_msgs in
#docs (.none) roleCase5 "Case 5" :=
:::::::
{nothereatallzzzz}[]
:::::::

namespace ManualCases
open Genre Manual

@[role_expander manualRegistered]
def manualRegistered : Verso.Doc.Elab.RoleExpander
  | _, _ => do
    pure #[← `(Verso.Doc.Inline.text "manual-registered-role")]

#docs (Manual) roleCase1 "Manual Case 1" :=
:::::::
{manualRegistered}[]
:::::::

def manualUnregistered : Verso.Doc.Elab.RoleExpander
  | _, _ => do
    pure #[← `(Verso.Doc.Inline.text "manual-unregistered-role")]

/--
error: Role function `manualUnregistered` was found but not registered as a role. Register it with `@[role]` or `@[role_expander ...]`.
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

/--
error: No registered role `manualNowhereNearZzzzz`. Available roles (showing 20 of 41): anchor, anchorError, anchorInfo, anchorName, anchorTerm, anchorWarning, blob, citehere, citep, citet, conv, deftech, draft, htmlSpan, index, inst, label, lean, leanCommand, leanInline
-/
#guard_msgs in
#docs (Manual) roleCase4 "Manual Case 4" :=
:::::::
{manualNowhereNearZzzzz}[]
:::::::

end ManualCases

namespace BlogCases
open Genre Blog

@[role_expander blogRegistered]
def blogRegistered : Verso.Doc.Elab.RoleExpander
  | _, _ => do
    pure #[← `(Verso.Doc.Inline.text "blog-registered-role")]

#docs (Blog.Post) roleCase1 "Blog Case 1" :=
:::::::
{blogRegistered}[]
:::::::

def blogUnregistered : Verso.Doc.Elab.RoleExpander
  | _, _ => do
    pure #[← `(Verso.Doc.Inline.text "blog-unregistered-role")]

/--
error: Role function `blogUnregistered` was found but not registered as a role. Register it with `@[role]` or `@[role_expander ...]`.
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

/--
error: No registered role `blogNoCloseMatchZzzzz`. Available roles (showing 20 of 42): anchor, anchorError, anchorInfo, anchorName, anchorTerm, anchorWarning, blob, blogRegistered, citehere, citep, citet, conv, deftech, draft, htmlSpan, index, inst, label, lean, leanCommand
-/
#guard_msgs in
#docs (Blog.Post) roleCase4 "Blog Case 4" :=
:::::::
{blogNoCloseMatchZzzzz}[]
:::::::

end BlogCases

end Verso.RoleResolutionTest
