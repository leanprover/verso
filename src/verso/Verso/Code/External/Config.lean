/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
import Lean.Data.Options
import Lean.Exception
public import Lean.ToExpr
public import Lean.Data.Json.FromToJson

public import Verso.Doc.ArgParse
import Verso.Code.External.Env
public import Verso.Code.External.Files

open Lean
open Verso ArgParse

public section
register_option verso.examples.suggest : Bool := {
  defValue := false,
  descr := "Whether to suggest potentially-matching code examples"
}
end

namespace Verso.Code.External

public structure CodeConfig where
  /-- Whether to render proof states -/
  showProofStates : Bool := true
  /--
  Whether to treat names defined in the code as link targets.

  If unspecified, the block or inline element in question may fall back to a default value.
  -/
  defSite : Option Bool := none
deriving DecidableEq, Ord, Repr, Quote, ToExpr, ToJson, FromJson


variable [Monad m] [MonadOptions m] [MonadError m] [MonadLiftT CoreM m]

private def defaultProject : m String := do
  if let some p := verso.exampleProject.get? (← getOptions) then pure p else throwError "No default project specified"

private def defaultModule : m Name := do
  if let some m := verso.exampleModule.get? (← getOptions) then pure m.toName else throwError "No default module specified"

/--
Parses the project directory as a named argument {lit}`project`, falling back to the default if
specified in the option {option}`verso.exampleProject`.
-/
public def projectOrDefault : ArgParse m StrLit :=
  .named `project .strLit false <|>
  (Syntax.mkStrLit <$> .lift "default project" defaultProject) <|>
  .fail none (some "No `(project := ...)` argument provided and no default project set.")

/--
Parses the current module as a named argument {lit}`module`, falling back to the default if
specified in the option {option}`verso.exampleModule`.
-/
public def moduleOrDefault : ArgParse m Ident :=
  .named `module .ident false <|>
  (mkIdent <$> .lift "default module" defaultModule) <|>
  .fail none (some "No `(module := ...)` argument provided and no default module set.")

/--
A specification of which module to look in to find example code.
-/
public structure CodeModuleContext extends CodeConfig where
  /-- The module's name. -/
  module : Ident
  /-- The path at which the module's project is found -/
  project : StrLit

@[no_expose]
public instance : FromArgs CodeModuleContext m where
  fromArgs :=
    ((·, ·, ·, ·) <$> moduleOrDefault <*> projectOrDefault <*> .flag `showProofStates true <*> .flag `defSite true) <&> fun (m, p, s, d) =>
      ({module := m, project := p, showProofStates := s, defSite := d})

/--
A specification of which module to look in to find example code, potentially made more specific with
a named anchor.
-/
public structure CodeContext extends CodeModuleContext where
  /--
  The relevant `-- ANCHOR: X` to include
  -/
  anchor? : Option Ident

@[no_expose]
public instance : FromArgs CodeContext m where
  fromArgs := CodeContext.mk <$> fromArgs <*> .named `anchor .ident true

/--
A specification of which module to look in to find an example message, with its desired severity,
potentially made more specific with a named anchor.
-/
public structure MessageContext extends CodeContext where
  /--
  The desired severity of the message.
  -/
  severity : WithSyntax MessageSeverity
  /--
  Traces classes to show expanded by default
  -/
  expandTraces : List Lean.Name
  /--
  Only show the first trace with this title
  -/
  onlyTrace : Option String

@[no_expose]
public instance : FromArgs MessageContext m where
  fromArgs := (fun s ts t x => MessageContext.mk x s ts t) <$> .positional' `severity <*> .many (.named `expandTrace .name false) <*> (.named `onlyTrace .string true) <*> fromArgs

/--
A specification of which module to look in to find a quoted name, potentially made more specific with
a named anchor.
-/
public structure NameContext extends CodeContext where
  /--
  How to override the display of the name.
  -/
  show? : Option Ident

@[no_expose]
public instance : FromArgs NameContext m where
  fromArgs := NameContext.mk <$> fromArgs <*> .named' `show true
