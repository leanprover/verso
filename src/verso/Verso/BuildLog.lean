/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Lean.Data.Lsp.Basic
import Lean.Message

set_option doc.verso true
set_option linter.missingDocs true

/-!
A small logging abstraction for error reporting while generating readable output from a Verso
document.

Errors are non-fatal: the build runs to completion, but the process exit code reflects whether any
error was logged. Warnings never affect the exit code.
-/

namespace Verso

/--
The severity of a logged build message.
-/
public inductive Severity where
  | error
  | warning
deriving DecidableEq, Repr, Inhabited, Lean.ToJson, Lean.FromJson

/--
A source location attached to a logged message.
-/
public inductive SourceSpan where
  | none
  | pos (p : Lean.Lsp.Position)
  | range (r : Lean.Lsp.Range)
deriving Lean.ToJson, Lean.FromJson

public instance : Coe Lean.Lsp.Position SourceSpan := ⟨.pos⟩
public instance : Coe Lean.Lsp.Range SourceSpan := ⟨.range⟩

/--
An optional position or range coerces to a {name}`SourceSpan`, with {name}`none` becoming
{name}`SourceSpan.none`. This lets a call site assign an {lean}`Option Lean.Lsp.Position` directly
to a {name}`SourceSpan` field.
-/
public instance [Coe α SourceSpan] : Coe (Option α) SourceSpan where
  coe
    | none => .none
    | some x => x

/--
A resolved source location: a filename together with an optional source position.
-/
public structure SourceLoc where
  file : String
  span : SourceSpan := .none
deriving Lean.ToJson, Lean.FromJson

/-- Converts an LSP position (0-based) to a {name}`Lean.Position` (1-based line, 0-based column). -/
def SourceLoc.toLeanPosition (p : Lean.Lsp.Position) : Lean.Position :=
  ⟨p.line + 1, p.character⟩

/--
A logged build message.
-/
public structure LogMessage where
  severity : Severity
  text : String
  loc : Option SourceLoc

/--
Formats a {name}`LogMessage` for printing to stderr.
-/
public def LogMessage.format (msg : LogMessage) : String :=
  match msg.loc with
  | none => msg.text
  | some loc =>
    match loc.span with
    | .pos p =>
      Lean.mkErrorStringWithPos loc.file (SourceLoc.toLeanPosition p) msg.text
    | .range r =>
      Lean.mkErrorStringWithPos loc.file (SourceLoc.toLeanPosition r.start) msg.text
        (endPos := some (SourceLoc.toLeanPosition r.end))
    | .none => s!"{loc.file}: {msg.text}"

/--
Monads that can emit build log messages.
-/
public class MonadBuildLog (m : Type → Type) where
  log : Severity → String → (loc : Option SourceLoc := none) → m Unit

/--
Reports a build message of the given severity.
-/
public def report [MonadBuildLog m] (severity : Severity) (text : String) (loc : Option SourceLoc := none) : m Unit :=
  MonadBuildLog.log severity text loc

/--
Reports an error. Errors do not abort the build, but they cause a non-zero exit code.
-/
public def reportError [MonadBuildLog m] (text : String) (loc : Option SourceLoc := none) : m Unit :=
  MonadBuildLog.log .error text loc

/--
Reports a warning. Warnings do not affect the exit code.
-/
public def reportWarning [MonadBuildLog m] (text : String) (loc : Option SourceLoc := none) : m Unit :=
  MonadBuildLog.log .warning text loc

/--
A logger is a structure that both emits messages (typically to stderr) and tracks them for later
summarization.
-/
public structure Logger (m : Type → Type) where
  /-- Records a message of the given severity at the given optional source location. -/
  log : Severity → String → Option SourceLoc → m Unit
  /-- The errors logged so far. -/
  errors : m (Array LogMessage)
  /-- The warnings logged so far. -/
  warnings : m (Array LogMessage)

public instance [Applicative m] : Inhabited (Logger m) where
  default.log _ _ _ := pure ()
  default.errors := pure default
  default.warnings := pure default

/--
Creates a fresh {name}`Logger` that accumulates messages in {name}`IO.Ref`s in addition to printing
them to the current stderr (resolved at log time, rather than captured when {name}`Logger.new` is
called).
-/
public def Logger.new : IO (Logger IO) := do
  let errorsRef ← IO.mkRef #[]
  let warningsRef ← IO.mkRef #[]
  return {
    log severity text loc := do
      let msg : LogMessage := { severity, text, loc }
      match severity with
      | .error => errorsRef.modify (·.push msg)
      | .warning => warningsRef.modify (·.push msg)
      IO.eprintln msg.format
    errors := errorsRef.get
    warnings := warningsRef.get
  }

/--
Lifts a logger into a more powerful monad.
-/
public def Logger.lift [MonadLiftT m m'] (logger : Logger m) : Logger m' where
  log severity text loc := liftM (logger.log severity text loc)
  errors := liftM logger.errors
  warnings := liftM logger.warnings

public instance [MonadLiftT IO m] : Coe (Logger IO) (Logger m) := ⟨Logger.lift⟩

/--
Reports an error directly through a {name}`Logger` value. Most callers should use
{name}`reportError` instead.
-/
public def Logger.reportError (logger : Logger m) (text : String) (loc : Option SourceLoc := none) : m Unit :=
  logger.log .error text loc

/--
Reports a warning directly through a {name}`Logger` value. Most callers should use
{name}`reportWarning` instead.
-/
public def Logger.reportWarning (logger : Logger m) (text : String) (loc : Option SourceLoc := none) : m Unit :=
  logger.log .warning text loc

/--
Whether any error has been logged.
-/
public def Logger.hasErrors [Functor m] (logger : Logger m) : m Bool :=
  (!·.isEmpty) <$> logger.errors

/--
Whether any warning has been logged.
-/
public def Logger.hasWarnings [Functor m] (logger : Logger m) : m Bool :=
  (!·.isEmpty) <$> logger.warnings

/--
The process exit code implied by the logged messages: non-zero if and only if an error was logged.
-/
public def Logger.exitCode [Monad m] (logger : Logger m) : m UInt32 := do
  return if (← logger.hasErrors) then 1 else 0

/--
Prints a summary of the logged errors and returns the implied exit code, leaving the process to
decide whether to propagate it.
-/
public def Logger.failIfErrors [Monad m] [MonadLiftT IO m] (logger : Logger m) : m UInt32 := do
  match (← logger.errors).size with
  | 0 => return 0
  | 1 => liftM (IO.eprintln "An error was encountered!"); return 1
  | n => liftM (IO.eprintln s!"{n} errors were encountered!"); return 1

/--
Runs a build's main action with a fresh {lean}`Logger IO`, then returns the exit code implied by the
messages it logged (see {name}`Logger.failIfErrors`).
-/
public def withLogger [Monad m] [MonadLiftT IO m] (act : Logger IO → m Unit) : m UInt32 := do
  let logger ← Logger.new
  act logger
  logger.failIfErrors

/--
Equips a monad with a {name}`Logger`, and thus a {name}`MonadBuildLog` instance.
-/
public abbrev BuildLogT (m : Type → Type) : Type → Type := ReaderT (Logger m) m

/--
Runs a {name}`BuildLogT` action with a fresh {lean}`Logger IO`, then returns the exit code implied
by the messages it logged.

This is the {lean}`BuildLogT IO` specialization of {name}`withLogger`, and it can simplify the
syntax of call sites.
-/
public def runWithLogger (act : BuildLogT IO Unit) : IO UInt32 := do
  withLogger (act.run ·)

public instance {m m' : Type → Type}
    [MonadReaderOf (Logger m') m] [Monad m] [MonadLiftT m' m] :
    MonadBuildLog m where
  log severity text loc := do
    let logger : Logger m' ← readThe (Logger m')
    liftM (logger.log severity text loc)

-- These instances can't be merged because it would leave one of the semiOutParams of MonadLiftT
-- underdetermined

public instance {m m' : Type → Type} [MonadLiftT m' m] :
    MonadLift (ReaderT (Logger m) m) (ReaderT (Logger m') m) where
  monadLift act := fun logger => act logger.lift

public instance {m' m n : Type → Type} [MonadLift m n] :
    MonadLift (ReaderT (Logger m') m) (ReaderT (Logger m') n) where
  monadLift act := fun logger => MonadLift.monadLift (act logger)
