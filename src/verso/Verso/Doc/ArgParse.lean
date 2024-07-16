/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso.Doc
import Verso.Hover

open Lean Elab
open Verso Doc

namespace Verso

namespace ArgParse

section

variable (m) [Monad m] [MonadInfoTree m] [MonadResolveName m] [MonadEnv m] [MonadError m]

structure ValDesc (α) where
  description : MessageData
  get : ArgVal → m α

inductive ArgParse (m) : Type → Type 1 where
  | fail (stx? : Option Syntax) (message? : Option MessageData) : ArgParse m α
  | pure (val : α) : ArgParse m α
  | positional (nameHint : Name) (val : ValDesc m α) : ArgParse m α
  | named (name : Name) (val : ValDesc m α) (optional : Bool) : ArgParse m (if optional then Option α else α)
  | anyNamed (name : String) (val : ValDesc m α) : ArgParse m (Ident × α)
  | done : ArgParse m Unit
  | orElse (p1 : ArgParse m α) (p2 : Unit → ArgParse m α) : ArgParse m α
  | seq (p1 : ArgParse m (α → β)) (p2 : Unit → ArgParse m α) : ArgParse m β

instance : Inhabited (ArgParse m α) where
  default := .fail none none

instance : Applicative (ArgParse m) where
  pure := ArgParse.pure
  seq := ArgParse.seq

instance : Alternative (ArgParse m) where
  failure := ArgParse.fail none none
  orElse := ArgParse.orElse

def ArgParse.describe : ArgParse m α → MessageData
  | .fail _ msg? => msg?.getD "Cannot succeed"
  | .pure x => "No arguments expected"
  | .positional _x v => v.description
  | .named x v opt => if opt then "[" else "" ++ m!"{x} : {v.description}" ++ if opt then "]" else ""
  | .anyNamed x v => s!"{x}: a named " ++ v.description
  | .done => "no arguments remaining"
  | .orElse p1 p2 => p1.describe ++ " or " ++ (p2 ()).describe
  | .seq p1 p2 => p1.describe ++ " then " ++ (p2 ()).describe

scoped instance [Monad m] [MonadError m] : MonadError (StateT σ m) where
  throw e := fun _ => throw e
  tryCatch act handler := fun st => tryCatch (act st) (fun e => handler e st)
  getRef := fun st => (·, st) <$> getRef
  withRef ref act := fun st => withRef ref (act st)
  add stx msg := fun st => (·, st) <$> AddErrorMessageContext.add stx msg

structure ParseState where
  remaining : Array Arg
  info : Array (Syntax × MessageData)

-- NB the order of ExceptT and StateT is important here
def ArgParse.parse : ArgParse m α → ExceptT (Array Arg × Exception) (StateT ParseState m) α
  | .fail stx? msg? => do
    let stx ← stx?.getDM getRef
    let msg := msg?.getD "failed"
    throw ((← get).remaining, .error stx msg)
  | .pure x => Pure.pure x
  | .positional x vp => do
    let initArgs := (← get).remaining
    if let some (v, args') := getPositional initArgs then
      let val? : Except (Array Arg × Exception) α ← liftM <|
        try
          Except.ok <$> vp.get v
        catch exn => Pure.pure <| Except.error (initArgs, exn)
      match val? with
      | .ok val =>
        modify fun s => {s with remaining := args'}
        Pure.pure val
      | .error e => throw e
    else throw ((← get).remaining, .error (← getRef) m!"Positional argument {x} ({vp.description}) not found")
  | .named x vp optional => do
    let initArgs := (← get).remaining
    if let some (stx, v, args') := getNamed initArgs x then
      let val? : Except (Array Arg × Exception) _ ← liftM <|
        try
          Except.ok <$> vp.get v
        catch exn => Pure.pure <| Except.error (initArgs, exn)
      match val? with
      | .ok val =>
        modify fun s => {s with remaining := args', info := s.info.push (stx, vp.description)}
        Pure.pure <| match optional with
          | true => some val
          | false => val
      | .error e => throw e
    else match optional with
      | true => Pure.pure none
      | false => throw ((← get).remaining, .error (← getRef) m!"Named argument {x} ({vp.description}) not found")
  | .anyNamed x vp => do
    let initArgs := (← get).remaining
    if h : initArgs.size > 0 then
      match initArgs[0] with
      | .anon _ =>
        throw ((← get).remaining, .error (← getRef) m!"Name-argument pair '{x}' ({vp.description}) expected, got anonymous argument")
      | .named stx y v =>
        let val? : Except (Array Arg × Exception) _ ← liftM <|
          try
            Except.ok <$> vp.get v
          catch exn => Pure.pure <| Except.error (initArgs, exn)
        match val? with
        | .ok val =>
          modify fun s => {s with remaining := initArgs.extract 1 initArgs.size}
          Pure.pure (y, val)
        | .error e => throw e
    else throw ((← get).remaining, .error (← getRef) m!"Name-argument pair '{x}' ({vp.description}) not found")
  | .done => do
    let args := (← get).remaining
    if h : args.size > 0 then
      match args[0] with
      | .anon v => throw (args, .error v.syntax "Unexpected argument")
      | .named stx _ _ => throw (args, .error stx "Unexpected argument")
    else Pure.pure ()
  | .orElse p1 p2 =>
    try p1.parse
    catch
      | e1@(args1, _) =>
        try (p2 ()).parse
          catch
          | e2@(args2, _) =>
            if args2.size < args1.size then throw e1 else throw e2
  | .seq p1 p2 => Seq.seq p1.parse (fun () => p2 () |>.parse)
where
  getNamed (args : Array Arg) (x : Name) : Option (Syntax × ArgVal × Array Arg) := Id.run do
    for h : i in [0:args.size] do
      if let .named stx y v := args[i] then
        if y.getId == x then return some (stx, v, args.extract 0 i ++ args.extract (i+1) args.size)
    return none
  getPositional (args : Array Arg) : Option (ArgVal × Array Arg) := Id.run do
    for h : i in [0:args.size] do
      if let .anon v := args[i] then
        return some (v, args.extract 0 i ++ args.extract (i+1) args.size)
    return none
end

variable {m} [Monad m] [MonadInfoTree m] [MonadResolveName m] [MonadEnv m] [MonadError m] [MonadLiftT CoreM m]

def ValDesc.bool : ValDesc m Bool where
  description := m!"{true} or {false}"
  get
    | .name b => do
      let b' ← liftM <| realizeGlobalConstNoOverloadWithInfo b
      if b' == ``true then pure true
      else if b' == ``false then pure false
      else throwErrorAt b "Expected 'true' or 'false'"
    | other => throwError "Expected Boolean, got {repr other}"

def ValDesc.string : ValDesc m String where
  description := m!"a string"
  get
    | .str s => pure s.getString
    | other => throwError "Expected string, got {repr other}"

def ValDesc.ident : ValDesc m Ident where
  description := m!"an identifier"
  get
    | .name x => pure x
    | other => throwError "Expected string, got {repr other}"

def ValDesc.name : ValDesc m Name where
  description := m!"a name"
  get
    | .name x => pure x.getId
    | other => throwError "Expected string, got {repr other}"


def ArgParse.run [Monad m] [MonadInfoTree m] [MonadResolveName m] [MonadEnv m] [MonadError m] [MonadLiftT IO m] (p : ArgParse m α) (args : Array Arg) : m α := do
  match ← p.parse _ ⟨args, #[]⟩ with
  | (.ok v, ⟨more, info⟩) =>
    if more.size = 0 then
      for (loc, what) in info do
        Verso.Hover.addCustomHover loc what
      return v
    else throwError "Unexpected arguments {repr more}"
  | (.error e, _) => throw e.snd
