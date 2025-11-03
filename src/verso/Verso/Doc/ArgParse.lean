/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso.Doc
import Verso.Hover
import Lean.Parser
import Lean.Elab.GuardMsgs
import Verso.Parser
import Verso.SyntaxUtils

open Lean Elab
open Verso Doc

namespace Verso

namespace ArgParse

variable (m) [Monad m] [MonadInfoTree m] [MonadResolveName m] [MonadEnv m] [MonadError m]


inductive SigDoc where
  | text (str : String)
  | name (name : Name)
  | append (d1 d2 : SigDoc)

instance : Append SigDoc := ⟨.append⟩

instance : Coe String SigDoc := ⟨.text⟩

instance : Coe Name SigDoc := ⟨.name⟩

def SigDoc.toMessageData : SigDoc → MessageData
  | .text s => s
  | .append x y => x.toMessageData ++ y.toMessageData
  | .name x => x

instance : ToMessageData SigDoc where
  toMessageData x := x.toMessageData

section
variable {m} [Monad m] [MonadResolveName m] [MonadEnv m] [MonadOptions m] [MonadLog m] [AddMessageContext m]
def SigDoc.toString : SigDoc → m String
  | .text s => pure s
  | .name x => do
    let x ← unresolveNameGlobal x
    pure x.toString
  | .append d1 d2 => do
    return (← d1.toString) ++ (← d2.toString)
end

elab "doc!" s:interpolatedStr(ident) : term => do
  let mut out ← Meta.mkAppM ``SigDoc.text #[toExpr ""]
  for part in s.raw.getArgs do
    if let some str := part.isInterpolatedStrLit? then
      out ← Meta.mkAppM ``SigDoc.append #[out, ← Meta.mkAppM ``SigDoc.text #[toExpr str]]
    else if part.getKind == identKind then
      let x ← realizeGlobalConstNoOverloadWithInfo part
      out ← Meta.mkAppM ``SigDoc.append #[out, ← Meta.mkAppM ``SigDoc.name #[toExpr x]]
    else
      throwErrorAt part "Didn't understand"
  return out

/--
Documents which kinds of values a `ValDesc` might match.

These are typically constructed using `CanMatch.Ident`, `CanMatch.String`, `CanMatch.Num`, and the
`Union CanMatch` instance.
-/
structure CanMatch where
  /-- Identifiers may match -/
  ident : Bool
  /-- String literals may match -/
  string : Bool
  /-- Numerals may match -/
  num : Bool

def CanMatch.toString (m : CanMatch) : String :=
  let s :=
    (if m.ident then ["Ident"] else []) ++
    (if m.string then ["String"] else []) ++
    (if m.num then ["Num"] else []) |> String.intercalate " | "
  if s.isEmpty then "∅" else s

def CanMatch.format (m : CanMatch) : Std.Format :=
  let sep : Std.Format := .text " |" ++ .line
  let s :=
    (if m.ident then ["Ident"] else []) ++
    (if m.string then ["String"] else []) ++
    (if m.num then ["Num"] else [])
  if s.isEmpty then "∅" else .group (sep.joinSep s)

instance : ToString CanMatch := ⟨CanMatch.toString⟩

/--
Identifiers can match this argument.
-/
def CanMatch.Ident : CanMatch := { ident := true, string := false, num := false }

/--
Strings can match this argument.
-/
def CanMatch.String : CanMatch := { ident := false, string := true, num := false }

/--
Numbers can match this argument.
-/
def CanMatch.Num : CanMatch := { ident := false, string := false, num := true }

instance : Union CanMatch where
  union a b := {
    ident := a.ident || b.ident,
    string := a.string || b.string,
    num := a.num || b.num
  }

/--
A means of transforming a Verso argument value into a given type.
-/
structure ValDesc (α) where
  /-- How should this argument be documented in automatically-generated signatures? -/
  description : SigDoc
  /-- Which of the three kinds of values can match this argument? -/
  signature : CanMatch
  /-- How to transform the value into the given type. -/
  get : ArgVal → m α

instance [Functor m] : Functor (ValDesc m) where
  map f d := { d with get := fun v => f <$> d.get v }

/--
A canonical way to convert a Verso argument into a given type.
-/
class FromArgVal (α : Type) (m : Type → Type) where
  /--
  A canonical way to convert a Verso argument into a given type.
  -/
  fromArgVal : ValDesc m α

export FromArgVal (fromArgVal)

end ArgParse

open ArgParse

/--
A parser for arguments in some underlying monad.
-/
inductive ArgParse (m : Type → Type) : Type → Type 1 where
  /--
  Fails with the provided error message.
  -/
  | fail (stx? : Option Syntax) (message? : Option SigDoc) : ArgParse m α
  /--
  Returns a value without parsing any arguments.
  -/
  | protected pure (val : α) : ArgParse m α
  /--
  Provides an argument value by lifting an action from the underlying monad.
  -/
  | lift (desc : String) (act : m α) : ArgParse m α
  /--
  Matches a positional argument.
  -/
  | positional (nameHint : Name) (val : ValDesc m α) (doc? : Option SigDoc := none) :
    ArgParse m α
  /--
  Matches an argument with the provided name.
  -/
  | named (name : Name) (val : ValDesc m α) (optional : Bool) (doc? : Option SigDoc := none) :
    ArgParse m (if optional then Option α else α)
  /--
  Matches any named argument.
  -/
  | anyNamed (name : Name) (val : ValDesc m α) (doc? : Option SigDoc := none) : ArgParse m (Ident × α)
  /--
  Matches a flag with the provided name.
  -/
  | flag (name : Name) (default : Bool) (doc? : Option SigDoc := none) : ArgParse m Bool
  /--
  Matches a flag with the provided name, deriving a default value from the monad
  -/
  | flagM (name : Name) (default : m Bool) (doc? : Option SigDoc := none) : ArgParse m Bool
  /--
  No further arguments are allowed.
  -/
  | done : ArgParse m Unit
  /--
  Error recovery.
  -/
  | protected orElse (p1 : ArgParse m α) (p2 : Unit → ArgParse m α) : ArgParse m α
  /--
  The sequencing operation of an applicative functor.
  -/
  | protected seq (p1 : ArgParse m (α → β)) (p2 : Unit → ArgParse m α) : ArgParse m β
  /--
  Zero or more repetitions.
  -/
  | protected many : ArgParse m α → ArgParse m (List α)
  /-- Returns all remaining arguments. This is useful for consuming some, then forwarding the rest. -/
  | protected remaining : ArgParse m (Array Arg)

namespace ArgParse
section
variable (m) [Monad m] [MonadInfoTree m] [MonadResolveName m] [MonadEnv m] [MonadError m] [MonadLiftT CoreM m] [MonadLog m] [AddMessageContext m] [MonadOptions m]

/--
A canonical way to convert a sequence of Verso arguments into a given type.
-/
class FromArgs (α : Type) (m : Type → Type) where
  /-- Converts a sequence of arguments into a value. -/
  fromArgs : ArgParse m α

export Verso.ArgParse.FromArgs (fromArgs)

instance : FromArgs Unit m := ⟨.pure ()⟩

/--
Matches a positional argument using the type's `FromArgVal` instance.
-/
def positional' {m} [FromArgVal α m] (nameHint : Name) (doc? : Option SigDoc := none) : ArgParse m α :=
  .positional nameHint fromArgVal (doc? := doc?)

/--
Matches a named argument using the type's `FromArgVal` instance.
-/
def named' {m} [FromArgVal α m]
    (name : Name) (optional : Bool) (doc? : Option SigDoc := none) :
    ArgParse m (if optional then Option α else α) :=
  .named name fromArgVal optional (doc? := doc?)

/--
Matches any named argument using the type's `FromArgVal` instance.
-/
def anyNamed' {m} [FromArgVal α m]
    (name : Name) (doc? : Option SigDoc := none) :
    ArgParse m (Ident × α) :=
  .anyNamed name fromArgVal (doc? := doc?)


instance : Inhabited (ArgParse m α) where
  default := .fail none none

instance : Applicative (ArgParse m) where
  pure := ArgParse.pure
  seq := ArgParse.seq

instance : Alternative (ArgParse m) where
  failure := ArgParse.fail none none
  orElse := ArgParse.orElse

/--
Matches an argument with the provided name. If the argument is not present, `default` is returned.
-/
def namedD {m} (name : Name) (val : ValDesc m α) (default : α) : ArgParse m α :=
  named name val true <&> (·.getD default)

/--
Matches an argument with the provided name using the type's `FromArgVal` instance. If the argument
is not present, `default` is returned.
-/
def namedD' {m} [FromArgVal α m] (name : Name) (default : α) : ArgParse m α :=
  namedD name fromArgVal default

def describe : ArgParse m α → SigDoc
  | .fail _ msg? => msg?.getD "Cannot succeed"
  | .pure x => "No arguments expected"
  | .lift desc act => desc
  | .positional _x v _ => v.description
  | .named x v opt _ => if opt then "[" else "" ++ x.toString ++ doc!" : " ++ v.description ++ if opt then "]" else ""
  | .anyNamed x v _ => s!"{x}: a named " ++ v.description
  | .flag x .. | .flagM x .. => s!"the flag {x}"
  | .done => "no arguments remaining"
  | .orElse p1 p2 => p1.describe ++ " or " ++ (p2 ()).describe
  | .seq p1 p2 => p1.describe ++ " then " ++ (p2 ()).describe
  | .many p => "zero or more " ++ p.describe
  | .remaining => "any arguments"

structure SimpleDesc where
  positional : Array (Name × CanMatch × SigDoc) := {}
  byName : Array (Name × CanMatch × Bool × SigDoc) := {}
  flags : Array (Name × Option Bool × SigDoc) := {}
  keyVals : Option (Name × CanMatch × SigDoc) := none

def toSimpleDesc {m} (p : ArgParse m α) : Option SimpleDesc :=
  go p |>.run {} |>.map (·.snd)
where
  go {α} : ArgParse m α → StateT SimpleDesc Option Unit
  | .fail _ msg? => failure
  | .pure x | .done => Pure.pure ()
  | .lift .. | .orElse .. => failure
  | .positional x v doc? =>
    modify fun sd => { sd with positional := sd.positional.push (x, v.signature, doc?.getD v.description) }
  | .named x v opt doc? =>
    modify fun sd => { sd with byName := sd.byName.push (x, v.signature, opt, doc?.getD v.description)}
  | .anyNamed x v doc?  | .many (.anyNamed x v doc?) => do
    if (← get).keyVals.isNone then
      modify fun sd => { sd with keyVals := some (x, v.signature, doc?.getD v.description) }
    else failure
  | .flag x default doc? => do
    modify fun sd => { sd with flags := sd.flags.push (x, some default, doc?.getD "Flag") }
  | .flagM x _ doc? => do
    modify fun sd => { sd with flags := sd.flags.push (x, none, doc?.getD "Flag") }
  | .seq p1 p2 => do
    go p1
    go (p2 ())
  | .many p => failure
  | .remaining => failure


def SimpleDesc.markdown (d : SimpleDesc) : SigDoc :=
  let {positional, byName, flags, keyVals} := d
  if positional.isEmpty && byName.isEmpty && flags.isEmpty && keyVals.isNone then
    "No parameters"
  else
    posList positional ++ nameList byName ++ flagList flags ++ kv keyVals
where
  posList (pos : Array (Name × CanMatch × SigDoc)) : SigDoc :=
    if pos.isEmpty then ""
    else if let #[(x, t, doc)] := pos then
      doc!"Positional: `" ++ x.toString ++ " : " ++ t.toString ++ " — " ++ doc ++ "`\n\n"
    else
      let args :=
        pos.foldl (init := doc!"Positional:\n") fun s (x, t, doc) =>
          s ++ doc!"* `" ++ .text x.toString ++ " : " ++ t.toString ++ "` — " ++ doc ++ "\n"
      args ++ "\n"
  nameList (ns : Array (Name × CanMatch × Bool × SigDoc)) : SigDoc :=
    if ns.isEmpty then ""
    else if let #[(x, t, opt, doc)] := ns then
      doc!"Named: `" ++ .text x.toString ++ " : " ++ t.toString ++ "` (" ++
      (if opt then "optional" else "required") ++ doc!") — " ++ doc ++ "\n\n"
    else
      let args :=
        ns.foldl (init := doc!"Named:\n") fun s (x, t, opt, doc) =>
          s ++ doc!"* `" ++ x.toString ++ " : " ++ t.toString ++
            "` (" ++ (if opt then "optional" else "required") ++ ") — " ++ doc ++ "\n"
      args ++ "\n"
  flagList (fs : Array (Name × Option Bool × SigDoc)) : SigDoc :=
    if fs.isEmpty then ""
    else
      fs.foldl (init := doc!"Flag" ++ if fs.size = 1 then "" else "s" ++ ":\n") fun s (x, default, doc) =>
        s ++ doc!"* `" ++ x.toString ++ (default.map (s!"` (default `{·}`) - ")).getD "" ++ doc ++ "\n"
  kv : Option (Name × CanMatch × SigDoc) → SigDoc
    | none => ""
    | some (x, t, doc) =>
      doc!"Dictionary: `" ++ x.toString ++ "`, saving names of `" ++ t.toString ++ "` — " ++ doc

def signature' {m} (prec : Nat) (p : ArgParse m α) : Option Std.Format :=
  match p with
  | .fail _ msg? => failure
  | .pure x | .done => do return .nil
  | .lift desc act => do return desc
  | .positional x v _ => do return s!"{x} :" ++ .line ++ (← v.signature.format)
  | .named x v opt _ => do
    let d := v.signature.format
    let s := .group <| .nest 2 <| .text s!"{x} :" ++ .line ++ d
    return withParen 2 <| if opt then "(" ++ s ++ ")?" else s
  | .anyNamed x v _ => do
    let d := v.signature.format
    let s := .group <| .nest 2 <| .text s!"{x} :" ++ .line ++ d ++ .line ++ "(key/value)"
    return withParen 2 s
  | .flag x .. | .flagM x .. => do
    return s!"[+/-]{x}"
  | .orElse p1 p2 => do
    let s1 := p1.signature' 2
    let s2 := (p2 ()).signature' 3
    match s1, s2 with
    | some s1, some s2 =>
      return .group <| s1 ++ " <|>" ++ .line ++ s2
    | some s, none | none, some s => return s
    | none, none => failure
  | .seq p1 p2 => do
    let s1 ← p1.signature' 2
    let s2 ← (p2 ()).signature' 2
    if s1.isEmpty then return s2
    else if s2.isEmpty then return s1
    else return s1 ++ .line ++ s2
  | .many p => do return (← p.signature' 1) ++ "*"
  | .remaining => return "any"
where
  withParen p (x : Std.Format) : Std.Format := if p > prec then "(" ++ x ++ ")" else x

def signature {m} (p : ArgParse m α) : Option SigDoc :=
  if let some sd := toSimpleDesc p then
    some sd.markdown
  else if let some s := p.signature' 0 then
    some <| doc!"```\n" ++ s.pretty 40 ++ doc!"\n```\n"
  else none

scoped instance [Monad m] [MonadError m] : MonadError (StateT σ m) where
  throw e := fun _ => throw e
  tryCatch act handler := fun st => tryCatch (act st) (fun e => handler e st)
  getRef := fun st => (·, st) <$> getRef
  withRef ref act := fun st => withRef ref (act st)
  add stx msg := fun st => (·, st) <$> AddErrorMessageContext.add stx msg


instance : ToMessageData ArgVal where
  toMessageData
    | .name n => toMessageData n.getId
    | .str s => toMessageData s.getString.quote
    | .num n => toMessageData n.getNat

instance : ToMessageData Arg where
  toMessageData
    | .anon v => toMessageData v
    | .named _ x v => m!"({x.getId} := {v})"
    | .flag _ x v => m!"{if v then "+" else "-"}{x.getId}"

structure ParseState where
  remaining : Array Arg
  info : Array (Syntax × Name × SigDoc)

private def firstOriginal (stxs : Array Syntax) : Syntax := Id.run do
  for stx in stxs do
    if stx.getRange? (canonicalOnly := true) |>.isSome then return stx
  return .missing

-- NB the order of ExceptT and StateT is important here
partial def parseArgs : ArgParse m α → ExceptT (Array Arg × Exception) (StateT ParseState m) α
  | .fail stx? msg? => do
    let stx ← stx?.getDM getRef
    let msg := msg?.getD "failed"
    throwThe (Array Arg × Exception) ((← get).remaining, Lean.Exception.error stx msg.toMessageData)
  | .pure x => Pure.pure x
  | .lift desc act => act
  | .positional x vp doc? => do
    let initArgs := (← get).remaining
    if let some (v, args') := getPositional initArgs then
      let val? : Except (Array Arg × Exception) α ← liftM <|
        try
          Except.ok <$> withRef v.syntax (vp.get v)
        catch exn =>
          match exn with
          | Lean.Exception.error ref msg =>
            let msg' := m!"In positional argument '{x}':{indentD msg}"
            Pure.pure <| Except.error (initArgs, Exception.error ref msg')
          | _ => Pure.pure <| Except.error (initArgs, exn)
      match val? with
      | .ok val =>
        modify fun s => {s with remaining := args'}
        if let some d := doc? then
          modify fun s => {s with info := s.info.push (v.syntax, x, d)}
        else
          modify fun s => {s with info := s.info.push (v.syntax, x, vp.description)}
        Pure.pure val
      | .error e => throwThe (Array Arg × Exception) e
    else throwThe (Array Arg × Exception) ((← get).remaining, .error (← getRef) m!"Positional argument '{x}' ({vp.description}) not found")
  | .named x vp optional doc? => do
    let initArgs := (← get).remaining
    if let some (stx, n, v, args') := getNamed initArgs x then
      let val? : Except (Array Arg × Exception) _ ← liftM <|
        try
          Except.ok <$> withRef v.syntax (vp.get v)
        catch exn => Pure.pure <| Except.error (initArgs, exn)
      -- This is needed to apply hovers correctly when a macro expands a positional argument into a named one
      let pos := firstOriginal #[stx, n, v.syntax]
      match val? with
      | .ok val =>
        modify fun s => {s with remaining := args'}
        if let some d := doc? then
          modify fun s => {s with info := s.info.push (pos, x, d)}
        else
          modify fun s => {s with info := s.info.push (pos, x, vp.description)}
        Pure.pure <| match optional with
          | true => some val
          | false => val
      | .error e => throwThe (Array Arg × Exception) e
    else match optional with
      | true => Pure.pure none
      | false => throwThe (Array Arg × Exception) ((← get).remaining, .error (← getRef) m!"Named argument '{x}' ({vp.description}) not found")
  | .anyNamed x vp doc? => do
    let initArgs := (← get).remaining
    if h : initArgs.size > 0 then
      match initArgs[0] with
      | .anon _ =>
        throwThe (Array Arg × Exception) ((← get).remaining, .error (← getRef) m!"Name-argument pair '{x}' ({vp.description}) expected, got anonymous argument")
      | .flag _ x v =>
        throwThe (Array Arg × Exception) ((← get).remaining, .error (← getRef) m!"Name-argument pair '{x}' ({vp.description}) expected, got flag `{if v then "+" else "-"}{x.getId}`")
      | .named stx y v =>
        let val? : Except (Array Arg × Exception) _ ← liftM <|
          try
            Except.ok <$> withRef v.syntax (vp.get v)
          catch exn => Pure.pure <| Except.error (initArgs, exn)
        match val? with
        | .ok val =>
          if let some d := doc? then
            modify fun s => {s with info := s.info.push (stx, x, d)}
          else
            modify fun s => {s with info := s.info.push (stx, x, vp.description)}
          modify fun s => {s with remaining := initArgs.extract 1 initArgs.size}
          Pure.pure (y, val)
        | .error e => throwThe (Array Arg × Exception) e
    else throwThe (Array Arg × Exception) ((← get).remaining, .error (← getRef) m!"Name-argument pair '{x}' ({vp.description}) not found")
  | .flag x default doc? => do
    let initArgs := (← get).remaining
    if let some (stx, n, v, args') := getFlag initArgs x then
      -- This is needed to apply hovers correctly when a macro expands a positional argument into a named one
      let pos := firstOriginal #[stx, n]
      modify fun s => {s with remaining := args'}
      if let some d := doc? then
        modify fun s => {s with info := s.info.push (pos, x, d)}
      else
        modify fun s => {s with info := s.info.push (pos, x, "Flag")}
      pure v
    else if let some (stx, n, v, args') := getNamed initArgs x then
      let val? : Except (Array Arg × Exception) _ ← liftM <|
        try
          Except.ok <$> withRef v.syntax (do
            match v with
            | .name x =>
              let x' ← realizeGlobalConstNoOverloadWithInfo x
              if x' == ``true then pure true else if x' == ``false then pure false else throwError "Expected Boolean"
            | _ => throwError "Expected Boolean")
        catch exn => Pure.pure <| Except.error (initArgs, exn)
      -- This is needed to apply hovers correctly when a macro expands a positional argument into a named one
      let pos := firstOriginal #[stx, n, v.syntax]
      match val? with
      | .ok val =>
        modify fun s => {s with remaining := args'}
        if let some d := doc? then
          modify fun s => {s with info := s.info.push (pos, x, d)}
        else
          modify fun s => {s with info := s.info.push (pos, x, "Flag")}
        if let some _:= stx.getRange? (canonicalOnly := true) then
          let hint ← MessageData.hint m!"Replace with the updated syntax:" #[s!"{if val then "+" else "-"}{x.toString}"] (ref? := some stx)
          logWarningAt stx m!"Deprecated flag syntax.{hint}"
        Pure.pure val
      | .error e => throwThe (Array Arg × Exception) e
    else
      pure default
  | .flagM x default doc? => do
    let initArgs := (← get).remaining
    if let some (stx, n, v, args') := getFlag initArgs x then
      -- This is needed to apply hovers correctly when a macro expands a positional argument into a named one
      let pos := firstOriginal #[stx, n]
      modify fun s => {s with remaining := args'}
      if let some d := doc? then
        modify fun s => {s with info := s.info.push (pos, x, d)}
      else
        modify fun s => {s with info := s.info.push (pos, x, "Flag")}
      pure v
    else if let some (stx, n, v, args') := getNamed initArgs x then
      let val? : Except (Array Arg × Exception) _ ← liftM <|
        try
          Except.ok <$> withRef v.syntax (do
            match v with
            | .name x =>
              let x' ← realizeGlobalConstNoOverloadWithInfo x
              if x' == ``true then pure true else if x' == ``false then pure false else throwError "Expected Boolean"
            | _ => throwError "Expected Boolean")
        catch exn => Pure.pure <| Except.error (initArgs, exn)
      -- This is needed to apply hovers correctly when a macro expands a positional argument into a named one
      let pos := firstOriginal #[stx, n, v.syntax]
      match val? with
      | .ok val =>
        modify fun s => {s with remaining := args'}
        if let some d := doc? then
          modify fun s => {s with info := s.info.push (pos, x, d)}
        else
          modify fun s => {s with info := s.info.push (pos, x, "Flag")}
        if let some _:= stx.getRange? (canonicalOnly := true) then
          let hint ← MessageData.hint m!"Replace with the updated syntax:" #[s!"{if val then "+" else "-"}{x.toString}"] (ref? := some stx)
          logWarningAt stx m!"Deprecated flag syntax.{hint}"
        Pure.pure val
      | .error e => throwThe (Array Arg × Exception) e
    else
      default
  | .done => do
    let args := (← get).remaining
    if h : args.size > 0 then
      match args[0] with
      | .anon v => throwThe (Array Arg × Exception) (args, .error v.syntax m!"Unexpected argument {v}")
      | .flag stx x v => throwThe (Array Arg × Exception) (args, .error stx m!"Unexpected flag {if v then "+" else "-"}{x.getId}")
      | .named stx x _ => throwThe (Array Arg × Exception) (args, .error stx m!"Unexpected named argument '{x.getId}'")
    else Pure.pure ()
  | .orElse p1 p2 => do
    let s ← get
    tryCatchThe (Array Arg × Exception) p1.parseArgs fun
      | e1@((args1 : Array Arg), _) =>
        tryCatchThe (Array Arg × Exception) (set s *> (p2 ()).parseArgs) fun
          | e2@(args2, _) =>
            if args2.size < args1.size then throwThe (Array Arg × Exception) e1 else throwThe (Array Arg × Exception) e2
  | .seq p1 p2 => Seq.seq p1.parseArgs (fun () => p2 () |>.parseArgs)
  | .many p => do
    if let some x ← tryCatchThe (Array Arg × Exception) (some <$> p.parseArgs) fun _ => pure none then
      let xs ← ArgParse.many p |>.parseArgs
      return (x :: xs)
    else return []
  | .remaining => modifyGet fun s =>
    let r := s.remaining
    (r, {s with remaining := #[]})
where
  getNamed (args : Array Arg) (x : Name) : Option (Syntax × Ident × ArgVal × Array Arg) := Id.run do
    for h : i in [0:args.size] do
      if let .named stx y v := args[i] then
        if y.getId.eraseMacroScopes == x then return some (stx, y, v, args.extract 0 i ++ args.extract (i+1) args.size)
    return none
  getFlag (args : Array Arg) (x : Name) : Option (Syntax × Ident × Bool × Array Arg) := Id.run do
    for h : i in [0:args.size] do
      if let .flag stx y v := args[i] then
        if y.getId.eraseMacroScopes == x then return some (stx, y, v, args.extract 0 i ++ args.extract (i+1) args.size)
    return none
  getPositional (args : Array Arg) : Option (ArgVal × Array Arg) := Id.run do
    for h : i in [0:args.size] do
      if let .anon v := args[i] then
        return some (v, args.extract 0 i ++ args.extract (i+1) args.size)
    return none
end

section
variable {m} [Monad m] [MonadInfoTree m] [MonadResolveName m] [MonadEnv m] [MonadError m] [MonadLiftT CoreM m]

def ValDesc.bool : ValDesc m Bool where
  description := doc!"{true} or {false}"
  signature := .Ident
  get
    | .name b => do
      let b' ← liftM <| realizeGlobalConstNoOverloadWithInfo b
      if b' == ``true then Pure.pure true
      else if b' == ``false then Pure.pure false
      else throwErrorAt b "Expected 'true' or 'false'"
    | other => throwError "Expected Boolean, got {other}"

instance : FromArgVal Bool m where
  fromArgVal := .bool


def ValDesc.string : ValDesc m String where
  description := doc!"a string"
  signature := .String
  get
    | .str s => Pure.pure s.getString
    | other => throwError "Expected string, got {toMessageData other}"

instance : FromArgVal String m where
  fromArgVal := .string

def ValDesc.ident : ValDesc m Ident where
  description := doc!"an identifier"
  signature := .Ident
  get
    | .name x => Pure.pure x
    | other => throwError "Expected identifier, got { toMessageData other}"

instance : FromArgVal Ident m where
  fromArgVal := .ident

/--
Parses a name as an argument value.

The name is returned without macro scopes.
-/
def ValDesc.name : ValDesc m Name where
  description := doc!"a name"
  signature := .Ident
  get
    | .name x => Pure.pure x.getId.eraseMacroScopes
    | other => throwError "Expected identifier, got {other}"

instance : FromArgVal Name m where
  fromArgVal := .name

def ValDesc.resolvedName : ValDesc m Name where
  description := doc!"a resolved name"
  signature := .Ident
  get
    | .name x => realizeGlobalConstNoOverloadWithInfo x
    | other => throwError "Expected identifier, got {other}"

/-- Associates a new description with a parser for better error messages. -/
def ValDesc.as (what : SigDoc) (desc : ValDesc m α) : ValDesc m α :=
  {desc with description := what}

/--
Parses a natural number.
-/
def ValDesc.nat : ValDesc m Nat where
  description := doc!"a name"
  signature := .Num
  get
    | .num n => Pure.pure n.getNat
    | other => throwError "Expected string, got {repr other}"

instance : FromArgVal Nat m where
  fromArgVal := .nat

open Lean.Parser in
/--
Parses a sequence of Verso inline elements from a string literal. Returns a FileMap within which
they can be related to their original source.
-/
def ValDesc.inlinesString [MonadFileMap m] : ValDesc m (FileMap × TSyntaxArray `inline) where
  description := doc!"a string that contains a sequence of inline elements"
  signature := .String
  get
    | .str s => open Lean.Parser in do
      let text ← getFileMap
      let input := s.getString
      let ictxt := mkInputContext input s!"string literal on line {s.raw.getPos?.map ((s!" on line {text.toPosition · |>.line}")) |>.getD ""}"
      let env ← getEnv
      let pmctx : ParserModuleContext := {env, options := {}}
      let p := Verso.Parser.textLine -- TODO use upstreamed once public
      let s' := p.run ictxt pmctx (getTokenTable env) (mkParserState input)
      if s'.allErrors.isEmpty then
        if s'.stxStack.size = 1 then
          match s'.stxStack.back with
          | .node _ _ contents => Pure.pure (FileMap.ofString input, contents.map (⟨·⟩))
          | other => throwError "Unexpected syntax from Verso parser. Expected a node, got {other}"
        else throwError "Unexpected internal stack size from Verso parser. Expected 1, got {s'.stxStack.size}"
      else
        let mut msg := "Failed to parse:"
        for (p, _, e) in s'.allErrors do
          let {line, column} := text.toPosition p
          msg := msg ++ s!"  {line}:{column}: {toString e}\n    {repr <| p.extract input input.rawEndPos}\n"
        throwError msg
    | other => throwError "Expected string, got {repr other}"

def ValDesc.messageSeverity : ValDesc m MessageSeverity where
  description :=
    open MessageSeverity in
    doc!"The expected severity: `{error}`, `{warning}`, or `{information}`"
  signature := .Ident
  get := open MessageSeverity in fun
    | .name b => do
      let b' ← realizeGlobalConstNoOverloadWithInfo b
      if b' == ``error then Pure.pure .error
      else if b' == ``warning then Pure.pure .warning
      else if b' == ``information then Pure.pure .information
      else throwErrorAt b "Expected '{``error}', '{``warning}', or '{``information}'"
    | other => throwError "Expected severity, got {repr other}"

instance : FromArgVal MessageSeverity m where
  fromArgVal := .messageSeverity

open Lean.Elab.Tactic.GuardMsgs in
def ValDesc.whitespaceMode : ValDesc m WhitespaceMode where
  description :=
    open WhitespaceMode in
    doc!"The expected whitespace mode: `{exact}`, `{normalized}`, or `{lax}`"
  signature := .Ident
  get := open WhitespaceMode in fun
    | .name b => do
      let b' ← realizeGlobalConstNoOverloadWithInfo b
      if b' == ``exact then Pure.pure .exact
      else if b' == ``normalized then Pure.pure .normalized
      else if b' == ``lax then Pure.pure .lax
      else throwErrorAt b "Expected '{``exact}', '{``normalized}', or '{``lax}'"
    | other => throwError "Expected whitespace mode, got {repr other}"

/--
A value with the syntax that denotes it in source code.

Used to provide error messages or other feedback at the right location.
-/
structure WithSyntax (α) where
  val : α
  «syntax» : Syntax

/--
Parses a value along with its original syntax, which can be useful for providing error messages or
other feedback at the right location.
-/
def ValDesc.withSyntax (desc : ValDesc m α) : ValDesc m (WithSyntax α) where
  description := desc.description
  signature := desc.signature
  get v := (WithSyntax.mk · v.syntax) <$> desc.get v

instance [FromArgVal α m] : FromArgVal (WithSyntax α) m where
  fromArgVal := .withSyntax FromArgVal.fromArgVal

/--
Parses a string literal.
-/
def ValDesc.strLit [Monad m] [MonadError m] : ValDesc m StrLit where
  description := doc!"a string"
  signature := .String
  get
    | .str s => Pure.pure s
    | other => throwError "Expected string, got {toMessageData other}"

instance : FromArgVal StrLit m where
  fromArgVal := .strLit

/--
Parses a numeric literal.
-/
def ValDesc.numLit [Monad m] [MonadError m] : ValDesc m NumLit where
  description := doc!"a number"
  signature := .String
  get
    | .num n => Pure.pure n
    | other => throwError "Expected number, got {toMessageData other}"

instance : FromArgVal NumLit m where
  fromArgVal := .numLit


variable [MonadLiftT BaseIO m] [MonadLog m] [AddMessageContext m] [MonadOptions m]

def run (p : ArgParse m α) (args : Array Arg) : m α := do
  match ← p.parseArgs _ ⟨args, #[]⟩ with
  | (.ok v, ⟨more, info⟩) =>
    if more.size = 0 then
      for (loc, name, what) in info do
        if loc.getHeadInfo matches (.original ..) then
          Verso.Hover.addCustomHover loc m!"{name}: {what}"
      return v
    else if h : more.size = 1 then
      throwErrorAt more[0].syntax "Unexpected argument {more[0]}"
    else
      let errs := MessageData.joinSep (more.map (toMessageData ·) |>.toList) ("," ++ Std.Format.line)
      throwError "Unexpected arguments: {.group <| indentD errs}"
  | (.error e, st) =>
    throw e.snd

def parse [FromArgs α m] (args : Array Arg) : m α := do
  ArgParse.run fromArgs args

def parseThe (α) [FromArgs α m] (args : Array Arg) : m α := do
  ArgParse.run fromArgs args

/--
Documentation for bar, convert into a unit test it is only here for debugging
-/
structure Bar where
  /-- Field3 -/
  field3 : Nat
  /-- Field4 -/
  field4 : String


/--
Documentation for foo, convert into a unit test it is only here for debugging
-/
structure Foo extends Bar where
  /-- Field1 -/
  field1 : Nat
  /-- Field2 -/
  field2 : String
