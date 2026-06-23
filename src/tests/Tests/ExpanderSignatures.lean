/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Verso
public import VersoManual
public meta import Verso
public meta import VersoManual

public section

namespace Verso.ExpanderSignatureTest.Module
set_option guard_msgs.diff true

open Lean Elab Command
open Verso Doc Elab ArgParse

/-!
The argument signature of every role/directive/code block is precomputed into a constant when the
expander is defined. These tests pin down that the signature is computed correctly, and in
particular that defining an expander whose parser is built from `.many`/`partial` combinators does
not crash when the module holding the constant is loaded.

This file defines the expanders in a `module`, so the parsers are `meta`. `Tests/ExpanderSignaturesLegacy.lean`
checks the same thing for a non-`module` source file.
-/

structure ManyArgs where
  tag : Name
  attrs : Array (String × String)

meta def manyAttrs : ArgParse DocElabM (Array (String × String)) := List.toArray <$> .many oneAttr
where
  oneAttr : ArgParse DocElabM (String × String) :=
    (fun (k, v) => (k.getId.toString (escape := false), v)) <$> .anyNamed `attr .string

meta instance : FromArgs ManyArgs DocElabM where
  fromArgs := ManyArgs.mk <$> .positional `tag .name <*> manyAttrs

@[directive]
meta def manyDir : DirectiveExpanderOf ManyArgs
  | _, _ => do ``(Verso.Doc.Block.concat #[])

structure SimpleArgs where
  tag : Name
  title : Option String
  loud : Bool

meta instance : FromArgs SimpleArgs DocElabM where
  fromArgs := SimpleArgs.mk <$> .positional `tag .name <*> .named `title .string true <*> .flag `loud false "Be loud?"

@[directive]
meta def simpleDir : DirectiveExpanderOf SimpleArgs
  | _, _ => do ``(Verso.Doc.Block.concat #[])

/--
info: simpleDir: Positional: `tag : Ident — a name`

Named: `title : String` (optional) — a string

Flag* `loud` (default `false`) - Be loud?
---
info: manyDir: ```
tag :
Ident
attr : String (key/value)*
```
-/
#guard_msgs in
run_cmd do
  let report (label : String) (s : Option SigDoc) : CommandElabM Unit :=
    match s with
    | some sd => do logInfo m!"{label}: {← sd.toString}"
    | none => logInfo m!"{label}: «no signature»"
  report "simpleDir" (sig SimpleArgs)
  report "manyDir" (sig ManyArgs)
