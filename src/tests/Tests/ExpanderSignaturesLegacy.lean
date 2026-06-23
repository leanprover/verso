/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Verso
import VersoManual

namespace Verso.ExpanderSignatureTest.Legacy
set_option guard_msgs.diff true

open Lean Elab Command
open Verso Doc Elab ArgParse

/-!
The non-`module` counterpart of `Tests/ExpanderSignatures.lean`. The expanders are defined in a
legacy source file, so the parsers are ordinary (non-`meta`) definitions and the generated
signature constants are not marked `meta`. The signatures must still be computed correctly, and
loading this file must not crash on the `.many` parser's constant.
-/

structure ManyArgs where
  tag : Name
  attrs : Array (String × String)

def manyAttrs : ArgParse DocElabM (Array (String × String)) := List.toArray <$> .many oneAttr
where
  oneAttr : ArgParse DocElabM (String × String) :=
    (fun (k, v) => (k.getId.toString (escape := false), v)) <$> .anyNamed `attr .string

instance : FromArgs ManyArgs DocElabM where
  fromArgs := ManyArgs.mk <$> .positional `tag .name <*> manyAttrs

@[directive]
def manyDir : DirectiveExpanderOf ManyArgs
  | _, _ => do ``(Verso.Doc.Block.concat #[])

structure SimpleArgs where
  tag : Name
  title : Option String
  loud : Bool

instance : FromArgs SimpleArgs DocElabM where
  fromArgs := SimpleArgs.mk <$> .positional `tag .name <*> .named `title .string true <*> .flag `loud false "Be loud?"

@[directive]
def simpleDir : DirectiveExpanderOf SimpleArgs
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
