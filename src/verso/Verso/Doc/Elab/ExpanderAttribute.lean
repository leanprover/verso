/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.KeyedDeclsAttribute

namespace Verso.Doc.Elab

open Lean

unsafe def mkDocExpanderAttrUnsafe (attrName typeName : Name) (descr : String) (attrDeclName : Name) : IO (KeyedDeclsAttribute α) :=
  KeyedDeclsAttribute.init {
    name := attrName,
    descr := descr,
    valueTypeName := typeName,
    evalKey := fun _ stx => do
      Elab.realizeGlobalConstNoOverloadWithInfo (← Attribute.Builtin.getIdent stx)
  } attrDeclName


@[implemented_by mkDocExpanderAttrUnsafe]
opaque mkDocExpanderAttributeSafe (attrName typeName : Name) (desc : String) (attrDeclName : Name) : IO (KeyedDeclsAttribute α)

def mkDocExpanderAttribute (attrName typeName : Name) (desc : String) (attrDeclName : Name := by exact decl_name%) : IO (KeyedDeclsAttribute α) := mkDocExpanderAttributeSafe attrName typeName desc attrDeclName

unsafe def mkUncheckedDocExpanderAttrUnsafe (attrName typeName : Name) (descr : String) (attrDeclName : Name) : IO (KeyedDeclsAttribute α) :=
  KeyedDeclsAttribute.init {
    name := attrName,
    descr := descr,
    valueTypeName := typeName,
    evalKey := fun _ stx => do
      return (← Attribute.Builtin.getIdent stx).getId
  } attrDeclName


@[implemented_by mkUncheckedDocExpanderAttrUnsafe]
opaque mkUncheckedDocExpanderAttributeSafe (attrName typeName : Name) (desc : String) (attrDeclName : Name) : IO (KeyedDeclsAttribute α)

def mkUncheckedDocExpanderAttribute (attrName typeName : Name) (desc : String) (attrDeclName : Name := by exact decl_name%) : IO (KeyedDeclsAttribute α) := mkUncheckedDocExpanderAttributeSafe attrName typeName desc attrDeclName
