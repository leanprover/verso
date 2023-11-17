/-
Copyright (c) 2023 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean
import Std.Tactic.GuardMsgs

namespace LeanDoc

namespace Doc


inductive LinkDest where
  | url (address : String)
  | ref (name : String)
deriving Repr

inductive Inline where
  | text (string : String)
  | emph (content : Array Inline)
  | bold (content : Array Inline)
  | code (string : String)
  | linebreak (string : String)
  | link (content : Array Inline) (dest : LinkDest)
  | concat (content : Array Inline)
deriving Repr

inductive ArgVal where
  | name (x : String)
  | str (text : String)
  | num (n : Nat)
deriving Repr

inductive Arg where
  | anon (value : ArgVal)
  | named (name : String) (value : ArgVal)
deriving Repr

structure ListItem (α : Type u) where
  indent : Nat
  contents : Array α
deriving Repr

inductive Block where
  | para (contents : Array Inline)
  | code (name : Option String) (args : Array Arg) (indent : Nat) (content : String)
  | ul (items : Array (ListItem Block))
  | blockquote (items : Array Block)
deriving Repr

inductive Part where
  | mk (title : Array Inline) (titleString : String) (content : Array Block) (subParts : Array Part)
deriving Repr

def Part.title : Part → Array Inline
  | .mk title .. => title
def Part.titleString : Part → String
  | .mk _ titleString .. => titleString
def Part.content : Part → Array Block
  | .mk _ _ content .. => content
def Part.subParts : Part → Array Part
  | .mk _ _ _ subParts => subParts
