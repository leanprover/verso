/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
import Std.Data.HashSet
import Verso.Method
public import Lean.Data.Json.FromToJson.Basic

public section

set_option linter.missingDocs true

namespace Verso.Multi
open Verso.Method
open Lean (ToJson FromJson)
open Std (HashSet)

private def validCharString := "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789-_"

/-- The characters allowed in slugs. -/
def Slug.validChars :=
  HashSet.ofList [
    'a','b','c','d','e','f','g','h','i','j','k','l','m','n','o','p','q','r','s','t','u','v','w','x','y','z',
    'A','B','C','D','E','F','G','H','I','J','K','L','M','N','O','P','Q','R','S','T','U','V','W','X','Y','Z',
    '0','1','2','3','4','5','6','7','8','9',
    '-','_']

/--
A slug is well-formed if all its characters are valid.
-/
def Slug.wf (str : String) : Bool :=
  str.all (· ∈ validChars)

private def mangle (c : Char) : String :=
  replacements.lookup c |>.getD "___"
where
  replacements : List (Char × String) := [
    ('<', "_LT_"),
    ('>', "_GT_"),
    (';', "_SEMI_"),
    ('‹', "_FLQ_"),
    ('›', "_FRQ_"),
    ('«', "_FLQQ_"),
    ('»', "_FLQQ_"),
    ('⟨', "_LANGLE_"),
    ('⟩', "_RANGLE_"),
    ('(', "_LPAR_"),
    (')', "_RPAR_"),
    ('[', "_LSQ_"),
    (']', "_RSQ_"),
    ('→', "_ARR_"),
    ('↦', "_MAPSTO_"),
    ('⊢', "_VDASH_")
  ]

/--
Converts a string to a valid slug, mangling as appropriate.
-/
def asSlug (str : String) : String :=
  let rec loop (iter : String.Iterator) (acc : String) : String :=
    if iter.atEnd then acc
    else
      let c := iter.curr
      loop iter.next <|
        if c ∈ Slug.validChars then acc.push c
        else if c.isWhitespace then acc.push '-'
        else acc ++ mangle c
  loop str.iter ""

/--
A slug is a well-formed string.
-/
structure Slug where
  private mk ::
  /-- Converts the slug to the underlying string. -/
  toString : String
deriving BEq, Hashable, DecidableEq, Ord, Repr

instance : ToString Slug := ⟨Slug.toString⟩

instance : ToJson Slug where
  toJson s := ToJson.toJson s.toString

instance : FromJson Slug where
  fromJson? v := private do
    let s : String ← FromJson.fromJson? v
    if asSlug s = s then pure ⟨s⟩
    else throw s!"String {s} contains invalid characters"

namespace Slug

instance : LT Slug where
  lt := (·.toString < ·.toString)

instance : DecidableRel (@LT.lt Slug _) := fun s1 s2 =>
  if h : s1.toString < s2.toString then .isTrue h else .isFalse h

instance : LE Slug where
  le s1 s2 := s1 = s2 ∨ s1 < s2

instance : DecidableRel (@LE.le Slug _) := fun s1 s2 =>
  if h : s1 = s2 then .isTrue (.inl h)
  else if h' : s1.toString < s2.toString then .isTrue (.inr h')
  else .isFalse <| by intro nope; cases nope <;> contradiction

defmethod String.sluggify (str : String) : Slug :=
  ⟨asSlug str⟩

/--
Converts a string to a slug.
-/
def ofString (str : String) : Slug := str.sluggify

/--
Returns a slug that's not present in `used`, starting with `slug` and appending consecutive numbers
until it becomes unique.

The consecutive numbers start at `startCount`, which is `1` by default. Callers with reason to
believe that there will be many collisions may provide an alternative starting value.
-/
partial def unique (used : HashSet Slug) (slug : Slug) (startCount : Nat := 1) : Slug :=
  if !(used.contains slug) then slug
  else
    let rec attempt (i : Nat) :=
      let slug' := s!"{slug.toString}{i}".sluggify
      if !(used.contains slug') then slug'
      else attempt (i + 1)
    attempt startCount
