module
import Lean.Data.NameMap.Basic

set_option linter.missingDocs true
set_option doc.verso true

open Lean

/-!
# Name Suffix Maps

A map keyed by {lean}`Name` that supports lookup by suffix. When a key is inserted, only the last
component of the name is used as the index, so looking up a suffix like {lit}`foo` can match
{lit}`A.B.foo`. Among matches, longer suffix overlap is preferred, and ties are returned together,
sorted lexicographically.
-/

namespace Verso.Genre.Blog

/--
A map from {name}`Name` to {name}`α` that supports suffix-based lookup.

Internally, entries are indexed by the last component of their key. Because name suffixes are
mostly unique, the per-bucket arrays are expected to be very small.
-/
public structure NameSuffixMap (α : Type) : Type where
  private contents : Lean.NameMap (Array (Name × α)) := {}

/-- The empty {name}`NameSuffixMap`. -/
public def NameSuffixMap.empty : NameSuffixMap α := {}

/--
The empty {name}`NameSuffixMap` can written “{lean (type := "NameSuffixMap α")}`∅`”.
-/
public instance : EmptyCollection (NameSuffixMap α) := ⟨NameSuffixMap.empty⟩

public instance : Inhabited (NameSuffixMap α) := ⟨{}⟩

/-- Inserts a key-value pair, replacing any existing entry with the same key. -/
public def NameSuffixMap.insert (map : NameSuffixMap α) (key : Name) (val : α) : NameSuffixMap α := Id.run do
  let some last := key.components.getLast?
    | map
  let mut arr := map.contents.find? last |>.getD #[]
  for h : i in [0:arr.size] do
    have : i < arr.size := by get_elem_tactic
    if arr[i].fst == key then
      return { map with contents := map.contents.insert last (arr.set i (key, val)) }
  return { map with contents := map.contents.insert last (arr.push (key, val)) }

/-- Returns all entries as an array, sorted by key. -/
public def NameSuffixMap.toArray (map : NameSuffixMap α) : Array (Name × α) := Id.run do
  let mut arr := #[]
  for (_, arr') in map.contents.toList do
    arr := arr ++ arr'
  arr.qsort (fun x y => x.fst.toString < y.fst.toString)

/-- Returns all entries as a list, sorted by key. -/
public def NameSuffixMap.toList (map : NameSuffixMap α) : List (Name × α) := map.toArray.toList

/--
Looks up entries whose key has {name}`key` as a suffix. Among candidates sharing the same last
component, those with the longest matching suffix (as determined by number of components in the
name, not string length) are returned. If multiple entries tie for the longest match, all of them
are returned, sorted lexicographically by key.
-/
public def NameSuffixMap.get (map : NameSuffixMap α) (key : Name) : Array (Name × α) := Id.run do
  let ks := key.componentsRev
  let some k' := ks.head?
    | #[]
  let some candidates := map.contents.find? k'
    | #[]
  let mut result := none
  for (n, c) in candidates do
    match matchLength ks n.componentsRev, result with
    | none, _ => continue
    | some l, none => result := some (l, #[(n, c)])
    | some l, some (l', found) =>
      if l > l' then result := some (l, #[(n, c)])
      else if l == l' then result := some (l', found.push (n, c))
      else continue
  let res := result.map Prod.snd |>.getD #[]
  res.qsort (fun x y => x.fst.toString < y.fst.toString)
where
  matchLength : List Name → List Name → Option Nat
    | [], _ => some 0
    | _ :: _, [] => none
    | x::xs, y::ys =>
      if x == y then
        matchLength xs ys |>.map (· + 1)
      else none

public instance : GetElem (NameSuffixMap α) Name (Array (Name × α)) (fun _ _ => True) where
  getElem map key _ := map.get key
