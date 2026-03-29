module
import Lean.Data.NameMap.Basic
open Lean

namespace Verso.Genre.Blog

-- The assumption here is that suffixes are _mostly_ unique, so the arrays will likely be very
-- small.
public structure NameSuffixMap (α : Type) : Type where
  private contents : Lean.NameMap (Array (Name × α)) := {}

public def NameSuffixMap.empty : NameSuffixMap α := {}

public instance : EmptyCollection (NameSuffixMap α) := ⟨NameSuffixMap.empty⟩

public instance : Inhabited (NameSuffixMap α) := ⟨{}⟩

public def NameSuffixMap.insert (map : NameSuffixMap α) (key : Name) (val : α) : NameSuffixMap α := Id.run do
  let some last := key.components.getLast?
    | map
  let mut arr := map.contents.find? last |>.getD #[]
  for h : i in [0:arr.size] do
    have : i < arr.size := by get_elem_tactic
    if arr[i].fst == key then
      return {map with contents := map.contents.insert last (arr.set i (key, val))}
  return {map with contents := map.contents.insert last (arr.push (key, val))}

public def NameSuffixMap.toArray (map : NameSuffixMap α) : Array (Name × α) := Id.run do
  let mut arr := #[]
  for (_, arr') in map.contents.toList do
    arr := arr ++ arr'
  arr.qsort (fun x y => x.fst.toString < y.fst.toString)

public def NameSuffixMap.toList (map : NameSuffixMap α) : List (Name × α) := map.toArray.toList

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
