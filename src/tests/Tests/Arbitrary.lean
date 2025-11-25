/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Plausible
public import Plausible.ArbitraryFueled
public meta import Plausible.ArbitraryFueled
import Lean.Data.Json.FromToJson
import all MultiVerso.InternalId
public meta import MultiVerso.NameMap
public meta import MultiVerso
public meta import VersoManual.Html.JsFile
public meta import VersoManual.Html.CssFile
public meta import VersoManual.Html.Features
public meta import VersoManual.LicenseInfo
public meta import VersoSearch.DomainSearch
public meta import Verso.Output.Html
public meta import MultiVerso.Manifest
public meta import VersoManual.Basic
import all VersoManual.Basic
import VersoManual.Html.CssFile

open Lean
open Plausible Gen Arbitrary
open Verso Multi
open Shrinkable
open Std

/-!
This module contains Plausible generators for most of the types that Verso regularly serializes or
deserializes.
-/


public meta section

def sizedArrayOf (gen : Gen α) : Gen (Array α) := do
  let count ← chooseNat
  let mut out := #[]
  for _ in 0...count do
    out := out.push (← gen.resize (· / count))
  return out

instance : Arbitrary InternalId where
  arbitrary := private InternalId.mk <$> arbitrary

instance : Shrinkable InternalId where
  shrink private
    | { id } => Shrinkable.shrink id <&> InternalId.mk


instance : Arbitrary JsonNumber where
  arbitrary := do
    return { mantissa := ← arbitrary, exponent := ← arbitrary }

instance : Shrinkable JsonNumber where
  shrink x :=
    let ms := shrink x.mantissa
    let xs := shrink x.exponent
    ms.map ({ x with mantissa := · }) ++ xs.map ({ x with exponent := · })


instance : ArbitraryFueled Json where
  arbitraryFueled := arb
where
  arb
    | 0 =>
      oneOf #[
        pure .null,
        pure (.bool true),
        pure (.bool false),
        .num <$> arbitrary,
        .str <$> arbitrary
      ]
    | n + 1 => do
      oneOf #[
        pure .null,
        pure (.bool true),
        pure (.bool false),
        .num <$> arbitrary,
        .str <$> arbitrary,
        .arr <$> sizedArrayOf (arb n),
        .obj <$> (Std.TreeMap.Raw.ofArray · _) <$> genObj n
      ] (by simp)
  genObj (fuel : Nat) : Gen (Array (String × Json)) := do
    let count ← Gen.chooseNat
    let mut xs := #[]
    for _ in 0...count do
      xs := xs.push (← arbitrary, (← Gen.resize (· / count) (arb fuel)))
    return xs

partial instance : Shrinkable Json where
  shrink v := (if v matches .null then [] else [.null]) ++ sh v
where
  sh
    | .null => []
    | .bool true => [.bool false]
    | .bool _ => []
    | .num n => .num <$> shrink n
    | .str s => .str <$> shrink s
    | .arr xs =>
      have : Shrinkable Json := ⟨sh⟩
      .arr <$> shrink xs
    | .obj v =>
      have : Shrinkable Json := ⟨sh⟩
      let xs := v.toArray
      let xs' := shrink xs
      xs'.map fun v => .obj (Std.TreeMap.Raw.ofArray v _)

local instance : Arbitrary (Std.HashSet InternalId) where
  arbitrary := do
    return .ofArray (← Gen.arrayOf arbitrary)

local instance : Shrinkable (Std.HashSet InternalId) where
  shrink v :=
    Std.HashSet.ofArray <$> shrink v.toArray

instance : Arbitrary Object where
  arbitrary := do
    let canonicalName ← arbitrary
    let data ← arbitrary
    let ids ← arbitrary
    return { canonicalName, data, ids}

instance : Shrinkable Object where
  shrink x :=
    (shrink x.canonicalName |>.map ({x with canonicalName := ·})) ++
    (shrink x.data |>.map ({ x with data := · })) ++
    (shrink x.ids |>.map ({ x with ids := · }))


instance : Arbitrary Domain where
  arbitrary := do
    let objects : Std.TreeMap String Object compare ← do
      let mut arr := #[]
      let count ← chooseNat
      for _ in 0...count do
        arr := arr.push (← arbitrary, ← arbitrary)
      pure (.ofArray arr (cmp := compare))
    let objectsById := objects.foldl (init := {}) fun byId x obj =>
      obj.ids.fold (init := byId) fun byId id =>
        byId.alter id fun
          | none => some {x}
          | some xs => some (xs.insert x)
    let title ← arbitrary
    let description ← arbitrary
    return { objects, objectsById, title, description }

instance : Shrinkable (HashSet String) where
  shrink xs :=
    shrink xs.toArray |>.map .ofArray

instance : Shrinkable Domain where
  shrink dom :=
    (shrink dom.objects.toArray |>.map ({ dom with objects := .ofArray · })) ++
    (shrink dom.objectsById.toArray |>.map ({ dom with objectsById := .ofArray ·})) ++
    (shrink dom.title |>.map ({ dom with title := · })) ++
    (shrink dom.description |>.map ({ dom with description := · }))

@[expose]
def Letter := Char
deriving BEq, ToString, Repr, Ord, Hashable

def letters : Vector Char 26 := "abcdefghijklmnopqrstuvwxyz".toList.toArray.toVector

instance : Arbitrary Letter where
  arbitrary := do
    let ⟨i, ⟨_, h⟩⟩ ← choose Nat 0 25 (by grind)
    return letters[i]'(by grind)

instance instShrinkableLetter : Shrinkable Letter where
  shrink c :=
    if let some i := letters.findFinIdx? (· == c) then
      letters.take i |>.toList
    else []

@[expose]
def LetterString := String
deriving BEq, ToString, Repr, Ord, Hashable

instance : Arbitrary LetterString where
  arbitrary := do
    let len ← chooseNat
    let mut s := ""
    for _ in 0...(len + 1) do
      s := s.push ((← arbitrary) : Letter)
    return s

instance : Shrinkable LetterString where
  shrink s :=
    if let some first := s.startPos.get? then
      let rest := s.drop 1
      [String.singleton first] ++ [rest.copy] ++
      (instShrinkableLetter.shrink first |>.map (String.singleton · ++ rest))
    else []

def slugChars := Slug.validChars.toArray

def slugChar : Gen Char := do
  have : slugChars.size > 0 := by decide +native
  let ⟨i, ⟨_, h⟩⟩ ← choose Nat 0 (slugChars.size - 1) (by simp)
  return slugChars[i]'(by grind)

def slugString : Gen String := do
  let len ← chooseNat
  let mut s := ""
  for _ in 0...(len + 1) do
    s := s.push (← slugChar)
  return s

instance : Arbitrary Slug where
  arbitrary := do
    let s : String ← slugString
    return s.sluggify

instance : Shrinkable Slug where
  shrink x :=
    shrink x.toString |>.map (·.sluggify)

instance : Arbitrary RemoteLink where
  arbitrary := do
    let path ← arbitrary
    let htmlId ← arbitrary
    let root ← arbitrary
    return { path, htmlId, root}

instance : Shrinkable RemoteLink where
  shrink x :=
    (shrink x.path |>.map ({ x with path := · })) ++
    (shrink x.htmlId |>.map ({ x with htmlId := · })) ++
    (shrink x.root |>.map ({ x with root := · }))


instance : Arbitrary RefObject where
  arbitrary := do
    let link ← arbitrary
    let data ← arbitrary
    return { link, data }

instance : Shrinkable RefObject where
  shrink x :=
    (shrink x.link |>.map ({ x with link := · })) ++
    (shrink x.data |>.map ({ x with data := · }))

instance : Arbitrary RefDomain where
  arbitrary := do
    let title ← arbitrary
    let description ← arbitrary
    let mut contents := {}
    let count ← chooseNat
    for _ in 0...count do
      contents := contents.insert (← arbitrary) (← Gen.resize (· / count) arbitrary)
    return { title, description, contents }

instance [Shrinkable α] [Shrinkable β] [BEq α] [Hashable α] : Shrinkable (Std.HashMap α β) where
  shrink xs :=
    shrink xs.toArray |>.map (Std.HashMap.insertMany {} ·)

instance [Shrinkable α] [BEq α] [Hashable α] : Shrinkable (Std.HashSet α) where
  shrink xs :=
    shrink xs.toArray |>.map Std.HashSet.ofArray


instance : Shrinkable RefDomain where
  shrink x :=
    (shrink x.title |>.map ({ x with title := ·})) ++
    (shrink x.description |>.map ({ x with description := ·})) ++
    (shrink x.contents |>.map ({ x with contents := ·}))

/-- Generates non-anonymous names that users could write -/
instance : Arbitrary Name where
  arbitrary := do
    let size ← frequency (pure 0) [(5, pure 0), (1, chooseNat)]
    let mut x : Name := .str .anonymous (← arbitrary)
    for _ in 0...size do
      x := .str x (← arbitrary)
    return x

def chars : Vector Char 74 :=
  "abcdefghijklmnopqrstuvwzyzæøå.ABCDEFGHIJKLMNOPQRSTUVWXYZÆØÅλ𝒫() `_+×⊕·⟨⟩[]".toList.toArray.toVector

private def nameComponent : Gen String := do
    let mut s := ""
    for _ in 0...(← chooseNat) do
      s := s.push (← ch)
    return s
where
  ch : Gen Char := do
    let ⟨i, ⟨_, h⟩⟩ ← choose Nat 0 (chars.size - 1) (by grind)
    return chars[i]

instance : Arbitrary NameMap.PublicName where
  arbitrary := private do
    let size ← frequency (pure 0) [(5, pure 0), (1, chooseNat)]
    let mut x : NameMap.PublicName := .ofName <| .str .anonymous (← arbitrary)
    for _ in 0...size do
      x := ⟨.str x.toName (← nameComponent), by grind⟩
    return x


instance : Shrinkable NameMap.PublicName where
  shrink
    | ⟨.str .anonymous x, _⟩ =>
      shrink x |>.map (.ofName <| .str .anonymous ·)
    | ⟨.str y@(.str _ _) x, _⟩ =>
      .ofName y ::
      (shrink x |>.map (.ofName <| .str y ·))
    | ⟨.num _ _, _⟩ | ⟨.anonymous, _⟩ | ⟨.str (.num _ _) _, _⟩ =>
      False.elim <| by grind

instance [Arbitrary α] : Arbitrary (Verso.NameMap α) where
  arbitrary := do
    let mut domains : Verso.NameMap α := {}
    let count ← chooseNat
    for _ in 0...count do
      let (⟨x, ok⟩ : NameMap.PublicName) ← arbitrary
      domains := domains.insert x (← Gen.resize (· / count) arbitrary) ok
    return domains

open Shrinkable in
instance [Shrinkable α] : Shrinkable (Verso.NameMap α) where
  shrink v :=
    shrink v.toArray |>.map fun v => .ofArray v _

instance : Arbitrary RemoteInfo where
  arbitrary := do
    let root ← arbitrary
    let shortName ← arbitrary
    let longName ← arbitrary
    let domains ← arbitrary
    return { root, shortName, longName, domains }

instance : Shrinkable Name where
  shrink
    | .anonymous => []
    | .num x y => [x] ++ (shrink y).map (.num x)
    | .str x y => [x] ++ (shrink y).map (.str x)

instance : Shrinkable RemoteInfo where
  shrink v :=
    (shrink v.root |>.map ({ v with root := · })) ++
    (shrink v.shortName |>.map ({ v with shortName := · })) ++
    (shrink v.longName |>.map ({ v with longName := · })) ++
    (shrink v.domains |>.map ({ v with domains := · }))

instance : Arbitrary AllRemotes where
  arbitrary := do
    let mut xs := {}
    let count ← chooseNat
    for _ in 0...count do
      xs := xs.insert (← arbitrary) (← Gen.resize (· / count) arbitrary)
    return ⟨xs⟩

instance : Shrinkable AllRemotes where
  shrink x :=
    shrink x.allRemotes |>.map AllRemotes.mk

private def pathChars : Vector Char 55 :=
  "abcdefghijklmnopqrstuvwzyzABCDEFGHIJKLMNOPQRSTUVWXYZ-._".toList.toArray.toVector

private def pathComp : Gen String := do
  let mut s := ""
  for _ in 0...(← chooseNat) do
    s := s.push (← ch)
  return s
where
  ch : Gen Char := do
    let ⟨i, ⟨_, h⟩⟩ ← choose Nat 0 (pathChars.size - 1) (by grind)
    return pathChars[i]'(Nat.lt_succ_of_le h)

instance : Arbitrary System.FilePath where
  arbitrary := private do
    let components ← arrayOf pathComp
    let isRoot ← chooseAny Bool
    let init : System.FilePath := if isRoot then "/" else ""
    return components.foldl (α := String) (init := init) fun x y => x / y

instance : Shrinkable System.FilePath where
  shrink path :=
    if let some parent := path.parent then
      parent :: (path.fileName.toList.flatMap shrink |>.map path.withFileName)
    else []
