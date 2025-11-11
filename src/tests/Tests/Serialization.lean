/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Plausible
import Lean.Data.Json.FromToJson
import MultiVerso.InternalId
import MultiVerso
import VersoManual.Basic

/-!
This module contains Plausible generators for most of the types that Verso regularly serializes or
deserializes.
-/

open Lean
open Plausible Gen Arbitrary
open Verso Multi
open Shrinkable
open Std


def roundTripOk [ToJson α] [FromJson α] [BEq α] [Repr α] (x : α) : Bool :=
  let json := toJson x
  match fromJson? json with
  | .ok y => x == y
  | .error _ => false

deriving instance Arbitrary for JsonNumber

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
        .arr <$> genArr n,
        .obj <$> (Std.TreeMap.Raw.ofArray · _) <$> genObj n
      ] (by simp)
  genArr (fuel : Nat) : Gen (Array Json) := do
    let count ← Gen.chooseNat
    let mut xs := #[]
    for _ in 0...count do
      xs := xs.push (← Gen.resize (· / count) (arb fuel))
    return xs
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

instance : Arbitrary Slug where
  arbitrary := do
    let s : String ← arbitrary
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

instance : Shrinkable RefDomain where
  shrink x :=
    (shrink x.title |>.map ({ x with title := ·})) ++
    (shrink x.description |>.map ({ x with description := ·})) ++
    (shrink x.contents |>.map ({ x with contents := ·}))

/-- Generates non-anonymous names that users could write -/
def arbitraryName : Gen Name := do
  let size ← frequency (pure 0) [(5, pure 0), (1, chooseNat)]
  let mut x : Name := .str .anonymous (← arbitrary)
  for _ in 0...size do
    x := .str x (← arbitrary)
  return x

def chars : List Char := "abcdefghijklmnopqrstuvwzyzæøå.ABCDEFGHIJKLMNOPQRSTUVWXYZÆØÅλ𝒫() `_+×⊕·⟨⟩[]".toList

instance : Arbitrary NameMap.PublicName where
  arbitrary := do
    let size ← frequency (pure 0) [(5, pure 0), (1, chooseNat)]
    let mut x : NameMap.PublicName := .ofName (.str .anonymous (← arbitrary))
    for _ in 0...size do
      x := .ofName (.str x.toName (← component))
    return x
where
  component : Gen String := do
    let mut s := ""
    for _ in 0...(← chooseNat) do
      s := s.push (← ch)
    return s

  ch : Gen Char := do
    let ⟨i, ⟨_, h⟩⟩ ← choose Nat 0 (chars.length - 1) (by grind)
    return chars[i]'(Nat.lt_succ_of_le h)

instance : Shrinkable NameMap.PublicName where
  shrink
    | ⟨.str .anonymous x, _⟩ =>
      shrink x |>.map (.ofName <| .str .anonymous ·)
    | ⟨.str y@(.str _ _) x, _⟩ =>
      ⟨y, by grind [NameMap.isPublic]⟩ ::
      (shrink x |>.map (.ofName <| .str y ·))

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

instance [Shrinkable α] : Shrinkable (Lean.NameMap α) where
  shrink v :=
    shrink v.toArray |>.map fun xvs =>
      xvs.foldl (init := {}) (fun xs (x, v) => xs.insert x v)

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

section
open Verso Genre Manual

instance : Shrinkable Tag where
  shrink
    | .provided xs => shrink xs |>.map .provided
    | _ => []

instance : Shrinkable Link where
  shrink l :=
    (shrink l.path |>.map ({ l with path := · })) ++
    (shrink l.htmlId |>.map ({ l with htmlId := · }))

instance : Shrinkable Domains := inferInstanceAs <| Shrinkable (Verso.NameMap Multi.Domain)

instance : Shrinkable (TreeSet InternalId compare) where
  shrink xs :=
    shrink xs.toArray |>.map fun xs => .ofArray xs

instance : Shrinkable (HashSet String) where
  shrink xs :=
    shrink xs.toArray |>.map fun s => .ofArray s

instance : Shrinkable JsSourceMap where
  shrink f :=
    (shrink f.filename |>.map ({ f with filename := · })) ++
    (shrink f.contents |>.map ({ f with contents := · }))

instance : Shrinkable JsFile where
  shrink f :=
    (shrink f.filename |>.map ({ f with filename := · })) ++
    (shrink f.contents |>.map ({ f with contents := · })) ++
    (shrink f.defer |>.map ({ f with defer := · })) ++
    (shrink f.after |>.map ({ f with after := · })) ++
    (shrink f.sourceMap? |>.map ({ f with sourceMap? := · }))

instance : Shrinkable Search.DomainMapper where
  shrink m :=
    (shrink m.className |>.map ({ m with className := ·})) ++
    (shrink m.displayName |>.map ({ m with displayName := ·})) ++
    (shrink m.dataToSearchables |>.map ({ m with dataToSearchables := ·})) ++
    (shrink m.quickJumpCss |>.map ({ m with quickJumpCss := ·}))

instance : Shrinkable LicenseInfo where
  shrink i :=
    (shrink i.identifier |>.map ({ i with identifier := · })) ++
    (shrink i.dependency |>.map ({ i with dependency := · })) ++
    (shrink i.howUsed |>.map ({ i with howUsed := · })) ++
    (shrink i.link |>.map ({ i with link := · })) ++
    (shrink i.text |>.map ({ i with text := · }))

instance : Shrinkable (HashSet LicenseInfo) where
  shrink xs :=
    shrink xs.toArray |>.map (.ofArray ·)

instance : Shrinkable TraverseState where
  shrink st :=
    (shrink st.tags.toArray |>.map ({ st with tags := ({} : HashMap _ _).insertMany ·})) ++
    (shrink st.externalTags.toArray |>.map ({ st with externalTags := ({} : HashMap _ _).insertMany ·})) ++
    (shrink st.domains |>.map ({ st with domains := ·})) ++
    (shrink st.remoteContent |>.map ({ st with remoteContent := ·})) ++
    (shrink st.ids |>.map ({ st with ids := ·})) ++
    (shrink st.extraCss |>.map ({ st with extraCss := ·})) ++
    (shrink st.extraJs |>.map ({ st with extraJs := ·})) ++
    (shrink st.extraJsFiles |>.map ({ st with extraJsFiles := ·})) ++
    (shrink st.extraCssFiles |>.map ({ st with extraCssFiles := ·})) ++
    (shrink st.quickJump |>.map ({ st with quickJump := ·})) ++
    (shrink st.licenseInfo |>.map ({ st with licenseInfo := ·}))

instance : Arbitrary Tag where
  arbitrary := do
    frequency provided [(1, provided), (1, external), (1, internal)]
where
  provided := do
    return .provided (← arbitrary)

  external := do
    let s : Slug ← arbitrary
    match FromJson.fromJson? (json%{"external":{"name":$s}}) with
    | .ok (e : Tag) => return e
    | .error e => panic! s!"failed to generate external tag from {s.toString.quote}! {e}"; return .provided ""

  internal := do
    let s : String ← arbitrary
    match FromJson.fromJson? (json%{"internal":{"name":$s}}) with
    | .ok (e : Tag) => return e
    | .error e => panic! s!"failed to generate internal tag from {s.quote}! {e}"; return .provided ""

instance : Arbitrary Link where
  arbitrary := do
    return { path := ← arbitrary, htmlId := ← arbitrary}

instance [Arbitrary α] [BEq α] [Hashable α] : Arbitrary (HashSet α) where
  arbitrary := do
    let count ← chooseNat
    let mut v := {}
    for _ in 0...count do
      v := v.insert (← arbitrary.resize (· / count))
    return v

instance : Arbitrary JsSourceMap where
  arbitrary := do
    return {filename := ← arbitrary, contents := ← arbitrary}

instance : Arbitrary JsFile where
  arbitrary := do
    return {
      filename := ← arbitrary,
      contents := ← arbitrary,
      sourceMap? := ← arbitrary,
      defer := ← arbitrary,
      after := ← arbitrary
    }

instance : Arbitrary Search.DomainMapper where
  arbitrary := do
    return {
      displayName := ← arbitrary,
      className := ← arbitrary,
      quickJumpCss := ← arbitrary,
      dataToSearchables := ← arbitrary
    }

instance : Arbitrary Search.DomainMappers where
  arbitrary := do
    let mut out := {}
    let count ← chooseNat
    for _ in 0...count do
      out := out.insert (← arbitrary) (← arbitrary.resize (· / count))
    return out

instance : Arbitrary LicenseInfo where
  arbitrary := do
    return {
      identifier := ← arbitrary,
      dependency := ← arbitrary,
      howUsed := ← arbitrary,
      link := ← arbitrary,
      text := ← arbitrary
    }

instance : Arbitrary TraverseState where
  arbitrary := do
    let count ← chooseNat
    let mut tags := {}
    for _ in 0...count do
      tags := tags.insert (← arbitrary.resize (· / count)) (← arbitrary.resize (· / count))

    let count ← chooseNat
    let mut externalTags := {}
    for _ in 0...count do
      externalTags := externalTags.insert (← arbitrary.resize (· / count)) (← arbitrary.resize (· / count))

    let count ← chooseNat
    let mut domains := {}
    for _ in 0...count do
      let n : NameMap.PublicName ← arbitrary
      domains := domains.insert n.toName (← arbitrary.resize (· / count))

    let remoteContent <- arbitrary

    let count ← chooseNat
    let mut ids := {}
    for _ in 0...count do
      ids := ids.insert (← arbitrary)

    let extraCss <- arbitrary
    let extraJs <- arbitrary
    let extraJsFiles <- arbitrary
    let extraCssFiles <- arbitrary
    let quickJump <- arbitrary
    let licenseInfo <- arbitrary
    let mut st := {
      tags, externalTags,
      domains,
      remoteContent,
      ids,
      extraCss, extraJs, extraJsFiles, extraCssFiles,
      quickJump,
      licenseInfo
    }
    -- add content
    let count ← chooseNat
    for _ in 0...count do
      let x : NameMap.PublicName ← arbitrary
      let val : Json ← arbitrary.resize (· / count)
      st := st.set x.toName val
    return st

end

def testInternalId := Testable.checkIO (NamedBinder "id" <| ∀ (id : InternalId), roundTripOk id)
def testObject := Testable.checkIO (NamedBinder "obj" <| ∀ (id : Object), roundTripOk id)
def testDomain := Testable.checkIO (NamedBinder "obj" <| ∀ (id : Domain), roundTripOk id)
def testRefDomain := Testable.checkIO (NamedBinder "obj" <| ∀ (id : RefDomain), roundTripOk id)
def testRefObject := Testable.checkIO (NamedBinder "obj" <| ∀ (id : RefObject), roundTripOk id)
def testRemoteInfo := Testable.checkIO (NamedBinder "obj" <| ∀ (id : RemoteInfo), roundTripOk id)
def testAllRemotes := Testable.checkIO (NamedBinder "obj" <| ∀ (id : AllRemotes), roundTripOk id)
def testTraverseState := Testable.checkIO (NamedBinder "obj" <| ∀ (id : Verso.Genre.Manual.TraverseState), roundTripOk id)

def serializationTests : List (Name × (Σ p, IO <| TestResult p)) := [
  (`testInternalId, ⟨_, testInternalId⟩),
  (`testObject, ⟨_, testObject⟩),
  (`testDomain, ⟨_, testDomain⟩),
  (`testRefDomain, ⟨_, testRefDomain⟩),
  (`testRefObject, ⟨_, testRefObject⟩),
  (`testRemoteInfo, ⟨_, testRemoteInfo⟩),
  (`testAllRemotes, ⟨_, testAllRemotes⟩),
  (`testTraverseState, ⟨_, testTraverseState⟩),
]

def runSerializationTests : IO Nat := do
  let mut failures := 0
  for (name, test) in serializationTests do
    IO.print s!"{name}: "
    let res ← test.2
    IO.println res
    unless res matches .success .. do
      failures := failures + 1
  return failures
