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
public meta import Tests.Arbitrary

open Lean
open Plausible Gen Arbitrary
open Verso Multi
open Shrinkable
open Std

meta section

def isEqOk [BEq α] (actual : Except ε α) (expected : α) : Bool :=
  match actual with
  | .ok v => v == expected
  | _ => false

def roundTripOk [ToJson α] [FromJson α] [BEq α] [Repr α] (x : α) : Bool :=
  let json := toJson x
  isEqOk (fromJson? json) x

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

instance instShrinkableHashSet : Shrinkable (HashSet String) where
  shrink xs :=
    shrink xs.toArray |>.map fun s => .ofArray s

instance instShrinkableJsSourceMap : Shrinkable JsSourceMap where
  shrink f :=
    (shrink f.filename |>.map ({ f with filename := · })) ++
    (shrink f.contents |>.map ({ f with contents := · }))

instance : Shrinkable JS where
  shrink f := shrink f.js |>.map JS.mk

instance : Shrinkable CSS where
  shrink f := shrink f.css |>.map CSS.mk

instance : Shrinkable JsFile where
  shrink f :=
    (shrink f.filename |>.map ({ f with filename := · })) ++
    (shrink f.contents |>.map ({ f with contents := · })) ++
    (shrink f.defer |>.map ({ f with defer := · })) ++
    (shrink f.after |>.map ({ f with after := · })) ++
    (shrink f.sourceMap? |>.map ({ f with sourceMap? := · }))

instance : Shrinkable CssFile where
  shrink f :=
    (shrink f.filename |>.map ({ f with filename := · }))

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

instance : Arbitrary JS where
  arbitrary := JS.mk <$> arbitrary

instance : Arbitrary CSS where
  arbitrary := CSS.mk <$> arbitrary

instance : Arbitrary JsFile where
  arbitrary := do
    return {
      filename := ← arbitrary,
      contents := ← arbitrary,
      sourceMap? := ← arbitrary,
      defer := ← arbitrary,
      after := ← arbitrary
    }

instance : Arbitrary CssFile where
  arbitrary := do
    return {
      filename := ← arbitrary,
      contents := ← arbitrary
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

    let count ← chooseNat
    let mut ids := {}
    for _ in 0...count do
      ids := ids.insert (← arbitrary)

    let extraCss ← arbitrary
    let extraJs ← arbitrary
    let extraJsFiles ← arbitrary
    let extraCssFiles ← arbitrary
    let quickJump ← arbitrary
    let licenseInfo ← arbitrary
    let mut st : TraverseState := {
      tags, externalTags,
      domains,
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

section
open Verso.Output

instance : ArbitraryFueled Html where
  arbitraryFueled := html
where
  html : Nat → Gen Html
    | 0 => text
    | n + 1 =>
      oneOf #[text, tag n, seq n] (by simp)
  text := .text <$> arbitrary <*> arbitrary
  tag n := do
    let name ← arbitrary
    let attrs ← sizedArrayOf do return (← arbitrary, ← arbitrary)
    let content ← (html n).resize (· - 1)
    return .tag name attrs content
  seq n := .seq <$> sizedArrayOf (html n)

partial instance : Shrinkable Html where
  shrink := shrinkHtml
where
  shrinkHtml
    | .text true s =>
      .text false s :: (shrink s |>.map (.text true))
    | .text false s =>
      shrink s |>.map (.text true)
    | .seq xs =>
      have : Shrinkable Html := ⟨shrinkHtml⟩
      shrink xs |>.map (.seq)
    | .tag name attrs content =>
      (shrink name |>.map (.tag · attrs content)) ++
      (shrink attrs |>.map (.tag name · content)) ++
      (shrinkHtml content |>.map (.tag name attrs ·))
end

section
open Verso.Genre.Manual

instance : Arbitrary ByteArray where
  arbitrary := do
    let count ← chooseNat
    let mut arr := ByteArray.emptyWithCapacity count
    for _ in 0...count do
      arr := arr.push (← arbitrary)
    return arr

instance : Shrinkable ByteArray where
  shrink arr :=
    let halves :=
      if arr.size > 1 then
        let i := arr.size / 2
        [arr.extract 0 i, arr.extract i arr.size]
      else []
    let dropped :=
      if arr.size > 1 then [arr.extract 1 arr.size] else []
    let zeroes :=
      if arr.foldl (init := false) (fun ok b => ok || b != 0) then
        [arr.foldl (init := ByteArray.emptyWithCapacity arr.size) (fun xs _ => xs.push 0)]
      else []
    let smaller := arr.foldl (init := ByteArray.emptyWithCapacity arr.size) (fun xs x => xs.push (x / 2))
    let smaller := if smaller == arr then [] else [smaller]
    let smaller' := arr.foldl (init := ByteArray.emptyWithCapacity arr.size) (fun xs x => xs.push (x - 1))
    let smaller' := if smaller' == arr then [] else [smaller']
    ByteArray.emptyWithCapacity 0 :: halves ++ dropped ++ zeroes ++ smaller ++ smaller'

instance : Arbitrary DataFile where
  arbitrary := do return { filename := ← arbitrary, contents := ← arbitrary }

instance : Shrinkable DataFile where
  shrink f :=
    (shrink f.filename |>.map ({ f with filename := · })) ++
    (shrink f.contents |>.map ({ f with contents := · }))

instance : Arbitrary Numbering where
  arbitrary := do
    oneOf #[ .nat <$> arbitrary, .letter <$> arbitrary]

instance : Shrinkable Numbering where
  shrink
    | .nat n => shrink n |>.map .nat
    | .letter c => .nat 0 :: (shrink c |>.map .letter)
end


instance : Arbitrary XrefSource where
  arbitrary :=
    oneOf #[(.localOverride ∘ System.FilePath.mk) <$> arbitrary, .remoteOverride <$> arbitrary, pure .default] (by simp)

instance : Shrinkable XrefSource where
  shrink
    | .localOverride f => .default :: (shrink f |>.map .localOverride)
    | .remoteOverride url => .default :: (shrink url |>.map .remoteOverride)
    | .default => []

instance : Arbitrary Time.Day.Offset where
  arbitrary := do
    let n : Nat ← arbitrary
    return OfNat.ofNat n

instance : Shrinkable Time.Day.Offset where
  shrink n :=
    (if n ≠ 0 then [0] else []) ++
    (if n > 1 then [⟨n.val / 2⟩, n - 1] else []) ++
    (if n < -1 then [⟨n.val / 2⟩, n + 1] else [])

instance : Arbitrary UpdateFrequency where
  arbitrary :=
    frequency (pure .manual) [
      (1, pure .manual),
      (4, .days <$> arbitrary)
    ]

instance : Shrinkable UpdateFrequency where
  shrink
    | .manual => []
    | .days n => .manual :: (shrink n |>.map .days)

instance : Arbitrary Remote where
  arbitrary :=
    return {
      root := ← arbitrary,
      shortName := ← arbitrary,
      longName := ← arbitrary,
      sources := ← arbitrary,
      updateFrequency := ← arbitrary
    }

instance : Shrinkable Remote where
  shrink rem :=
    (shrink rem.root |>.map ({ rem with root := · })) ++
    (shrink rem.shortName |>.map ({ rem with shortName := · })) ++
    (shrink rem.longName |>.map ({ rem with longName := · })) ++
    (shrink rem.sources |>.map ({ rem with sources := · })) ++
    (shrink rem.updateFrequency |>.map ({ rem with updateFrequency := · }))

open scoped Plausible.Decorations in
def testProp
    (p : Prop) (cfg : Configuration := {})
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] :
    IO (TestResult p') :=
  Testable.checkIO p' (cfg := cfg)

def testInternalId := testProp <| ∀ (id : InternalId), roundTripOk id
def testObject := testProp <| ∀ (obj : Object), roundTripOk obj
def testDomain := testProp <| ∀ (dom : Domain), roundTripOk dom
def testRefDomain := testProp <| ∀ (dom : RefDomain), roundTripOk dom
def testRefObject := testProp <| ∀ (obj : RefObject), roundTripOk obj
def testRemoteInfo := testProp <| ∀ (info : RemoteInfo), roundTripOk info
def testAllRemotes := testProp <| ∀ (remotes : AllRemotes), roundTripOk remotes
def testTraverseState := testProp <| ∀ (st : Verso.Genre.Manual.TraverseState), roundTripOk st
def testHtml := testProp <| ∀ (html : Verso.Output.Html), roundTripOk html
def testDataFile := testProp <| ∀ (f : Verso.Genre.Manual.DataFile), roundTripOk f
def testNumbering := testProp <| ∀ (n : Verso.Genre.Manual.Numbering), roundTripOk n
def testXrefSource := testProp <| ∀ (src : XrefSource), isEqOk (XrefSource.fromJson? src.toJson) src
def testRemote := testProp <| ∀ (r : Remote), isEqOk (Remote.fromJson? "" r.toJson) r

def serializationTests : List (Name × (Σ p, IO <| TestResult p)) := [
  (`testInternalId, ⟨_, testInternalId⟩),
  (`testObject, ⟨_, testObject⟩),
  (`testDomain, ⟨_, testDomain⟩),
  (`testRefDomain, ⟨_, testRefDomain⟩),
  (`testRefObject, ⟨_, testRefObject⟩),
  (`testRemoteInfo, ⟨_, testRemoteInfo⟩),
  (`testAllRemotes, ⟨_, testAllRemotes⟩),
  (`testTraverseState, ⟨_, testTraverseState⟩),
  (`testHtml, ⟨_, testHtml⟩),
  (`testDataFile, ⟨_, testDataFile⟩),
  (`testNumbering, ⟨_, testNumbering⟩),
  (`testXrefSource, ⟨_, testXrefSource⟩),
  (`testRemote, ⟨_, testRemote⟩),
]

public def runSerializationTests : IO Nat := do
  let mut failures := 0
  for (name, test) in serializationTests do
    IO.print s!"{name}: "
    let res ← test.2
    IO.println res
    unless res matches .success .. do
      failures := failures + 1
  return failures
