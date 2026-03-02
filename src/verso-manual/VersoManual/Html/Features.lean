/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Data.Json
import Std.Data.HashSet
import Verso.BEq
public import VersoManual.Html.DataFile
public import VersoManual.Html.JsFile
public import VersoManual.Html.CssFile
import Verso.Output.Html.KaTeX
public import VersoManual.LicenseInfo
import VersoManual.LicenseInfo.Licenses

set_option doc.verso true
set_option linter.missingDocs true

namespace Verso.Genre.Manual
open Lean
open Std
open Verso.Output.Html

/--
A built-in feature supported by the HTML backend of the manual genre.
-/
public inductive HtmlFeature where
  /--
  Rendering mathematics using KaTeX.

  Enabling this feature causes the bundled KaTeX to be included in the emitted HTML and math
  elements to be rendered on page load.
  -/
  | KaTeX
  /--
  The search box.

  Enabling this feature causes the search box JavaScript to be included.
  -/
  | search
deriving ToJson, FromJson, Repr, BEq, DecidableEq, Ord, Hashable

/--
A set of HTML features.
-/
public structure HtmlFeatures where
  private mk ::
  private hasKaTeX : Bool
  private hasSearch : Bool
deriving Repr, Inhabited, BEq


public instance : LawfulBEq HtmlFeature where
  rfl := by
    intro f; cases f <;> rfl
  eq_of_beq := by
    intro f f' hEq
    cases f <;> cases f' <;> first | rfl | contradiction

public instance : LawfulHashable HtmlFeature where
  hash_eq := by
    intro f f' hEq
    cases f <;> cases f' <;> first | rfl | contradiction

namespace HtmlFeatures
/--
No HTML features are enabled.
-/
public def empty : HtmlFeatures := ⟨false, false⟩

public instance : EmptyCollection HtmlFeatures := ⟨.empty⟩

@[simp, grind _=_]
theorem empty_is_empty : empty = {} := by simp [EmptyCollection.emptyCollection]

@[simp, grind =]
private theorem not_empty_hasKaTeX : ({} : HtmlFeatures).hasKaTeX = false := by
  simp [EmptyCollection.emptyCollection, empty]

@[simp, grind =]
private theorem not_empty_hasSearch : ({} : HtmlFeatures).hasSearch = false := by
  simp [EmptyCollection.emptyCollection, empty]

/--
Constructs a singleton set of HTML features.
-/
public def singleton (f : HtmlFeature) : HtmlFeatures :=
  match f with
    | .KaTeX => { hasKaTeX := true, hasSearch := false }
    | .search => { hasKaTeX := false, hasSearch := true }

public instance : Singleton HtmlFeature HtmlFeatures where
  singleton x := singleton x

/--
Adds a feature to the feature set.
-/
public def insert (feature : HtmlFeature) (features : HtmlFeatures) : HtmlFeatures :=
  match feature with
  | .KaTeX => { features with hasKaTeX := true }
  | .search => { features with hasSearch := true }

public instance : Insert HtmlFeature HtmlFeatures where
  insert x xs := insert x xs

@[simp, grind =]
theorem insert_empty_singleton : ({} : HtmlFeatures).insert f = {f} := by
  cases f <;> simp [insert, Singleton.singleton, singleton]

/--
Converts a feature set into an array of features.
-/
public def toArray (features : HtmlFeatures) : Array HtmlFeature :=
  match features with
  | ⟨true, true⟩ => #[.KaTeX, .search]
  | ⟨true, false⟩ => #[.KaTeX]
  | ⟨false, true⟩ => #[.search]
  | ⟨false, false⟩ => #[]

/--
Converts an array of features into a feature set.
-/
public def ofArray (features : Array HtmlFeature) : HtmlFeatures :=
  features.foldl (init := {}) (·.insert ·)

/--
Returns a feature set that contains the features in either set.
-/
public def union (fs fs' : HtmlFeatures) : HtmlFeatures :=
  { hasKaTeX := fs.hasKaTeX || fs'.hasKaTeX, hasSearch := fs.hasSearch || fs'.hasSearch }

public instance : Union HtmlFeatures where
  union := union

/--
Returns a feature set that contains the features in both sets.
-/
public def inter (fs fs' : HtmlFeatures) : HtmlFeatures :=
  { hasKaTeX := fs.hasKaTeX && fs'.hasKaTeX, hasSearch := fs.hasSearch && fs'.hasSearch }

public instance : Inter HtmlFeatures where
  inter := inter

/--
The feature set that includes all HTML features.
-/
public def all : HtmlFeatures := ⟨true, true⟩

/--
Checks whether the feature {name}`f` is enabled in {name}`features`.
-/
public def contains (features : HtmlFeatures) (f : HtmlFeature) : Bool :=
  match f with
  | .KaTeX => features.hasKaTeX
  | .search => features.hasSearch

/--
{name}`f` is a member of {name}`features`.
-/
public def Mem (features : HtmlFeatures) (f : HtmlFeature) : Prop :=
  features.contains f

public instance : Membership HtmlFeature HtmlFeatures where
  mem fs f := Mem fs f

@[grind _=_]
public theorem mem_iff_contains {fs : HtmlFeatures} {f : HtmlFeature} : f ∈ fs ↔ (fs.contains f = true) := by
  let ⟨hasK, hasS⟩ := fs
  cases fs <;> cases f <;> repeat (cases ‹Bool›) <;>
  simp [contains, Membership.mem, Mem]

@[simp, grind .]
public theorem mem_all {f : HtmlFeature} : f ∈ all := by
  cases f <;> simp [all, Membership.mem, Mem, contains]

@[simp, grind =]
public theorem mem_union {f : HtmlFeature} {fs fs' : HtmlFeatures} :
    f ∈ (fs ∪ fs') ↔ (f ∈ fs) ∨ (f ∈ fs') := by
  simp [Union.union, union]
  cases fs <;> cases fs' <;> cases f <;> repeat (cases ‹Bool›) <;>
  simp [contains, Membership.mem, Mem]

@[simp, grind =]
public theorem union_empty {fs : HtmlFeatures} :
    fs ∪ {} = fs := by
  simp [Union.union, union, EmptyCollection.emptyCollection, empty]

@[simp, grind =]
public theorem empty_union {fs : HtmlFeatures} :
    {} ∪ fs = fs := by
  simp [Union.union, union, EmptyCollection.emptyCollection, empty]

@[simp, grind =]
public theorem union_all {fs : HtmlFeatures} :
    fs ∪ all = all := by
  simp [Union.union, union, all]

@[simp, grind =]
public theorem all_union {fs : HtmlFeatures} :
    all ∪ fs = all := by
  simp [Union.union, union, all]

@[simp, grind =]
public theorem mem_inter {f : HtmlFeature} {fs fs' : HtmlFeatures} :
    f ∈ (fs ∩ fs') ↔ (f ∈ fs) ∧ (f ∈ fs') := by
  simp [Inter.inter, inter]
  cases fs <;> cases fs' <;> cases f <;> repeat (cases ‹Bool›) <;>
  simp [contains, Membership.mem, Mem]

@[simp, grind =]
public theorem inter_empty {fs : HtmlFeatures} :
    fs ∩ {} = {} := by
  simp [Inter.inter, inter, EmptyCollection.emptyCollection, empty]

@[simp, grind =]
public theorem empty_inter {fs : HtmlFeatures} :
    {} ∩ fs = {} := by
  simp [Inter.inter, inter, EmptyCollection.emptyCollection, empty]

@[simp, grind =]
public theorem inter_all {fs : HtmlFeatures} :
    fs ∩ all = fs := by
  simp [Inter.inter, inter, all]

@[simp, grind =]
public theorem all_inter {fs : HtmlFeatures} :
    all ∩ fs = fs := by
  simp [Inter.inter, inter, all]

/--
Membership is decidable.
-/
public instance instDecidableMem : Decidable (Mem fs f) :=
  if h : fs.contains f then
    .isTrue <| by simp [Mem, *]
  else .isFalse <| by simp [Mem, *]

@[inherit_doc instDecidableMem]
public instance instDecidableMembership {f : HtmlFeature} {fs : HtmlFeatures} : Decidable (f ∈ fs) :=
  instDecidableMem

@[simp, grind .]
public theorem all_contains_all (f : HtmlFeature) : all.contains f := by
  cases f <;> simp [all, contains]

public instance : ToJson HtmlFeatures where
  toJson fs := private ToJson.toJson fs.toArray

public instance : FromJson HtmlFeatures where
  fromJson? json := private do
    let arr ← FromJson.fromJson? (α := Array HtmlFeature) json
    return .ofArray arr

public instance [Monad m] : ForIn m HtmlFeatures HtmlFeature where
  forIn fs init step := private ForIn.forIn fs.toArray init step

end HtmlFeatures

/--
A collection of HTML assets that can be initialized in the manual configuration and enlarged by
custom elements during traversal.
-/
public structure HtmlAssets where
  /-- Which bundled features should be included? -/
  -- This default value is overridden in Verso.Genre.Manual.HtmlConfig
  features : HtmlFeatures := .empty
  /-- Extra CSS to be included inline into every `<head>` via `<style>` tags -/
  extraCss : HashSet CSS := {}
  /-- Extra JS to be included inline into every `<head>` via `<script>` tags -/
  extraJs : HashSet JS := {}
  /-- Extra JS to be written to the filesystem in the Verso data directory and loaded by each `<head>` -/
  extraJsFiles : HashSet JsFile := {}
  /-- Extra CSS to be written to the filesystem in the Verso data directory and loaded by each `<head>` -/
  extraCssFiles : HashSet CssFile := {}
  /-- Extra files to be placed in the Verso data directory -/
  extraDataFiles : HashSet DataFile := {}
  /-- Open-source licenses, to be collected for display in the final document. -/
  licenseInfo : HashSet LicenseInfo := {}
deriving Repr, Inhabited

/--
Returns all the files that should be written in the {lit}`-verso-data` directory.
-/
public def HtmlAssets.files (assets : HtmlAssets) : Array (String × (String ⊕ ByteArray)) := Id.run do
  let mut out := #[]
  for js in assets.extraJsFiles do
    out := out.push (js.filename, .inl js.contents.js)
    if let some m := js.sourceMap? then
      out := out.push (m.filename, .inl m.contents)
  for css in assets.extraCssFiles do
    out := out.push (css.filename, .inl css.contents.css)
  for data in assets.extraDataFiles do
    out := out.push (data.filename, .inr data.contents)
  return out

/--
Emits the extra CSS, JS, and data files to the specified destination directory, ensuring that it exists.
-/
public def HtmlAssets.writeFiles (assets : HtmlAssets) (destination : System.FilePath) : IO Unit := do
  for (name, content) in assets.files do
    let path := destination / name
    path.parent.forM IO.FS.createDirAll
    match content with
    | .inl string => IO.FS.writeFile path string
    | .inr bytes => IO.FS.writeBinFile path bytes
  assets.features.emitFiles destination

open Verso.BEq in
public instance : BEq HtmlAssets where
  beq := private ptrEqThen fun
    | { features := features1, extraCss := css1, extraJs := js1, extraJsFiles := jsFiles1, extraCssFiles := cssFiles1, extraDataFiles := data1, licenseInfo := license1 },
      { features := features2, extraCss := css2, extraJs := js2, extraJsFiles := jsFiles2, extraCssFiles := cssFiles2, extraDataFiles := data2, licenseInfo := license2 } =>
      features1 == features2 &&
      css1.size == css2.size && css1.all css2.contains &&
      js1.size == js2.size && js1.all js2.contains &&
      jsFiles1.size == jsFiles2.size && jsFiles1.all jsFiles2.contains &&
      cssFiles1.size == cssFiles2.size && cssFiles1.all cssFiles2.contains &&
      data1.size == data2.size && data1.all data2.contains &&
      license1.size == license2.size && license1.all license2.contains

public instance : ToJson HtmlAssets where
  toJson := private fun
    | { features, extraCss, extraJs, extraJsFiles, extraCssFiles, extraDataFiles, licenseInfo } =>
      json%{
        "features": $features,
        "extraCss": $extraCss.toArray,
        "extraJs": $extraJs.toArray,
        "extraJsFiles": $extraJsFiles.toArray,
        "extraCssFiles": $extraCssFiles.toArray,
        "extraDataFiles": $extraDataFiles.toArray,
        "licenseInfo": $licenseInfo.toArray
      }

public instance : FromJson HtmlAssets where
  fromJson? v := private do
    let features ← v.getObjValAs? _ "features"
    let extraCss ← HashSet.ofArray <$> v.getObjValAs? (Array CSS) "extraCss"
    let extraJs ← HashSet.ofArray <$> v.getObjValAs? (Array JS) "extraJs"
    let extraJsFiles ← HashSet.ofArray <$> v.getObjValAs? (Array JsFile) "extraJsFiles"
    let extraCssFiles ← HashSet.ofArray <$> v.getObjValAs? (Array CssFile) "extraCssFiles"
    let extraDataFiles ← HashSet.ofArray <$> v.getObjValAs? (Array DataFile) "extraDataFiles"
    let licenseInfo ← HashSet.ofArray <$> v.getObjValAs? (Array LicenseInfo) "licenseInfo"
    return { features, extraCss, extraJs, extraJsFiles, extraCssFiles, extraDataFiles, licenseInfo }

/--
Combines two sets of HTML assets.

If {name}`moreAssets` contains named file assets whose names conflict with those in {name}`assets`,
then the version in {name}`assets` is used.
-/
public def HtmlAssets.combine (assets moreAssets : HtmlAssets) : HtmlAssets := {
    features := assets.features ∪ moreAssets.features,
    extraCss := assets.extraCss.insertMany moreAssets.extraCss,
    extraJs := assets.extraJs.insertMany moreAssets.extraJs,
    extraJsFiles := moreAssets.extraJsFiles.fold (init := assets.extraJsFiles) fun extraJsFiles jsFile =>
      if extraJsFiles.all (·.filename ≠ jsFile.filename) then extraJsFiles.insert jsFile else extraJsFiles
    extraCssFiles := moreAssets.extraCssFiles.fold (init := assets.extraCssFiles) fun extraCssFiles cssFile =>
      if extraCssFiles.all (·.filename ≠ cssFile.filename) then extraCssFiles.insert cssFile else extraCssFiles
    extraDataFiles := moreAssets.extraDataFiles.fold (init := assets.extraDataFiles) fun extraDataFiles dataFile =>
      if extraDataFiles.all (·.filename ≠ dataFile.filename) then extraDataFiles.insert dataFile else extraDataFiles
    licenseInfo := assets.licenseInfo.insertMany moreAssets.licenseInfo
  }

/--
Returns the license information for a feature.
-/
public def HtmlFeature.licenseInfo : HtmlFeature → Array LicenseInfo
  | .KaTeX => #[Licenses.KaTeX]
  | .search => #[Licenses.fuzzysort, Licenses.w3Combobox, Licenses.elasticlunr.js]

/--
Returns the CSS file paths that should be referenced in page headers for a feature.
-/
public def HtmlFeature.cssFilePaths : HtmlFeature → Array String
  | .KaTeX => #["katex/katex.css"]
  -- This is handled specially due to the need to generate the search index
  | .search => #[]

/--
Returns the JS file paths and whether they should be deferred, for page headers.
-/
public def HtmlFeature.jsFilePaths : HtmlFeature → Array (String × Bool)
  | .KaTeX => #[("katex/katex.js", false), ("katex/math.js", false)]
  -- This is handled specially due to the need to generate the search index
  | .search => #[]

/--
Writes the files for a feature to the destination directory.
-/
public def HtmlFeature.emitFiles : HtmlFeature → System.FilePath → IO Unit
  | .KaTeX, dir => do
    IO.FS.createDirAll (dir / "katex")
    IO.FS.writeFile (dir / "katex" / "katex.css") katex.css
    IO.FS.writeFile (dir / "katex" / "katex.js") katex.js
    IO.FS.writeFile (dir / "katex" / "math.js") math.js
    for (name, contents) in katexFonts do
      let path := dir / name
      path.parent.forM IO.FS.createDirAll
      IO.FS.writeBinFile path contents
  -- This is handled specially due to the need to generate the search index
  | .search, _ => pure ()

/--
Writes the files for all enabled features to the destination directory.
-/
public def HtmlFeatures.emitFiles (features : HtmlFeatures) (dir : System.FilePath) : IO Unit := do
  for f in features do
    f.emitFiles dir

/--
This is a legacy coercion for API compatibility.
-/
public instance : Coe (List String) (HashSet CSS) where
  coe xs := xs.map CSS.mk |> .ofList

/--
This is a legacy coercion for API compatibility.
-/
public instance : Coe (List String) (HashSet JS) where
  coe xs := xs.map JS.mk |> .ofList

/--
This is a legacy coercion for API compatibility.
-/
public instance : Coe (List CSS) (HashSet CSS) where
  coe xs := .ofList xs

/--
This is a legacy coercion for API compatibility.
-/
public instance : Coe (List JS) (HashSet JS) where
  coe xs := .ofList xs

/--
This is a legacy coercion for API compatibility.
-/
public instance : Coe (HashSet String) (HashSet CSS) where
  coe xs := xs.toList.map CSS.mk |> .ofList

/--
This is a legacy coercion for API compatibility.
-/
public instance : Coe (HashSet String) (HashSet JS) where
  coe xs := xs.toList.map JS.mk |> .ofList
