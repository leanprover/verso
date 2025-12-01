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
  private features : HashSet HtmlFeature
deriving Repr

public instance : BEq HtmlFeatures where
  beq xs ys := private
    xs.features.size == ys.features.size &&
    xs.features.all ys.features.contains

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
public def empty : HtmlFeatures := ⟨{}⟩

public instance : EmptyCollection HtmlFeatures := ⟨.empty⟩

public instance : Singleton HtmlFeature HtmlFeatures where
  singleton x := private ⟨singleton x⟩

/--
Adds a feature to the feature set.
-/
public def insert (feature : HtmlFeature) (features : HtmlFeatures) : HtmlFeatures :=
  { features with features := features.features.insert feature }

public instance : Insert HtmlFeature HtmlFeatures where
  insert x xs := insert x xs

/--
Converts a feature set into an array of features.
-/
public def toArray (features : HtmlFeatures) : Array HtmlFeature :=
  features.features.toArray |>.qsortOrd

/--
Converts an array of features into a feature set.
-/
public def ofArray (features : Array HtmlFeature) : HtmlFeatures :=
  ⟨HashSet.ofArray features⟩

/--
The feature set that includes all HTML features.
-/
public def all : HtmlFeatures := {.KaTeX, .search}

/--
Checks whether the feature {name}`f` is enabled in {name}`features`.
-/
public def contains (features : HtmlFeatures) (f : HtmlFeature) : Bool := features.features.contains f

/--
{name}`f` is a member of {name}`features`.
-/
public def Mem (features : HtmlFeatures) (f : HtmlFeature) : Prop := f ∈ features.features

public instance : Membership HtmlFeature HtmlFeatures where
  mem fs f := Mem fs f

public theorem mem_iff_contains {fs : HtmlFeatures} {f : HtmlFeature} : f ∈ fs ↔ fs.contains f = true := by
  unfold contains
  apply HashSet.mem_iff_contains

/--
Membership is decidable.
-/
@[instance]
public def instDecidableMem : Decidable (Mem fs f) :=
  inferInstanceAs <| Decidable <| fs.contains f

/--
Membership is decidable.
-/
@[instance]
public def instDecidableMembership {f : HtmlFeature} {fs : HtmlFeatures} : Decidable (f ∈  fs) :=
  instDecidableMem

@[simp, grind! .]
public theorem all_contains_all (f : HtmlFeature) : all.contains f := by
  cases f <;> simp [all] <;> decide +native

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
  /-- Extra CSS to be included inline into every `<head>` via `<style>` tags -/
  extraCss : HashSet String := {}
  /-- Extra JS to be included inline into every `<head>` via `<script>` tags -/
  extraJs : HashSet String := {}
  /-- Extra JS to be written to the filesystem in the Verso data directory and loaded by each `<head>` -/
  extraJsFiles : HashSet JsFile := {}
  /-- Extra CSS to be written to the filesystem in the Verso data directory and loaded by each `<head>` -/
  extraCssFiles : HashSet CssFile := {}
  /-- Extra files to be placed in the Verso data directory -/
  extraDataFiles : HashSet DataFile := {}
  licenseInfo : HashSet LicenseInfo := {}
deriving Repr

/--
Returns all the files that should be written in the {lit}`-verso-data` directory.
-/
public def HtmlAssets.files (assets : HtmlAssets) : Array (String × (String ⊕ ByteArray)) := Id.run do
  let mut out := #[]
  for js in assets.extraJsFiles do
    out := out.push (js.filename, .inl js.contents)
    if let some m := js.sourceMap? then
      out := out.push (m.filename, .inl m.contents)
  for css in assets.extraCssFiles do
    out := out.push (css.filename, .inl css.contents)
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

open Verso.BEq in
public instance : BEq HtmlAssets where
  beq := private ptrEqThen fun
    | { extraCss := css1, extraJs := js1, extraJsFiles := jsFiles1, extraCssFiles := cssFiles1, extraDataFiles := data1, licenseInfo := license1 },
      { extraCss := css2, extraJs := js2, extraJsFiles := jsFiles2, extraCssFiles := cssFiles2, extraDataFiles := data2, licenseInfo := license2 } =>
      css1.size == css2.size && css1.all css2.contains &&
      js1.size == js2.size && js1.all js2.contains &&
      jsFiles1.size == jsFiles2.size && jsFiles1.all jsFiles2.contains &&
      cssFiles1.size == cssFiles2.size && cssFiles1.all cssFiles2.contains &&
      data1.size == data2.size && data1.all data2.contains &&
      license1.size == license2.size && license1.all license2.contains

public instance : ToJson HtmlAssets where
  toJson := private fun
    | { extraCss, extraJs, extraJsFiles, extraCssFiles, extraDataFiles, licenseInfo } =>
      json%{
        "extraCss": $extraCss.toArray,
        "extraJs": $extraJs.toArray,
        "extraJsFiles": $extraJsFiles.toArray,
        "extraCssFiles": $extraCssFiles.toArray,
        "extraDataFiles": $extraDataFiles.toArray,
        "licenseInfo": $licenseInfo.toArray
      }

public instance : FromJson HtmlAssets where
  fromJson? v := private do
    let extraCss ← HashSet.ofArray <$> v.getObjValAs? (Array String) "extraCss"
    let extraJs ← HashSet.ofArray <$> v.getObjValAs? (Array String) "extraJs"
    let extraJsFiles ← HashSet.ofArray <$> v.getObjValAs? (Array JsFile) "extraJsFiles"
    let extraCssFiles ← HashSet.ofArray <$> v.getObjValAs? (Array CssFile) "extraCssFiles"
    let extraDataFiles ← HashSet.ofArray <$> v.getObjValAs? (Array DataFile) "extraDataFiles"
    let licenseInfo ← HashSet.ofArray <$> v.getObjValAs? (Array LicenseInfo) "licenseInfo"
    return { extraCss, extraJs, extraJsFiles, extraCssFiles, extraDataFiles, licenseInfo }

/--
Adds the HTML assets corresponding to a feature.
-/
public def HtmlFeature.addAssets : HtmlFeature → HtmlAssets → HtmlAssets
  | .KaTeX, st => { st with
      extraCssFiles :=
        st.extraCssFiles
          |>.insert { filename := "katex/katex.css", contents := katex.css },
      extraJsFiles :=
        st.extraJsFiles
          |>.insert {filename := "katex/katex.js", contents := katex.js, sourceMap? := none}
          |>.insert {filename := "katex/math.js", contents := math.js, sourceMap? := none},
      extraDataFiles := st.extraDataFiles.insertMany (katexFonts.map fun f => ⟨f.1, f.2⟩),
      licenseInfo := st.licenseInfo.insert Licenses.KaTeX
    }
  | .search, st => { st with
      licenseInfo := st.licenseInfo.insertMany [Licenses.fuzzysort, Licenses.w3Combobox, Licenses.elasticlunr.js]
    }
