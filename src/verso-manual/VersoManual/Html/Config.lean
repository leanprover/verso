/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

module
public import Verso.Output.Html
import Verso.BEq
public import Lean.Data.Json.FromToJson
import VersoUtil.BinFiles.Z85
public import VersoManual.Html.Features
public import VersoManual.Html.JsFile
public import VersoManual.LicenseInfo

namespace Verso.Genre.Manual
open Lean

public structure HtmlConfig extends HtmlAssets where
  htmlDepth := 2
  extraFilesHtml : List (System.FilePath × String) := []
  /-- Extra elements to add to every page's `head` tag -/
  extraHead : Array Output.Html := #[]
  /-- Extra elements to add to every page's contents -/
  extraContents : Array Output.Html := #[]
  /-- The URL from which to draw the logo to show, if any -/
  logo : Option String := none
  /-- The URL that the logo should link to, if any (default is site root) -/
  logoLink : Option String := none
  /-- URL for source link -/
  sourceLink : Option String := none
  /-- URL for issue reports -/
  issueLink : Option String := none
  /--
  How deep should the local table of contents on each non-leaf HTML page?
  `none` means "unlimited".
  -/
  sectionTocDepth : Option Nat := some 1
  /--
  How deep should the local table of contents on the root HTML page?
  `none` means "unlimited".
  -/
  rootTocDepth : Option Nat := some 1
  /--
  Which bundled features should be included?
  -/
  features : HtmlFeatures := .all

public instance : ToJson HtmlConfig where
  toJson := private fun
    | { toHtmlAssets, htmlDepth, extraFilesHtml, extraHead, extraContents, logo, logoLink, sourceLink, issueLink, sectionTocDepth, rootTocDepth, features } =>
      json%{
        "toHtmlAssets": $toHtmlAssets,
        "htmlDepth": $htmlDepth,
        "extraFilesHtml": $extraFilesHtml,
        "extraHead": $extraHead,
        "extraContents": $extraContents,
        "logo": $logo,
        "logoLink": $logoLink,
        "sourceLink": $sourceLink,
        "issueLink": $issueLink,
        "sectionTocDepth": $sectionTocDepth,
        "rootTocDepth": $rootTocDepth,
        "features": $features
      }

public instance : FromJson HtmlConfig where
  fromJson? v := private do
    let toHtmlAssets <- v.getObjValAs? _ "toHtmlAssets"
    let htmlDepth <- v.getObjValAs? _ "htmlDepth"
    let extraFilesHtml <- v.getObjValAs? _ "extraFilesHtml"
    let extraHead <- v.getObjValAs? _ "extraHead"
    let extraContents <- v.getObjValAs? _ "extraContents"
    let logo <- v.getObjValAs? _ "logo"
    let logoLink <- v.getObjValAs? _ "logoLink"
    let sourceLink <- v.getObjValAs? _ "sourceLink"
    let issueLink <- v.getObjValAs? _ "issueLink"
    let sectionTocDepth <- v.getObjValAs? _ "sectionTocDepth"
    let rootTocDepth <- v.getObjValAs? _ "rootTocDepth"
    let features <- v.getObjValAs? _ "features"
    return { toHtmlAssets, htmlDepth, extraFilesHtml, extraHead, extraContents, logo, logoLink, sourceLink, issueLink, sectionTocDepth, rootTocDepth, features }
