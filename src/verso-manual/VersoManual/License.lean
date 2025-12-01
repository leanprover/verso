/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
import Verso.Doc.ArgParse
public import Verso.Doc.Elab.Monad
meta import Verso.Doc.Elab.Monad
public import VersoManual.Basic

import VersoManual.LicenseInfo
import VersoManual.LicenseInfo.Licenses
import VersoManual.Basic



open Lean (ToJson FromJson)

open Verso ArgParse Doc Elab

namespace Verso.Genre.Manual

open Verso.Output Html

private def paragraphed (text : String) : Array String := Id.run do
  let lines := text.splitOn "\n"
  let mut paras := #[]
  let mut thisPara := #[]
  for l in lines do
    if l.all Char.isWhitespace then
      if !thisPara.isEmpty then
        paras := paras.push (" ".intercalate thisPara.toList)
        thisPara := #[]
    else
      thisPara := thisPara.push l
  if !thisPara.isEmpty then
    paras := paras.push (" ".intercalate thisPara.toList)

  paras

/-- info: #["One paragraph with lines", "and another", "and more more"] -/
#guard_msgs in
#eval paragraphed r#"

One paragraph
with lines

and another

and more
more

"#

private def paragraphedHtml (text : String) : Html :=
  paragraphed text |>.map (fun (s : String) => {{<p>{{s}}</p>}})

def LicenseInfo.toHtml (license : LicenseInfo) (headerLevel : Nat) : Html :=
  let {identifier, dependency, howUsed, link, text} := license
  {{<section class="license-info">
      {{.tag s!"h{headerLevel}" #[] dependency }}
      {{link.map (fun url => {{<a class="link" href={{url}}>{{url}}</a>}}) |>.getD .empty}}
      {{howUsed.map paragraphedHtml |>.getD .empty}}
      <code class="spdx">{{identifier}}</code>
      {{text.map textHtml}}
    </section>}}
where
  textHtml
    | (hdr?, txt) =>
      let hdrHtml :=
        if let some hdr := hdr? then
          Html.tag s!"h{headerLevel+1}" #[] hdr
        else
          .empty
      {{<section>{{hdrHtml}}{{paragraphedHtml txt}}</section>}}

public section

block_extension Block.licenseInfo where
  traverse _ _ _ := do
    pure none
  toTeX := some <| fun _ _ _ _ _ => pure .empty
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ _ _ => do
      let headerLevel := (← read).traverseContext.headers.size + 1
      let allLicenses := (← read).traverseState.licenseInfo.toArray
      let allLicenses := allLicenses.qsort (·.dependency.trimAscii.copy.toLower < ·.dependency.trimAscii.copy.toLower)

      return allLicenses.map (·.toHtml headerLevel)

/--
Displays the open-source licenses of components used to build the document.
-/
@[block_command]
public meta def licenseInfo : BlockCommandOf Unit
  | () => ``(Block.other Block.licenseInfo #[])
