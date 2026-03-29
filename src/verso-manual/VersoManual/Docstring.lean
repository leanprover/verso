/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
import Lean.PrettyPrinter.Delaborator.Builtins
import Lean.Elab.Term
import Lean.DocString
import Lean.Widget.TaggedText
import Lean.Meta.Reduce
public import Lean.Data.Options
public import Lean.Environment
public import Lean.CoreM

import Std.Data.HashSet

public import VersoManual.Basic
import VersoManual.HighlightedCode
import VersoManual.Index
import VersoManual.Markdown
public meta import VersoManual.Markdown
public meta import VersoManual.Docstring.Basic
public import VersoManual.Docstring.Basic
public import VersoManual.Docstring.Config
public import VersoManual.Docstring.DeclInfo
public meta import VersoManual.Docstring.DeclInfo
public import VersoManual.Docstring.Show
public meta import VersoManual.Docstring.Show
public import VersoManual.Docstring.DocName
public import VersoManual.Docstring.PrettyPrint
meta import VersoManual.Docstring.PrettyPrint
import VersoManual.Docstring.Progress

import Verso.Instances
import Verso.Code
public import Verso.Code.HighlightedToTex
public meta import Verso.Doc.Elab.Block
public meta import Verso.Doc.Elab.Monad
public import Verso.Doc.ArgParse
import Verso.Doc.DocName
public meta import Verso.Doc.PointOfInterest
import Verso.Doc.PointOfInterest
public import Verso.Doc.Suggestion.Basic

public import MD4Lean

import SubVerso.Highlighting

import MD4Lean


open Lean
open Std (HashSet)

open Verso.Doc.Elab.PartElabM
open Verso.Code
open Verso.ArgParse
open Verso.Code.Highlighted.WebAssets
open Lean.Doc.Syntax

open SubVerso.Highlighting

public section

namespace Verso.ArgParse

open Lean Elab
open Verso.Genre.Manual.Docstring
open Verso.Doc.Suggestion

variable {m} [Monad m] [MonadOptions m] [MonadEnv m] [MonadLiftT CoreM m] [MonadError m] [MonadLog m] [AddMessageContext m] [MonadInfoTree m] [MonadLiftT MetaM m]

meta def ValDesc.documentableName : ValDesc m (Ident × Name) where
  description := "a name with documentation"
  signature := .Ident
  get
    | .name n => do
      let x ← realizeGlobalConstNoOverloadWithInfo n
      if !(← getAllowDeprecated) then
        if Lean.Linter.isDeprecated (← getEnv) x then
          let newName := Lean.Linter.getDeprecatedNewName (← getEnv) x
          let newNameText :=
            match newName with
            | none => m!""
            | some new => m!" Use '{new}' instead."
          newName.forM fun x => saveSuggestion n x.toString x.toString
          Lean.logErrorAt n <|
            .tagged ``Lean.Linter.deprecatedAttr <|
            m!"'{x}' is deprecated.{newNameText}\n\n" ++
            m!"Set option 'verso.docstring.allowDeprecated' to '{true}' to allow documentation for deprecated names."
      else
        -- Defer to default Lean deprecation warnings and settings if it's not a hard error
        Lean.Linter.checkDeprecated x
      pure (n, x)
    | other => throwError "Expected identifier, got {other}"

end Verso.ArgParse


namespace Verso.Genre.Manual.Block

def docstring (name : Name) (declType : Docstring.DeclType) (signature : Signature) (customLabel : Option String) (altNamesToSuggest : Array Name) : Block where
  name := `Verso.Genre.Manual.Block.docstring
  data := ToJson.toJson (name, declType, signature, customLabel, altNamesToSuggest)

def docstringSection (header : String) : Block where
  name := `Verso.Genre.Manual.Block.docstringSection
  data := ToJson.toJson header

def internalSignature (name : Highlighted) (signature : Option Highlighted) : Block where
  name := `Verso.Genre.Manual.Block.internalSignature
  data := ToJson.toJson (name, signature)

open Docstring in
def fieldSignature (visibility : Visibility) (name : Highlighted) (signature : Highlighted) (inheritedFrom : Option Nat) (inheritance : Array Highlighted) : Block where
  name := `Verso.Genre.Manual.Block.fieldSignature
  data := ToJson.toJson (visibility, name, signature, inheritedFrom, inheritance)

def inheritance (within : Name) (inheritance : Array Block.Docstring.ParentInfo) : Block where
  name := `Verso.Genre.Manual.Block.inheritance
  data := ToJson.toJson (within, inheritance)

def constructorSignature (signature : Highlighted) : Block where
  name := `Verso.Genre.Manual.Block.constructorSignature
  data := ToJson.toJson signature

end Block


instance [BEq α] [Hashable α] [FromJson α] : FromJson (HashSet α) where
  fromJson? v := do
    let xs ← v.getArr?
    let vs ← xs.mapM fromJson?
    pure <| HashSet.insertMany {} vs

instance [BEq α] [Hashable α] [ToJson α] : ToJson (HashSet α) where
  toJson v :=
    .arr <| v.toArray.map toJson

def docstringStyle := r#"
.namedocs {
  position: relative;
  border: solid 1px #98B2C0;
  border-radius: .5rem;
  padding-top: var(--verso--box-padding);
  margin-top: var(--verso--box-vertical-margin);
  margin-bottom: var(--verso--box-vertical-margin);
}

.namedocs .text {
  /* Causes margins on child elements to collapse inside the element, such
     that the margins don't extend into parent with the background color.
     The effect is that weird borders in the definition box don't happen anymore. */
  display: flow-root;
  /* Add a padding. this is the same as the margin applied to the first and last child.
     The effect is that the padding looks the same size on all sides. */
  padding: 0 var(--verso--box-padding);
  border-top: 1px solid #98B2C0;
}

.namedocs .text > pre {
  overflow-x: auto;
}

.namedocs .signature {
  font-family: var(--verso-code-font-family);
  margin-top: 0 !important;
  margin-left: var(--verso--box-padding) !important;
  margin-bottom: .75rem !important;
}

.namedocs .label {
  display: block;
  font-size: small;
  font-family: var(--verso-structure-font-family);
  position: absolute;
  top: -0.65rem;
  left: 1rem;
  background: #fff;
  padding: 0 .5rem .125rem;
  border: 1px solid #98B2C0;
  border-radius: 1rem;
  color: #555;
}

.namedocs h1 {
  font-size: inherit;
  font-weight: bold
  margin-top: 1rem;
  margin-bottom: 1rem;
}

.namedocs > .text .constructor {
  padding-top: 0;
  padding-right: 0;
  padding-bottom: 0;
  margin-top: 0.5rem;
  margin-bottom: 1.5rem;
}

.namedocs > .text .constructor::before {
  content: '| ';
  display: block;
  font-family: var(--verso-code-font-family);
  font-weight: bold;
  float: left;
  width: 0.5rem;
  white-space: pre;
}

.namedocs > .text .constructor .name-and-type {
  padding-left: 0.5rem;
  float: left;
  margin-top: 0;
  max-width: calc(100% - 1rem);
}
.namedocs > .text .constructor .docs {
  clear: both;
  padding-left: 1rem;
}

/* These margins work together with the padding on .text */
.namedocs .text > :first-child {
  margin-top: var(--verso--box-padding);
}
.namedocs .text > :last-child {
  margin-bottom: var(--verso--box-padding);
}

.namedocs .methods td, .namedocs .fields td {
  vertical-align: top;
}
.namedocs .inheritance {
  vertical-align: top;
  font-size: smaller;
  font-family: var(--verso-structure-font-family);
}
.namedocs .inheritance ol {
  display: inline-block;
  margin: 0;
  padding: 0;
}
.namedocs .inheritance ol li {
  list-style-type: none;
  display: inline-block;
}
.namedocs .inheritance ol li::after {
  content: " > "
}
.namedocs .inheritance ol li:last-child::after {
  content: "";
}

.namedocs .extends {
  display: inline;
  margin: 0;
  padding: 0;
}

.namedocs .extends li {
  list-style-type: none;
  display: inline-block;
}

.namedocs .extends li label {
  padding-right: 1rem;
}

.namedocs .subdocs .name-and-type {
  font-size: 1rem;
  margin-left: 0;
  margin-top: 0;
  margin-right: 0;
  margin-bottom: 0.5rem;
}

.namedocs .subdocs .docs {
  margin-left: 1.5rem;
  margin-top: 0;
  margin-right: 0;
  margin-bottom: 0.5rem;
}

.namedocs:has(input[data-parent-idx]) [data-inherited-from] {
  transition-property: opacity, display;
  transition-duration: 0.4s;
  transition-behavior: allow-discrete;
  @starting-style { opacity: 0 !important; }
}

#this-page-items .tactic-name { font-weight: bold; }
"# ++ Id.run do
  let mut str := ""
  for i in [0:50] do
    str := str ++ mkFilterRule i
  str
where
  mkFilterRule (i : Nat) : String :=
    ".namedocs:has(input[data-parent-idx=\"" ++ toString i ++ "\"]) [data-inherited-from=\"" ++ toString i ++ "\"] {
  display: none;
  opacity: 0;
}
.namedocs:has(input[data-parent-idx=\"" ++ toString i ++ "\"]:checked) [data-inherited-from=\"" ++ toString i ++"\"] {
  display: block;
  transform: none;
  opacity: 1;
}
.namedocs:has(input[data-parent-idx=\"" ++ toString i ++ "\"]:checked):has(.inheritance[data-inherited-from=\"" ++ toString i ++"\"]:hover) [data-inherited-from]:not([data-inherited-from=\"" ++ toString i ++"\"]) {
  opacity: 0.5;
}
"

@[block_extension Block.docstringSection]
def docstringSection.descr : BlockDescr where
  traverse _ _ _ := pure none
  toTeX := some fun _goI goB _id info contents =>
    open Verso.Output.TeX in do
    let .ok header := FromJson.fromJson? (α := String) info
      | Verso.Doc.TeX.logError "Failed to deserialize docstring section data while generating TeX"; return .empty
    pure \TeX{\par\noindent\textbf{\Lean{header}}\par " " \Lean{.seq (← contents.mapM goB)}}
  toHtml := some fun _goI goB _id info contents =>
    open Verso.Doc.Html HtmlT in
    open Verso.Output Html in do
      let .ok header := FromJson.fromJson? (α := String) info
        | do Verso.Doc.Html.HtmlT.logError "Failed to deserialize docstring section data while generating HTML"; pure .empty
      return {{
        <h1>{{header}}</h1>
        {{← contents.mapM goB}}
      }}

@[block_extension Block.internalSignature]
def internalSignature.descr : BlockDescr where
  traverse _ _ _ := pure none
  toTeX := some fun _goI goB _id info contents =>
    open Verso.Output.TeX in do
    let .ok (name, signature) := FromJson.fromJson? (α := Highlighted × Option Highlighted) info
      | Verso.Doc.TeX.logError "Failed to deserialize docstring section data while generating TeX"; return .empty
    let signatureTeX ← do
      if let some sig := signature then
        pure \TeX{ " : " \Lean{ (← sig.toTeX) } }
      else pure .empty
    pure \TeX{\par " " \Lean{← name.toTeX} \Lean{signatureTeX} \Lean{.seq (← contents.mapM goB)}}
  toHtml := some fun _goI goB _id info contents =>
    open Verso.Doc.Html HtmlT in
    open Verso.Output Html in do
      let .ok (name, signature) := FromJson.fromJson? (α := Highlighted × Option Highlighted) info
        | do Verso.Doc.Html.HtmlT.logError "Failed to deserialize docstring section data while generating HTML"; pure .empty
      return {{
        <section class="subdocs">
          <pre class="name-and-type hl lean">
            {{← name.toHtml (g := Manual)}}
            {{← if let some s := signature then do
                  pure {{" : " {{← s.toHtml (g := Manual)}} }}
                else pure .empty}}
          </pre>
          <div class="docs">
            {{← contents.mapM goB}}
          </div>
        </section>
      }}


@[block_extension Block.inheritance]
def inheritance.descr : BlockDescr where
  traverse _ _ _ := pure none
  toTeX := some fun _goI goB _id info contents =>
    open Verso.Output.TeX in do
    let .ok (name, _parents) := FromJson.fromJson? (α := Name × Array Block.Docstring.ParentInfo) info
      | Verso.Doc.TeX.logError "Failed to deserialize docstring section data while generating TeX"; return .empty
    return \TeX{\Lean{s!"{name}"} \Lean{.seq (← contents.mapM goB)}}
  toHtml := some fun _goI _goB _id info _contents =>
    open Verso.Doc.Html HtmlT in
    open Verso.Output Html in do
      let .ok (name, parents) := FromJson.fromJson? (α := Name × Array Block.Docstring.ParentInfo) info
        | do Verso.Doc.Html.HtmlT.logError "Failed to deserialize docstring structure inheritance data while generating HTML"; pure .empty
      let parentRow ← do
        if parents.isEmpty then pure .empty
        else pure {{
            <ul class="extends">
              {{← parents.mapM fun parent => do
                let filterId := s!"{parent.index}-{parent.name}-{name}"
                pure {{
                  <li>
                    <input type="checkbox" id={{filterId}} data-parent-idx={{toString parent.index}}/>
                    <label for={{filterId}}><code class="hl lean inline">{{← parent.parent.toHtml (g := Manual)}}</code></label>
                  </li>}}
              }}
            </ul>
          }}

open Block.Docstring (Visibility) in
@[block_extension Block.fieldSignature]
def fieldSignature.descr : BlockDescr where
  traverse _ _ _ := pure none
  toTeX := some fun _goI goB _id info contents =>
    open Verso.Output.TeX in do
    let .ok (visibility, name, signature, inheritedFrom, parents) := FromJson.fromJson? (α := Visibility × Highlighted × Highlighted × Option Nat × Array Highlighted) info
      | Verso.Doc.TeX.logError "Failed to deserialize docstring section data while generating TeX"; return .empty
    let visibility : Verso.Output.TeX :=
      match visibility with
      | .public => .empty
      | .private => \TeX{ \textbf{"private"} }
      | .protected => .empty
    let desc := \TeX{ \par " " \Lean{visibility} \Lean{← name.toTeX} " : " \Lean{← signature.toTeX} \par " " \Lean{.seq (← contents.mapM goB)}}
    let parentsTeX := (← parents.toList.mapM (·.toTeX)).intersperse (.raw ", ")
    let inheritedExtra : Output.TeX := match inheritedFrom with
    | .none => ""
    | .some _ => .raw "Inherited from " ++ parentsTeX
    pure (desc ++ inheritedExtra)
  toHtml := some fun _goI goB _id info contents =>
    open Verso.Doc.Html HtmlT in
    open Verso.Output Html in do
      let .ok (visibility, name, signature, inheritedFrom, parents) := FromJson.fromJson? (α := Visibility × Highlighted × Highlighted × Option Nat × Array Highlighted) info
        | do Verso.Doc.Html.HtmlT.logError "Failed to deserialize docstring section data while generating HTML"; pure .empty
      let inheritedAttr : Array (String × String) :=
        inheritedFrom.map (fun i => #[("data-inherited-from", toString i)]) |>.getD #[]
      let visibility : Html :=
        match visibility with
        | .public => .empty
        | .private => {{<span class="keyword">"private"</span>" "}}
        | .protected => .empty
      return {{
        <section class="subdocs" {{inheritedAttr}}>
          <pre class="name-and-type hl lean">
            {{visibility}}{{← name.toHtml (g := Manual)}} " : " {{ ← signature.toHtml (g := Manual)}}
          </pre>
          {{← if inheritedFrom.isSome then do
              pure {{
                <div class="inheritance docs" {{inheritedAttr}}>
                  "Inherited from "
                  <ol>
                  {{ ← parents.mapM fun p => do
                      pure {{<li><code class="hl lean inline">{{ ← p.toHtml (g := Manual) }}</code></li>}}
                  }}
                  </ol>
                </div>}}
            else pure .empty}}
          <div class="docs">
            {{← contents.mapM goB}}
          </div>
        </section>
      }}

@[block_extension Block.constructorSignature]
def constructorSignature.descr : BlockDescr where
  traverse _ _ _ := pure none
  toTeX := some fun _goI goB _id info contents =>
    open Verso.Output.TeX in do
      let .ok signature := FromJson.fromJson? (α := Highlighted) info
        | Verso.Doc.TeX.logError "Failed to deserialize docstring section data while generating TeX"; pure .empty
      let signat ← signature.toTeX
      pure \TeX{ \Lean{.raw "\\begin{list}{$|$}{\\leftmargin=1em\\topsep=0pt \\partopsep=0pt}\\item "}
                 \Lean{signat}
                 \Lean{.raw "\\par " }
                 \Lean{← contents.mapM goB}
                 \Lean{.raw "\\end{list}" } }

  toHtml := some fun _goI goB _id info contents =>
    open Verso.Doc.Html HtmlT in
    open Verso.Output Html in do
      let .ok signature := FromJson.fromJson? (α := Highlighted) info
        | do Verso.Doc.Html.HtmlT.logError "Failed to deserialize docstring section data while generating HTML"; pure .empty

      return {{
        <div class="constructor">
          <pre class="name-and-type hl lean">{{← signature.toHtml (g := Manual)}}</pre>
          <div class="docs">
            {{← contents.mapM goB}}
          </div>
        </div>
      }}


open Verso.Output Html in
def Signature.toHtml : Signature → HighlightHtmlM Manual Html
  | {wide, narrow} => do
    return {{<div class="wide-only">{{← wide.toHtml}}</div><div class="narrow-only">{{← narrow.toHtml}}</div>}}

open Verso.Output TeX in
def Signature.toTeX [Monad m] [Doc.TeX.GenreTeX g m] : Signature → Doc.TeX.TeXT g m TeX
  | { wide, .. } =>
    wide.toTeX

open Verso.Search in
def docDomainMapper : DomainMapper :=
  DomainMapper.withDefaultJs docstringDomain "Documentation" "doc-domain" |>.setFont { family := .code }

open Verso.Search in
def docSuggestionMapper : DomainMapper := {
  displayName := "Suggestion",
  className := "suggestion-domain",
  dataToSearchables := "(domainData) =>
    Object.entries(domainData.contents).map(([key, value]) => ({
      searchKey: value[0].data.searchTerm,
      address: `${value[0].address}#${value[0].id}`,
      domainId: '" ++ suggestionDomain.toString ++ "',
      ref: value[0].data.suggestedRedirect,
    }))",
  customRender := "(searchable, matchedParts, document) => {
    const searchTerm = document.createElement('p');
    for (const { t, v } of matchedParts) {
      if (t === 'text') {
        searchTerm.append(v);
      } else {
        const emEl = document.createElement('em');
        searchTerm.append(emEl);
        emEl.textContent = v;
      }
    }
    searchTerm.append(document.createElement('br'));
    searchTerm.append(`↪ ${searchable.ref}`);
    return searchTerm
  }"
  : DomainMapper
}.setFont { family := .code }

open Verso.Genre.Manual.Markdown in
@[block_extension Block.docstring]
def docstring.descr : BlockDescr := withHighlighting {
  init st := st
    |>.setDomainTitle docstringDomain "Lean constant reference"
    |>.setDomainDescription docstringDomain "Documentation for Lean constants"
    |>.addQuickJumpMapper docstringDomain docDomainMapper
    |>.setDomainTitle suggestionDomain "Lean constant suggestions"
    |>.setDomainDescription suggestionDomain "Search suggestions for Lean constants"
    |>.addQuickJumpMapper suggestionDomain docSuggestionMapper

  traverse id info _ := do
    let .ok (name, declType, _signature, _customLabel, altNames) :=
      FromJson.fromJson? (α := Name × Block.Docstring.DeclType × Signature × Option String × Array Name) info
      | do logError "Failed to deserialize docstring data"; pure none

    match declType with
    | .structure true ctor? fields fieldInfos _parents _ancestors =>
        if let some ctor := ctor? then
          saveRef id ctor.name <| some <| Doc.Inline.concat #[Doc.Inline.text "Instance constructor of ", Doc.Inline.code name.toString]

        for (f, i) in fields.zip fieldInfos do
          saveRef id i.projFn
            (some <| Doc.Inline.concat #[Doc.Inline.code i.projFn.toString, Doc.Inline.text " (class method)"])
            (showName := some f.toString)
    | .structure false ctor? fields fieldInfos _parents _ancestors =>
        if let some ctor := ctor? then
          saveRef id ctor.name <| some <| Doc.Inline.concat #[Doc.Inline.text "Constructor of ", Doc.Inline.code name.toString]

        for (f, i) in fields.zip fieldInfos do
          saveRef id i.projFn
            (some <| Doc.Inline.concat #[Doc.Inline.code i.projFn.toString, Doc.Inline.text " (structure field)"])
            (showName := some f.toString)
    | .inductive ctors _ _ =>
      for c in ctors do
        saveRef id c.name <| some <| Doc.Inline.concat #[Doc.Inline.text "Constructor of ", Doc.Inline.code name.toString]
    | _ => pure ()

    -- Save a backreference
    match (← get).get? `Verso.Genre.Manual.docstring with
    | some (.error e) => logError e
    | some (.ok (v : Json)) =>
      let found : HashSet InternalId := (v.getObjVal? name.toString).bind fromJson? |>.toOption |>.getD {}
      modify (·.set `Verso.Genre.Manual.docstring <|  v.setObjVal! name.toString (toJson (found.insert id)))
    | none =>
      modify (·.set `Verso.Genre.Manual.docstring <| Json.mkObj [] |>.setObjVal! name.toString (toJson [id]))

    -- Save a new-style backreference
    modify fun st => st.saveDomainObject docstringDomain name.toString id
    saveRef id name none
    if name.getPrefix != .anonymous then
      Index.addEntry id {term := Doc.Inline.code name.getString!, subterm := some <| Doc.Inline.code name.toString}

    for altName in altNames do
      modify fun st => st
        |>.saveDomainObject suggestionDomain (altName.toString ++ "↪" ++ name.toString) id
        |>.saveDomainObjectData suggestionDomain (altName.toString ++ "↪" ++ name.toString) (json%{
          "searchTerm": $altName.toString,
          "suggestedRedirect": $name.toString
        })

    pure none
  toHtml := some <| fun _goI goB id info contents =>
    open Verso.Doc.Html HtmlT in
    open Verso.Output Html in do
      let .ok (name, declType, signature, customLabel, _) := FromJson.fromJson? (α := Name × Block.Docstring.DeclType × Signature × Option String × Array Name) info
        | do Verso.Doc.Html.HtmlT.logError "Failed to deserialize docstring data while generating HTML"; pure .empty
      let sig : Html ← signature.toHtml

      let xref ← state
      let idAttr := xref.htmlId id

      let label := customLabel.getD declType.label

      if label == "" then
        Doc.Html.HtmlT.logError s!"Missing label for '{name}': supply one with 'label := \"LABEL\"'"

      return {{
        <div class="namedocs" {{idAttr}}>
          {{permalink id xref false}}
          <span class="label">{{label}}</span>
          <pre class="signature hl lean block">{{sig}}</pre>
          <div class="text">
            {{← contents.mapM goB}}
          </div>
        </div>
      }}

  localContentItem := fun _id info _contents => open Verso.Output.Html in do
    let  (name, _declType, _signature, _customLabel, _altNames) ←
      FromJson.fromJson? (α := Name × Block.Docstring.DeclType × Signature × Option String × Array Name) info
    let names := #[name.getString!, name.toString]
    pure <| names.map fun s => (s, {{<code>{{s}}</code>}})

  toTeX := some <| fun _goI goB _id info contents =>
    open Verso.Output.TeX in do
      let .ok (name, declType, signature, customLabel, _) := FromJson.fromJson? (α := Name × Block.Docstring.DeclType × Signature × Option String × Array Name) info
        | Verso.Doc.TeX.logError "Failed to deserialize docstring data while generating TeX"; return .empty

      let label := customLabel.getD declType.label
      if label == "" then
        Verso.Doc.TeX.logError s!"Missing label for '{name}': supply one with 'label := \"LABEL\"'"
      pure \TeX{\begin{docstringBox}{\Lean{label}} \Lean{← signature.toTeX} \tcblower " " \Lean{← contents.mapM goB} \end{docstringBox}}

  extraCss := [docstringStyle]
}
where
  saveRef
      (id : InternalId) (name : Name)
      (subterm : Option (Doc.Inline Manual))
      (showName : Option String := none) :
      ReaderT TraverseContext (StateT TraverseState IO) Unit := do
    let path ← (·.path) <$> read
    let _ ← Verso.Genre.Manual.externalTag id path name.toString
    Index.addEntry id {
      term := Doc.Inline.code (showName.getD name.toString),
      subterm := subterm
    }
    modify (·.saveDomainObject docstringDomain name.toString id)

open Verso.Doc.Elab

structure DocstringConfig where
  name : Ident × Name
  /--
  Ignores the option `verso.docstring.allowMissing` and allows _this_ docstring to be missing.
  -/
  allowMissing : Bool
  /-- Suppress the fields of a structure. -/
  hideFields : Bool := false
  /-- Suppress the constructor of a structure or class. -/
  hideStructureConstructor : Bool := false
  /-- Label to show instead of the default. -/
  label : Option String := none

section
variable [Monad m] [MonadOptions m] [MonadEnv m] [MonadLiftT CoreM m] [MonadLiftT MetaM m] [MonadError m]
variable [MonadLog m] [AddMessageContext m] [Elab.MonadInfoTree m]

meta instance : FromArgs DocstringConfig m where
  fromArgs :=
   DocstringConfig.mk <$>
    .positional `name .documentableName <*>
    .flagM `allowMissing (verso.docstring.allowMissing.get <$> getOptions)
      "Warn instead of error on missing docstrings (defaults to value of option `verso.docstring.allowMissing)" <*>
    .flag `hideFields false <*>
    .flag `hideStructureConstructor false <*>
    .named `label .string true

end

open Verso.Doc.Elab

open Block.Docstring in
@[block_command]
meta def docstring : BlockCommandOf DocstringConfig
  | ⟨(x, name), allowMissing, hideFields, hideCtor, customLabel⟩ => do
    let opts : Options → Options := (verso.docstring.allowMissing.set · allowMissing)

    withOptions opts do
      Doc.PointOfInterest.save (← getRef) name.toString (detail? := some "Documentation")
      let blockStx ←
        match ← getDocString? (← getEnv) name with
        | none => pure #[]
        | some docs =>
          let some ast := MD4Lean.parse docs
            | throwErrorAt x "Failed to parse docstring as Markdown"

          ast.blocks.mapM (blockFromMarkdownWithLean [name])

      if !(← Docstring.getAllowDeprecated) && Lean.Linter.isDeprecated (← getEnv) name then
        Lean.logError m!"'{name}' is deprecated.\n\nSet option 'verso.docstring.allowDeprecated' to 'true' to allow documentation for deprecated names."

      let declType ← Block.Docstring.DeclType.ofName name (hideFields := hideFields) (hideStructureConstructor := hideCtor)

      let signature ← Signature.forName name

      let extras ← getExtras name declType

      let altNames ← getStoredSuggestions name

      ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstring $(quote name) $(quote declType) $(quote signature) $(quote customLabel) $(quote altNames.toArray)) #[$(blockStx ++ extras),*])
where
  getExtras (name : Name) (declType : Block.Docstring.DeclType) : DocElabM (Array Term) :=
    match declType with
    | .structure isClass constructor? _ fieldInfo parents _ => do
      let ctorRow : Option Term ← constructor?.mapM fun constructor => do
        let header := if isClass then "Instance Constructor" else "Constructor"
        let sigDesc : Array Term ←
          if let some docs := constructor.docstring? then
            let some mdAst := MD4Lean.parse docs
              | throwError "Failed to parse docstring as Markdown"
            mdAst.blocks.mapM (blockFromMarkdownWithLean [name, constructor.name])
          else pure (#[] : Array Term)
        let sig ← `(Verso.Doc.Block.other (Verso.Genre.Manual.Block.internalSignature $(quote constructor.hlName) none) #[$sigDesc,*])
        ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstringSection $(quote header)) #[$sig])

      let parentsRow : Option Term ← do
        if parents.isEmpty then pure none
        else
          let header := "Extends"
          let inh ← ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.inheritance $(quote name) $(quote parents)) #[])
          some <$> ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstringSection $(quote header)) #[$inh])

      let fieldsRow : Option Term ← do
        let header := if isClass then "Methods" else "Fields"
        let fieldInfo := fieldInfo.filter (·.subobject?.isNone)
        let fieldSigs : Array Term ← fieldInfo.mapM fun i => do
          let inheritedFrom : Option Nat :=
            i.fieldFrom.head?.bind (fun n => parents.findIdx? (·.name == n.name))
          let sigDesc : Array Term ←
            if let some docs := i.docString? then
              let some mdAst := MD4Lean.parse docs
                | throwError "Failed to parse docstring as Markdown"
              mdAst.blocks.mapM (blockFromMarkdownWithLean <| name :: (constructor?.map ([·.name])).getD [])
            else
              pure (#[] : Array Term)
          ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.fieldSignature $(quote i.visibility) $(quote i.fieldName) $(quote i.type) $(quote inheritedFrom) $(quote <| parents.map (·.parent))) #[$sigDesc,*])
        if fieldSigs.isEmpty then pure none
        else some <$> ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstringSection $(quote header)) #[$fieldSigs,*])

      pure <| ctorRow.toArray ++ parentsRow.toArray ++ fieldsRow.toArray
    | .inductive ctors .. => do
      let ctorSigs : Array Term ←
        -- Elaborate constructor docs in the type's NS
        ctors.mapM fun c => withTheReader Core.Context ({· with currNamespace := name}) do
          let sigDesc ←
            if let some docs := c.docstring? then
              let some mdAst := MD4Lean.parse docs
                | throwError "Failed to parse docstring as Markdown"
              mdAst.blocks.mapM (blockFromMarkdownWithLean [name, c.name])
            else pure (#[] : Array Term)
          ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.constructorSignature $(quote c.signature)) #[$sigDesc,*])
      pure #[← ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstringSection "Constructors") #[$ctorSigs,*])]
    | _ => pure #[]

section
variable {m}
variable [Monad m] [MonadError m] [MonadLiftT CoreM m] [MonadLiftT MetaM m] [MonadEnv m]
variable [MonadLog m] [AddMessageContext m] [MonadOptions m] [MonadWithOptions m]
variable [Lean.Elab.MonadInfoTree m]

structure IncludeDocstringOpts where
  name : Name
  elaborate : Bool

meta instance : FromArgs IncludeDocstringOpts m where
  fromArgs :=
    IncludeDocstringOpts.mk <$> (.positional `name .documentableName <&> (·.2)) <*> .flag `elab true
end

open Block.Docstring in
@[block_command]
meta def includeDocstring : BlockCommandOf IncludeDocstringOpts
  | {name, elaborate} => do
    let fromMd :=
      if elaborate then
        blockFromMarkdownWithLean [name]
      else
        Markdown.blockFromMarkdown (handleHeaders := Markdown.strongEmphHeaders)

    let blockStx ←
      match ← getDocString? (← getEnv) name with
      | none => pure #[]
      | some docs =>
        let some ast := MD4Lean.parse docs
          | throwError "Failed to parse docstring as Markdown"
        ast.blocks.mapM fromMd

    ``(Doc.Block.concat #[$blockStx,*])

def Block.optionDocs (name : Name) (defaultValue : Option Highlighted) : Block where
  name := `Verso.Genre.Manual.optionDocs
  data := ToJson.toJson (name, defaultValue)

open Lean Elab Term in
elab "docs_for%" name:ident : term => do
  let x ← realizeGlobalConstNoOverloadWithInfo name
  if let some docs ← findDocString? (← getEnv) x then
    pure <| .lit <| .strVal docs
  else
    throwErrorAt name "No docs for {x}"

open Lean Elab Term in
elab "sig_for%" name:ident : term => do
  let x ← realizeGlobalConstNoOverloadWithInfo name
  let ⟨fmt, _infos⟩ ← withOptions (·.setBool `pp.tagAppFns true) <| Block.Docstring.ppSignature x
  let tt := Lean.Widget.TaggedText.prettyTagged (w := 48) fmt
  pure <| .lit <| .strVal tt.stripTags


meta def highlightDataValue (v : DataValue) : Highlighted :=
  .token <|
    match v with
    | .ofString (v : String) => ⟨.str v, toString v⟩
    | .ofBool b =>
      if b then
        ⟨.const ``true (sig_for% true) (some <| "The Boolean value `true`") false none, "true"⟩
      else
        ⟨.const ``false (sig_for% false) (some <| "The Boolean value `false`") false none, "false"⟩
    | .ofName (v : Name) => ⟨.unknown, v.toString⟩
    | .ofNat (v : Nat) => ⟨.unknown, toString v⟩
    | .ofInt (v : Int) => ⟨.unknown, toString v⟩
    | .ofSyntax (v : Syntax) => ⟨.unknown, toString v⟩ -- TODO

@[expose]
def optionDocs.Args := Ident
meta instance : FromArgs optionDocs.Args DocElabM := ⟨.positional `name .ident "The option name"⟩

open Block.Docstring in
@[block_command]
meta def optionDocs : BlockCommandOf optionDocs.Args
  | x => do
    let optDecl ← getOptionDecl x.getId
    Doc.PointOfInterest.save x.raw optDecl.declName.toString
    let some mdAst := MD4Lean.parse optDecl.descr
      | throwErrorAt x.raw "Failed to parse docstring as Markdown"
    let contents ← mdAst.blocks.mapM (blockFromMarkdownWithLean [])
    ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.optionDocs $(quote x.getId) $(quote <| highlightDataValue optDecl.defValue)) #[$contents,*])

open Verso.Search in
def optionDomainMapper : DomainMapper :=
  DomainMapper.withDefaultJs optionDomain "Compiler Option" "doc-option-domain" |>.setFont { family := .code }

open Verso.Genre.Manual.Markdown in
@[block_extension optionDocs]
def optionDocs.descr : BlockDescr := withHighlighting {
  init st := st
    |>.setDomainTitle optionDomain "Compiler options"
    |>.addQuickJumpMapper optionDomain optionDomainMapper

  traverse id info _ := do
    let .ok (name, _defaultValue) := FromJson.fromJson? (α := Name × Highlighted) info
      | do logError "Failed to deserialize docstring data while traversing an option"; pure none

    let path ← (·.path) <$> read
    let _ ← Verso.Genre.Manual.externalTag id path name.toString
    Index.addEntry id {term := Doc.Inline.code name.toString}
    if name.getPrefix != .anonymous then
      Index.addEntry id {term := Doc.Inline.code name.getString!, subterm := some <| Doc.Inline.code name.toString}

    modify fun st => st.saveDomainObject optionDomain name.toString id

    pure none
  toHtml := some <| fun _goI goB id info contents =>
    open Verso.Doc.Html in
    open Verso.Output Html in do
      let .ok (name, defaultValue) := FromJson.fromJson? (α := Name × Highlighted) info
        | do Verso.Doc.Html.HtmlT.logError "Failed to deserialize docstring data while generating HTML for an option"; pure .empty
      let x : Html := Html.text true <| Name.toString name

      let xref ← HtmlT.state
      let idAttr := xref.htmlId id

      return {{
        <div class="namedocs" {{idAttr}}>
          {{permalink id xref false}}
          <span class="label">"option"</span>
          <pre class="signature hl lean block">{{x}}</pre>
          <div class="text">
            <p>"Default value: " <code class="hl lean inline">{{← defaultValue.toHtml (g := Manual)}}</code></p>
            {{← contents.mapM goB}}
          </div>
        </div>
      }}
  localContentItem := fun _id info _contents => open Verso.Output.Html in do
    let (name, _defaultValue) ← FromJson.fromJson? (α := Name × Highlighted) info
    pure #[
      (name.toString, {{<code>{{name.toString}}</code>}}),
      (s!"{name.toString} (Option)", {{<code>{{name.toString}}</code>" (Option)"}})
    ]
  toTeX := some <| fun _goI goB _id _info contents => contents.mapM goB
  extraCss := [docstringStyle]
}

def Block.tactic (name : Lean.Elab.Tactic.Doc.TacticDoc) («show» : Option String) : Block where
  name := `Verso.Genre.Manual.tactic
  data := ToJson.toJson (name, «show»)

structure TacticDocsOptions where
  name : StrLit ⊕ Ident
  «show» : Option String
  replace : Bool
  allowMissing : Bool

section

variable [Monad m] [MonadError m] [MonadLiftT CoreM m] [MonadOptions m]

meta instance : FromArgs TacticDocsOptions m where
  fromArgs :=
    TacticDocsOptions.mk <$>
      .positional `name strOrName <*>
      .named `show .string true <*>
      .flag `replace false <*>
      .flagM `allowMissing (verso.docstring.allowMissing.get <$> getOptions)
        "Warn instead of error on missing docstrings (defaults to value of option `verso.docstring.allowMissing)"
where
  strOrName : ValDesc m (StrLit ⊕ Ident) := {
    description := "First token in tactic, or canonical parser name"
    signature := .Ident ∪ .String
    get := fun
      | .name x => pure (.inr x)
      | .str s => pure (.inl s)
      | .num n => throwErrorAt n "Expected tactic name (either first token as string, or internal parser name)"
  }

end

open Lean Elab Term Parser Tactic Doc in
private def getTactic (name : StrLit ⊕ Ident) : TermElabM TacticDoc := do
  for t in ← allTacticDocs do
    match name with
    | .inr name => if t.internalName == name.getId then return t
    | .inl name => if t.userName == name.getString then return t
  let n : MessageData :=
    match name with
    | .inl x => x
    | .inr x => x
  let blame : Syntax := name.elim TSyntax.raw TSyntax.raw
  throwErrorAt blame m!"Tactic not found: {n}"


open Lean Elab Term Parser Tactic Doc in
private meta def getTacticOverloads (name : StrLit ⊕ Ident) : TermElabM (Array TacticDoc) := do
  let mut out := #[]
  for t in ← allTacticDocs do
    match name with
    | .inr name => if t.internalName == name.getId then out := out.push t
    | .inl name => if t.userName == name.getString then out := out.push t

  if out.size > 0 then return out
  let n : MessageData :=
    match name with
    | .inl x => x
    | .inr x => x
  let blame : Syntax := name.elim TSyntax.raw TSyntax.raw
  throwErrorAt blame m!"Tactic not found: {n}"


open Lean Elab Term Parser Tactic Doc in
private meta def getTactic? (name : String ⊕ Name) : TermElabM (Option TacticDoc) := do
  for t in ← allTacticDocs do
    if .inr t.internalName == name || .inl t.userName == name then
      return some t
  return none

open Block.Docstring in
@[directive]
meta def tactic : DirectiveExpanderOf TacticDocsOptions
  | opts, more => do
    let tactics ← getTacticOverloads opts.name
    let blame : Syntax := opts.name.elim TSyntax.raw TSyntax.raw
    let withDocs := tactics.filter (·.docString.isSome)
    -- Prefer overloads with docstrings to overloads without
    let tactic ←
      if h : tactics.size = 0 then throwErrorAt blame "Tactic not found"
      else if h : withDocs.size > 0 then pure withDocs[0]
      else pure tactics[0]
    if tactics.size > 1 then
      logWarningAt blame s!"Found {tactics.size} overloads: {tactics.map (toString ·.internalName) |>.toList |> ", ".intercalate}"
    Doc.PointOfInterest.save (← getRef) tactic.userName
    if tactic.userName == tactic.internalName.toString && opts.show.isNone then
      throwError "No `show` option provided, but the tactic has no user-facing token name"
    let contents ←
      if opts.replace then pure #[]
      else
        let some str := tactic.docString
          | throwError "Tactic {tactic.userName} ({tactic.internalName}) has no docstring"
        let some mdAst := MD4Lean.parse str
          | throwError m!"Failed to parse docstring as Markdown. Docstring contents:\n{repr str}"
        mdAst.blocks.mapM (blockFromMarkdownWithLean [])
    let userContents ← more.mapM elabBlock
    ``(Verso.Doc.Block.other (Block.tactic $(quote tactic) $(quote opts.show)) #[$(contents ++ userContents),*])

def Inline.tactic : Inline where
  name := `Verso.Genre.Manual.tacticInline


open Verso.Search in
def tacticDomainMapper : DomainMapper := {
  className := "tactic-domain"
  displayName := "Tactic"
  dataToSearchables :=
    "(domainData) =>
  Object.entries(domainData.contents).map(([key, value]) => ({
    searchKey: value[0].data.userName,
    address: `${value[0].address}#${value[0].id}`,
    domainId: 'Verso.Genre.Manual.doc.tactic',
    ref: value,
  }))"
  : DomainMapper }.setFont { family := .code, weight := .bold}

open Verso.Genre.Manual.Markdown in
open Lean Elab Term Parser Tactic Doc in
@[block_extension tactic]
def tactic.descr : BlockDescr := withHighlighting {
  init st := st
    |>.setDomainTitle tacticDomain "Tactic Documentation"
    |>.setDomainDescription tacticDomain "Detailed descriptions of tactics"
    |>.addQuickJumpMapper tacticDomain tacticDomainMapper

  traverse id info _ := do
    let .ok (tactic, «show») := FromJson.fromJson? (α := TacticDoc × Option String) info
      | do logError "Failed to deserialize docstring data while traversing a tactic"; pure none
    let path ← (·.path) <$> read
    let _ ← Verso.Genre.Manual.externalTag id path <| show.getD tactic.userName
    Index.addEntry id {term := Doc.Inline.code <| show.getD tactic.userName}

    modify fun st =>
      st
        |>.saveDomainObject tacticDomain tactic.internalName.toString id
        |>.saveDomainObjectData tacticDomain tactic.internalName.toString (json%{"userName": $tactic.userName})

    pure none
  toHtml := some <| fun _goI goB id info contents =>
    open Verso.Doc.Html in
    open Verso.Output Html in do
      let .ok (tactic, «show») := FromJson.fromJson? (α := TacticDoc × Option String) info
        | do Verso.Doc.Html.HtmlT.logError "Failed to deserialize tactic data while generating HTML for a tactic"; pure .empty
      let x : Highlighted := .token ⟨.keyword tactic.internalName none tactic.docString, show.getD tactic.userName⟩

      let xref ← HtmlT.state
      let idAttr := xref.htmlId id

      return {{
        <div class="namedocs" {{idAttr}}>
          {{permalink id xref false}}
          <span class="label">"tactic"</span>
          <pre class="signature hl lean block">{{← x.toHtml (g := Manual)}}</pre>
          <div class="text">
            {{← contents.mapM goB}}
          </div>
        </div>
      }}
  localContentItem := fun _id info _contents => open Verso.Output.Html in do
    let (tactic, «show») ← FromJson.fromJson? (α := TacticDoc × Option String) info
    let str := show.getD tactic.userName
    pure #[(str, {{<code class="tactic-name">{{str}}</code>}})]
  toTeX := some <| fun _goI goB _id _info contents => contents.mapM goB
  extraCss := [docstringStyle]
}

structure TacticInlineOptions where
  «show» : Option String

section
variable [Monad m] [MonadError m]

meta instance : FromArgs TacticInlineOptions m where
  fromArgs :=
    TacticInlineOptions.mk <$> .named `show .string true
end

@[role tactic]
meta def tacticInline : RoleExpanderOf TacticInlineOptions
  | {«show»}, inlines => do
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let `(inline|code( $tac:str )) := arg
      | throwErrorAt arg "Expected code literal with the tactic name"
    let tacTok := tac.getString
    let tacName := tac.getString.toName
    let some tacticDoc := (← getTactic? (.inl tacTok)) <|> (← getTactic? (.inr tacName))
      | throwErrorAt tac "Didn't find tactic named {tac}"

    let hl : Highlighted := tacToken tacticDoc «show»

    `(Verso.Doc.Inline.other {Inline.tactic with data := ToJson.toJson $(quote hl)} #[Verso.Doc.Inline.code $(quote tacticDoc.userName)])
where
  tacToken (t : Lean.Elab.Tactic.Doc.TacticDoc) (overrideStr : Option String) : Highlighted :=
    .token ⟨.keyword t.internalName none t.docString, overrideStr.getD t.userName⟩


@[inline_extension tacticInline]
def tacticInline.descr : InlineDescr := withHighlighting {
  traverse _ _ _ := do
    pure none
  toTeX :=
    some <| fun go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  extraCss := [docstringStyle]
  toHtml :=
    open Verso.Output.Html Verso.Doc.Html in
    some <| fun _ _ data _ => do
      match FromJson.fromJson? data with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean tactic code while rendering HTML: " ++ err
        pure .empty
      | .ok (hl : Highlighted) =>
        hl.inlineHtml (g := Manual) "examples"
}

-- TODO implement a system upstream like the one for normal tactics
def Block.conv (name : Name) («show» : String) (docs? : Option String) : Block where
  name := `Verso.Genre.Manual.conv
  data := ToJson.toJson (name, «show», docs?)

structure ConvTacticDoc where
  name : Name
  docs? : Option String

open Lean Elab Term Parser Tactic Doc in
meta def getConvTactic (name : StrLit ⊕ Ident) (allowMissing : Option Bool) : TermElabM ConvTacticDoc :=
  withOptions (allowMissing.map (fun b opts => verso.docstring.allowMissing.set opts b) |>.getD (·)) do
    let .inr kind := name
      | throwError "Strings not yet supported here"
    let parserState := parserExtension.getState (← getEnv)
    let some convs := parserState.categories.find? `conv
      | throwError "Couldn't find conv tactic list"
    for ⟨k, ()⟩ in convs.kinds do
      if kind.getId.isSuffixOf k then
        return ⟨k, ← getDocString? (← getEnv) k⟩
    throwError m!"Conv tactic not found: {kind}"

open Block.Docstring in
@[directive]
meta def conv : DirectiveExpanderOf TacticDocsOptions
  | opts, more => do
    let tactic ← getConvTactic opts.name opts.allowMissing
    Doc.PointOfInterest.save (← getRef) tactic.name.toString
    let contents ← if let some d := tactic.docs? then
        let some mdAst := MD4Lean.parse d
          | throwError "Failed to parse docstring as Markdown"
        mdAst.blocks.mapM (blockFromMarkdownWithLean [])
      else pure #[]
    let userContents ← more.mapM elabBlock
    let some toShow := opts.show
      | throwError "An explicit 'show' is mandatory for conv docs (for now)"
    ``(Verso.Doc.Block.other (Block.conv $(quote tactic.name) $(quote toShow) $(quote tactic.docs?)) #[$(contents ++ userContents),*])

open Verso.Search in
def convDomainMapper : DomainMapper := {
  className := "conv-tactic-domain",
  displayName := "Conv Tactic",
  dataToSearchables :=
    "(domainData) =>
  Object.entries(domainData.contents).map(([key, value]) => ({
    searchKey: value[0].data.userName,
    address: `${value[0].address}#${value[0].id}`,
    domainId: 'Verso.Genre.Manual.doc.tactic.conv',
    ref: value,
  }))"
  : DomainMapper }.setFont { family := .code, weight := .bold }

open Verso.Genre.Manual.Markdown in
open Lean Elab Term Parser Tactic Doc in
@[block_extension conv]
def conv.descr : BlockDescr := withHighlighting {
  init st := st
    |>.setDomainTitle convDomain "Conversion Tactics"
    |>.setDomainDescription convDomain "Tactics for performing targeted rewriting of subterms"
    |>.addQuickJumpMapper convDomain convDomainMapper

  traverse id info _ := do
    let .ok (name, «show», _docs?) := FromJson.fromJson? (α := Name × String × Option String) info
      | do logError "Failed to deserialize conv docstring data"; pure none
    let path ← (·.path) <$> read
    let _ ← Verso.Genre.Manual.externalTag id path <| name.toString
    Index.addEntry id {term := Doc.Inline.code <| «show»}

    modify fun st => st.saveDomainObject convDomain name.toString id
    modify fun st => st.saveDomainObjectData convDomain name.toString (json%{"userName": $«show»})

    pure none
  toHtml := some <| fun _goI goB id info contents =>
    open Verso.Doc.Html in
    open Verso.Output Html in do
      let .ok (name, «show», docs?) := FromJson.fromJson? (α := Name × String × Option String) info
        | do Verso.Doc.Html.HtmlT.logError "Failed to deserialize conv tactic data"; pure .empty
      let x : Highlighted := .token ⟨.keyword (some name) none docs?, «show»⟩

      let xref ← HtmlT.state
      let idAttr := xref.htmlId id

      return {{
        <div class="namedocs" {{idAttr}}>
          {{permalink id xref false}}
          <span class="label">"conv tactic"</span>
          <pre class="signature hl lean block">{{← x.toHtml (g := Manual)}}</pre>
          <div class="text">
            {{← contents.mapM goB}}
          </div>
        </div>
      }}
  localContentItem := fun _id info _contents => open Verso.Output.Html in do
    let (_name, «show», _docs?) ← FromJson.fromJson? (α := Name × String × Option String) info
    pure #[(«show», {{<code class="tactic-name">{{«show»}}</code>}})]

  toTeX := some <| fun _goI goB _id _info contents => contents.mapM goB
  extraCss := [docstringStyle]
}

public inline_extension Inline.conv (hl : Highlighted) via withHighlighting where
  data := ToJson.toJson hl
  traverse _ _ _ := pure none
  toTeX :=
    some <| fun go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  extraCss := [docstringStyle]
  toHtml :=
    open Verso.Output.Html Verso.Doc.Html in
    some <| fun _ _ data _ => do
      match FromJson.fromJson? data with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize conv tactic code while rendering HTML: " ++ err
        pure .empty
      | .ok (hl : Highlighted) =>
        hl.inlineHtml (g := Manual) "examples"

@[role_expander conv]
meta def convInline : RoleExpander
  | _args, inlines => do
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let `(inline|code( $convTac:str )) := arg
      | throwErrorAt arg "Expected code literal with the conv tactic name"
    let convTacName := convTac.getString.toName
    let convTacDoc ← getConvTactic (.inr (mkIdent convTacName)) none

    let hl : Highlighted := convToken convTacDoc convTac.getString

    return #[← `(Verso.Doc.Inline.other (Inline.conv $(quote hl)) #[Verso.Doc.Inline.code $(quote convTac.getString)])]
where
  convToken (t : ConvTacticDoc) (showStr : String) : Highlighted :=
    .token ⟨.keyword (some t.name) none t.docs?, showStr⟩
