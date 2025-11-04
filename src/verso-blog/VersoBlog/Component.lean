/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoBlog.Basic
import VersoBlog.Component.Ext
import Verso.Doc.ArgParse
import Std.Data.HashSet

open Verso Genre Blog
open Verso.Doc
open Verso Output Html

open Std (HashSet)

namespace Verso.Genre.Blog

/-!
Components represent building blocks for more complex content that can be included in Verso pages.

Block-level components exist as block-level elements in a page. Examples include:
   * Editable code samples
   * Tables
   * Screenshot galleries
   * Tabs

Inline-level components are like block-level components, except for inline elements.
-/

structure ComponentId where
  id : String
deriving Repr, DecidableEq, Ord

instance : Coe ComponentId String where
  coe := ComponentId.id

instance : ToString ComponentId where
  toString := ComponentId.id

syntax (name := block_component) "block_component" ident : attr

syntax (name := inline_component) "inline_component" ident : attr

open Lean in
initialize
  let register (name) (strName : String) (ext : PersistentEnvExtension (Name × Name) (Name × Name) (Lean.NameMap Name)) (get : Syntax → Option Ident) := do
    registerBuiltinAttribute {
      name := name,
      ref := by exact decl_name%,
      add := fun decl stx kind => do
        unless kind == AttributeKind.global do throwError "invalid attribute '{name}', must be global"
        unless ((← getEnv).getModuleIdxFor? decl).isNone do
          throwError "invalid attribute '{name}', declaration is in an imported module"
        let some extIdent := get stx
          | throwError "invalid syntax for '{name}' attribute"

        let extName ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo extIdent

        modifyEnv fun env => ext.addEntry env (extName.eraseMacroScopes, decl.eraseMacroScopes) -- TODO check that it's not already there

      descr := s!"Registers a definition as the implementation of {strName}"
    }
  register `block_component "a block component" blockComponentExt fun | `(attr|block_component $extIdent) => extIdent | _ => none
  register `inline_component "an inline component" inlineComponentExt fun | `(attr|inline_component $extIdent) => extIdent | _ => none

namespace Component
structure State where
  componentIds : HashSet String := {}
  headerJs : HashSet String := {}
  headerCss : HashSet String := {}

def State.freshId (state : State) : String × State := Id.run do
  let base := "--verso-component-"
  let mut n := state.componentIds.size
  repeat
    if base ++ toString n ∈ state.componentIds then
      n := n + 1
    else
      break
  let id := base ++ toString n
  return (id, {state with componentIds := state.componentIds.insert id})

end Component

abbrev ComponentM := ReaderT Components (StateT Component.State IO)

abbrev HtmlM genre := HtmlT genre ComponentM

structure BlockComponent : Type where
  traverse : Lean.Json → Array (Doc.Block Page) → TraverseM (Option (Doc.Block Page)) :=
    fun _ _ => pure none

  /--
  Extra JavaScript files to add to the generated HTML.

  Each element is a pair of a filename and contents.
  -/
  jsFiles : Array (String × String) := #[]

  /--
  Extra CSS files to add to the generated HTML.

  Each element is a pair of a filename and contents.
  -/
  cssFiles : Array (String × String) := #[]

  toHtml : ComponentId → Lean.Json →
    (Inline Page → HtmlM Page Html) →
    (Block Page → HtmlM Page Html) →
    Array (Block Page) → HtmlM Page Html

deriving TypeName

structure InlineComponent : Type where
  traverse : Lean.Json → Array (Doc.Inline Page) → TraverseM (Option (Doc.Inline Page)) :=
    fun _ _ => pure none

  /--
  Extra JavaScript files to add to the generated HTML.

  Each element is a pair of a filename and contents.
  -/
  jsFiles : Array (String × String) := #[]

  /--
  Extra CSS files to add to the generated HTML.

  Each element is a pair of a filename and contents.
  -/
  cssFiles : Array (String × String) := #[]

  toHtml : ComponentId → Lean.Json →
    (Inline Page → HtmlM Page Html) →
    Array (Inline Page) → HtmlM Page Html

deriving TypeName

open Lean in
def Components.fromLists (blocks : List (Name × BlockComponent)) (inlines : List (Name × InlineComponent)) : Components where
  blocks := .ofList (blocks.map fun (x, b) => (x, Dynamic.mk b)) _
  inlines := .ofList (inlines.map fun (x, b) => (x, Dynamic.mk b)) _

open Lean in
private def nameAndDef [Monad m] [MonadRef m] [MonadQuotation m] (ext : Name × Name) : m Term := do
  let quoted : Term := quote ext.fst
  let ident ← mkCIdentFromRef ext.snd
  `(($quoted, $(⟨ident⟩)))

open Lean Elab Term in
scoped elab "%registered_block_components" : term => do
  let env ← getEnv
  let mut exts := #[]
  for (ext, descr) in blockComponentExt.getState env do
    exts := exts.push (ext, descr)
  for imported in blockComponentExt.toEnvExtension.getState env |>.importedEntries do
    for x in imported do
      exts := exts.push x
  let stx ← `([$[($(← exts.mapM nameAndDef) : Name × BlockComponent)],*])
  elabTerm stx none

open Lean Elab Term in
scoped elab "%registered_inline_components" : term => do
  let env ← getEnv
  let mut exts := #[]
  for (ext, descr) in inlineComponentExt.getState env do
    exts := exts.push (ext, descr)
  for imported in inlineComponentExt.toEnvExtension.getState env |>.importedEntries do
    for x in imported do
      exts := exts.push x
  let stx ← `([$[($(← exts.mapM nameAndDef) : Name × InlineComponent)],*])
  elabTerm stx none


open Lean.Parser Term in
def extContents := structInstFields (sepByIndent Term.structInstField "; " (allowTrailingSep := true))

/--
Defines a new block component.

The `toHtml` field is mandatory, while `traverse`, `cssFiles`, and `jsFiles` are optional. The
component's parameters are in scope for `toHtml`, but they must have `ToJson` and `FromJson`
instances.

The `+directive` option just after the `block_component` keyword causes a directive to be generate
that expands into a use of the component. The directive's arguments are passed as the arguments to
the component. If this option is provided, then the parameter's types must additionally have
`FromArgVal` instances.
-/
syntax (docComment)? "block_component " ("+" noWs &"directive")? ident (ppSpace bracketedBinder)* ppIndent(ppSpace "where" extContents) : command

syntax (docComment)? "inline_component " ident (ppSpace bracketedBinder)* ppIndent(ppSpace "where" extContents) : command


open Lean in
def argNames : Lean.TSyntax ``Lean.Parser.Term.bracketedBinder → Array Ident
  | `(bracketedBinder| ($xs* : $_) )
  | `(bracketedBinder| {$xs* : $_} )
  | `(bracketedBinder| ⦃$xs* : $_⦄ ) => xs.filterMap getIdents
  | _ => #[]
where
  getIdents (x : TSyntax [`ident, _]) : Option Ident :=
    if x.raw.isIdent then pure ⟨x.raw⟩ else none

open Lean in
def argType : Lean.TSyntax ``Lean.Parser.Term.bracketedBinder → Option Term
  | `(bracketedBinder| ($_* : $t) )
  | `(bracketedBinder| {$_* : $t} )
  | `(bracketedBinder| ⦃$_* : $t⦄ ) => pure t
  | _ => none

open Lean in
def argNamesTypes : Lean.TSyntax ``Lean.Parser.Term.bracketedBinder → Array (Ident × Term)
  | `(bracketedBinder| ($xs* : $t) )
  | `(bracketedBinder| {$xs* : $t} )
  | `(bracketedBinder| ⦃$xs* : $t⦄ ) => xs.filterMap getIdents |>.map ((·, t))
  | _ => #[]
where
  getIdents (x : TSyntax [`ident, _]) : Option Ident :=
    if x.raw.isIdent then pure ⟨x.raw⟩ else none



open Lean Elab Command in
def splitToHtml (fields : Array (TSyntax ``Lean.Parser.Term.structInstField)) :
    CommandElabM (Option Term × Array (TSyntax ``Lean.Parser.Term.structInstField)) := do
  let (is, isNot) := fields.partition fun
    | `(Lean.Parser.Term.structInstField|toHtml) => true
    | `(Lean.Parser.Term.structInstField|toHtml $_:ident* := $_) => true
    | _ => false
  if is.size > 1 then
    for i in is.drop 1 do
      logErrorAt i "Redundant 'toHtml' field"
  return (← is[0]?.mapM asFun, isNot.map (⟨·⟩))
where
  asFun : Syntax → CommandElabM Term
    | `(Lean.Parser.Term.structInstField|$x:ident) => `(term|$x)
    | `(Lean.Parser.Term.structInstField|$_:ident $arg:structInstFieldBinder* := $body:term) => do
      `(term|fun $(← arg.mapM toFunBinder)* => $body)
    | stx => dbg_trace "not {stx}"; pure ⟨stx⟩
  toFunBinder : TSyntax ``Lean.Parser.Term.structInstFieldBinder → CommandElabM (TSyntax ``Lean.Parser.Term.funBinder)
    | `(Lean.Parser.Term.structInstFieldBinder|$x:ident) =>
      `(Lean.Parser.Term.funBinder|$x:ident)
    | `(Lean.Parser.Term.structInstFieldBinder|{$xs* : $t}) =>
      `(Lean.Parser.Term.funBinder|{$xs* : $t})
    | `(Lean.Parser.Term.structInstFieldBinder|[$t]) =>
      `(Lean.Parser.Term.funBinder|[$t])
    | `(Lean.Parser.Term.structInstFieldBinder|($x:ident : $t)) =>
      `(Lean.Parser.Term.funBinder|($x:ident : $t))
    | `(Lean.Parser.Term.structInstFieldBinder|($x:hole : $t)) =>
      `(Lean.Parser.Term.funBinder|($x:hole : $t))

    | _ =>
      `(_)

open Lean in
def deJson [Monad m] [MonadQuotation m]
    (b : Ident × Term) : m (TSyntax `Lean.Parser.Term.doSeqItem) :=
  let (x, t) := b
  `(Lean.Parser.Term.doSeqItem| let $x ← match FromJson.fromJson? (α := $t) $x with
      | .error e => do
        (HtmlT.logError e : HtmlM Page Unit)
        return Html.empty
      | .ok v => pure v)


open Lean Elab Command in
open Verso.ArgParse in
elab_rules : command
  | `(command|$[$doc:docComment]? block_component $[+directive%$dirTok]? $x $args* where $contents;*) => do
    let argNames := args.flatMap argNamesTypes
    let cmd1 ←
      `(command|$[$doc:docComment]? def $x:ident {g} [bg : BlogGenre g] $args* : Array (Doc.Block g) → Doc.Block g := bg.blockComponent decl_name% (.arr #[$[toJson $(argNames.map (·.1))],*]))
    let compName := x.getId ++ `comp |> mkIdentFrom x
    let dirName := x.getId ++ `directive |> mkIdentFrom x
    let (toHtml?, other) ← splitToHtml contents
    let noJson ← argNames.mapM deJson
    let arr : TSyntax `Lean.Parser.Term.doSeqItem ←
      if !argNames.isEmpty then
        `(Lean.Parser.Term.doSeqItem|
          let .arr #[$(argNames.map (·.1)),*] := json
            | HtmlT.logError s!"Expected array, got {json}"
              return .empty)
      else `(Lean.Parser.Term.doSeqItem|pure ())
    let toHtml ← toHtml?.mapM fun tm =>
      `(Lean.Parser.Term.structInstField|
        toHtml id json goI goB contents := do
              $arr
              $noJson*
              ($tm id json goI goB contents))
    let other := toHtml.toArray ++ other
    let cmd2 ←
      `(command|
        $[$doc:docComment]?
        @[block_component $x]
        private def $compName : BlockComponent where
          $other;*)
    elabCommand cmd1
    elabCommand cmd2
    if dirTok.isSome then

      let argPat : Term ← argNames.foldrM (init := ← `(Unit.unit)) fun (x, _) y =>
        `(($x, $y))
      let argP : Term ← argNames.foldrM (init := ← ``(ArgParse.done)) fun (x, t) y =>
        ``((·, ·) <$> ArgParse.positional $(quote x.getId) (FromArgVal.fromArgVal (α := $t)) <*> $y)
      let argT ← argNames.foldrM (init := ← `(Unit)) fun (_, t) y => `($t × $y)
      elabCommand (← `(def T := $argT))
      elabCommand (← `(instance : FromArgs T DocElabM := ⟨$argP⟩))
      let qArgs : Term ← argNames.foldlM (init := x) fun tm (x, _) =>
        `($tm $$(quote $x))
      let cmd3 ←
        `(command|
          @[directive $x]
          def $dirName : DirectiveExpanderOf T
            | $argPat, blocks => do `($qArgs #[$$(← blocks.mapM elabBlock),*]))
      elabCommand cmd3


open Lean Elab Command in
elab_rules : command
  | `(command|$[$doc:docComment]? inline_component $x $args* where $contents;*) => do
    let argNames := args.flatMap argNamesTypes
    let cmd1 ←
      `(command|$[$doc:docComment]? def $x:ident {g} [bg : BlogGenre g] $args* : Array (Doc.Inline g) → Doc.Inline g := bg.inlineComponent decl_name% (.arr #[$[toJson $(argNames.map (·.1))],*]))
    let compName := x.getId ++ `comp |> mkIdentFrom x
    let (toHtml?, other) ← splitToHtml contents
    let noJson ← argNames.mapM deJson
    let arr : TSyntax `Lean.Parser.Term.doSeqItem ←
      if !argNames.isEmpty then
        `(Lean.Parser.Term.doSeqItem|
          let .arr #[$(argNames.map (·.1)),*] := json
            | HtmlT.logError s!"Expected array, got {json}"
              return .empty)
      else `(Lean.Parser.Term.doSeqItem|pure ())
    let toHtml ← toHtml?.mapM fun tm =>
      `(Lean.Parser.Term.structInstField|
        toHtml id json goI contents := do
              $arr
              $noJson*
              ($tm id json goI contents))
    let other := toHtml.toArray ++ other
    let cmd2 ←
      `(command|
        $[$doc:docComment]?
        @[inline_component $x]
        private def $compName : InlineComponent where
          $other;*)
    elabCommand cmd1
    elabCommand cmd2
