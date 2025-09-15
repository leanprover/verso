/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual.Basic
import Verso.Doc.ArgParse

open Verso Doc Elab
open Verso.Genre Manual
open Verso.ArgParse
open Lean.Doc.Syntax

open Lean Elab

set_option pp.rawOnError true

namespace Verso.Genre.Manual

inductive TableConfig.Alignment where
  | left | right | center
deriving ToJson, FromJson, DecidableEq, Repr, Ord

open Syntax in
open TableConfig.Alignment in
instance : Quote TableConfig.Alignment where
  quote
    | .left => mkCApp ``left #[]
    | .center => mkCApp ``center #[]
    | .right => mkCApp ``right #[]

namespace TableConfig

/-- HTML class name for alignment -/
def Alignment.htmlClass : Alignment → String
  | .left => "left-align"
  | .right => "right-align"
  | .center => "center-align"

end TableConfig


structure TableConfig where
  /-- Name for refs -/
  name : Option String := none
  header : Bool := false
  /-- Alignment in the text (`none` means defer to stylesheet default) -/
  alignment : Option TableConfig.Alignment := none

block_extension Block.table (columns : Nat) (header : Bool) (tag : Option String) (alignment : Option TableConfig.Alignment) (assignedTag : Option Tag := none) where
  data := ToJson.toJson (columns, header, tag, assignedTag, alignment)

  traverse id data contents := do
    match FromJson.fromJson? data (α := Nat × Bool × Option String × Option Tag × Option TableConfig.Alignment) with
    | .error e => logError s!"Error deserializing table data: {e}"; pure none
    | .ok (_, _, none, _) => pure none
    | .ok (c, hdr, some x, none, align) =>
      let path ← (·.path) <$> read
      let tag ← Verso.Genre.Manual.externalTag id path x
      pure <| some <| Block.other {Block.table c hdr (some x) (assignedTag := some tag) align with id := some id} contents
    | .ok (_, _, some _, some _, _) => pure none

  toTeX := none

  toHtml :=
    open Verso.Doc.Html in
    open Verso.Output.Html in
    some <| fun _goI goB id data blocks => do
      match FromJson.fromJson? data (α := Nat × Bool × Option String × Option Tag × Option TableConfig.Alignment) with
      | .error e =>
        HtmlT.logError s!"Error deserializing table data: {e}"
        return .empty
      | .ok (columns, header, _, _, align) =>
      if let #[.ul items] := blocks then
        let xref ← HtmlT.state
        let attrs := xref.htmlId id
        let «class» := "tabular" ++ (align.map (" " ++ ·.htmlClass)).getD ""
        let mut items := items
        let mut rows := #[]
        while items.size > 0 do
          rows := rows.push (items.take columns |>.map (·.contents))
          items := items.extract columns items.size

        return {{
          <table class={{«class»}} {{attrs}}>
            {{← rows.mapIdxM fun i r => do
              let cols ← Output.Html.seq <$> r.mapM fun c => do
                let cell : Output.Html ← c.mapM goB
                if header && i == 0 then
                  pure {{<th>{{cell}}</th>}}
                else
                  pure {{<td>{{cell}}</td>}}
              if header && i == 0 then
                pure {{<thead><tr>{{cols}}</tr></thead>}}
              else
                pure {{<tr>{{cols}}</tr>}}
            }}
          </table>
        }}

      else
        HtmlT.logError "Malformed table"
        return .empty

  extraCss := [
r##"
table.tabular {
  margin: auto;
  border-spacing: 1rem;
}
table.tabular.left-align {
  margin-right: auto;
  margin-left: 0;
}
table.tabular.center-align {
  margin: auto;
}
table.tabular.right-align {
  margin-left auto;
  margin-right: 0;
}
table.tabular td, table.tabular th {
  text-align: left;
  vertical-align: top;
}
table.tabular td > p:first-child, table.tabular th > p:first-child {
  margin-top: 0;
}
table.tabular td > p:last-child, table.tabular th > p:first-child {
  margin-bottom: 0;
}
"##
  ]

section
variable [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] [MonadFileMap m]

def TableConfig.parse : ArgParse m TableConfig :=
  TableConfig.mk <$> .named `tag .string true <*> .flag `header true <*> .named `align alignment true
where
  alignment := {
    description := "Alignment of the table ('left', 'right', or 'center')"
    signature := .Ident
    get
      | .name x =>
        match x.getId with
        | `left => pure .left
        | `right => pure .right
        | `center => pure .center
        | _ => throwErrorAt x "Expected 'left', 'right', or 'center'"
      | .num x | .str x => throwErrorAt x "Expected 'left', 'right', or 'center'"
  }

instance : FromArgs TableConfig m := ⟨TableConfig.parse⟩

end

@[directive]
def table : DirectiveExpanderOf TableConfig
  | cfg, contents => do
    -- The table should be a list of lists. Extract them!
    let #[oneBlock] := contents
      | throwError "Expected a single unordered list"
    let `(block|ul{$items*}) := oneBlock
      | throwErrorAt oneBlock "Expected a single unordered list"
    let preRows ← items.mapM getLi
    let rows ← preRows.mapM fun blks => do
      let #[oneInRow] := blks.filter (·.raw.isOfKind ``Lean.Doc.Syntax.ul)
        | throwError "Each row should have exactly one list in it"
      let `(block|ul{ $cellItems*}) := oneInRow
        | throwErrorAt oneInRow "Each row should have exactly one list in it"
      cellItems.mapM getLi
    if h : rows.size = 0 then
      throwErrorAt oneBlock "Expected at least one row"
    else
      let columns := rows[0].size
      if columns = 0 then
        throwErrorAt oneBlock "Expected at least one column"
      if rows.any (·.size != columns) then

        throwErrorAt oneBlock s!"Expected all rows to have same number of columns, but got {rows.map (·.size)}"

      let flattened := rows.flatten
      let blocks : Array (Syntax.TSepArray `term ",") ← flattened.mapM (·.mapM elabBlock)
      ``(Block.other (Block.table $(quote columns) $(quote cfg.header) $(quote cfg.name) $(quote cfg.alignment)) #[Block.ul #[$[Verso.Doc.ListItem.mk #[$blocks,*]],*]])

where
  getLi : Syntax → DocElabM (TSyntaxArray `block)
    | `(list_item| * $content* ) => pure content
    | other => throwErrorAt other "Expected list item"
