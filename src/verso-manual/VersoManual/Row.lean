/-
Copyright (c) 2024-2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual.Basic
import Verso.Doc.ArgParse
import Verso.Doc.Elab

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual Html
open Verso.Doc.Html (HtmlT)
open Verso.Output (Html)

namespace Verso.Genre.Manual

block_extension Block.row (alignItems : String) where
  data := Json.str alignItems
  traverse _ _ _ := pure none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ blockHtml _ data content => do
      let .str ai := data
        | HtmlT.logError "Expected string JSON for row" *> pure .empty
      let style := s!"display: flex; flex-wrap: wrap; align-items: {ai}; gap: 1em;"
      pure {{
        <div class="verso-row" style={{style}}>
          {{← content.mapM blockHtml}}
        </div>
      }}
  toTeX :=
    some <| fun _ go _ _ content => do
      let rendered ← content.mapM go
      pure <| .seq <| rendered.toList.intersperse (.raw "\\quad ") |>.toArray

structure RowConfig where
  align : String

section
variable [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m]

def RowConfig.parse : ArgParse m RowConfig :=
  RowConfig.mk <$> .namedD' `align "top"

instance : FromArgs RowConfig m := ⟨RowConfig.parse⟩

end

/--
Arranges the contained blocks in a horizontal row. HTML output uses flexbox; TeX output
concatenates the rendered blocks separated by `\quad`, relying on each block to lay itself
out inline.

The `align` argument controls vertical alignment within the row, accepting `"top"`, `"middle"`, or
`"bottom"`. It is only meaningful for HTML output.
-/
@[directive]
def row : DirectiveExpanderOf RowConfig
  | config, stxs => do
    let alignItems ←
      match config.align with
      | "top"    => pure "flex-start"
      | "middle" => pure "center"
      | "bottom" => pure "flex-end"
      | other    => throwError "Expected 'top', 'middle', or 'bottom' for 'align', got {repr other}"
    let args ← stxs.mapM elabBlock
    ``(Verso.Doc.Block.other (Block.row $(quote alignItems)) #[ $[ $args ],* ])
