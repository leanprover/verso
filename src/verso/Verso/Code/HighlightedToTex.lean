/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jason Reed
-/
import SubVerso.Highlighting
import Verso.Method
import Verso.Output.TeX

open SubVerso.Highlighting
open Verso.Output
open Lean (Json ToJson FromJson Quote)
open Std (HashMap)

namespace SubVerso.Highlighting

open Verso.Output.TeX in
partial defmethod Highlighted.toTeX : Highlighted → Verso.Output.TeX
  | .token t => \TeX{\texttt{\Lean{ t.content }}}
  | .text str => \TeX{\Lean{ str }}
  | .seq hts => .seq <| hts.map (·.toTeX)
  | .span _info content => content.toTeX
  | .tactics _info _start _end _content => \TeX{"[Tactics]"}
  | .point _kind _info => \TeX{"Point]"}
  | .unparsed str => .raw str -- FIXME: Is this right?
