/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.Elab.InfoTree.Types

import Verso
import VersoManual.Basic
import VersoManual.HighlightedCode
import VersoManual.InlineLean.Outputs
import SubVerso.Examples

open SubVerso.Highlighting

open Verso Genre Manual ArgParse Doc Elab
open Verso Output Html
open Verso Code Highlighted WebAssets
open Verso.SyntaxUtils
open Lean Elab

namespace Verso.Genre.Manual.InlineLean


block_extension Block.syntaxError where
  traverse _ _ _ := pure none
  toTeX :=
    some <| fun _ go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  extraCss := [
    r"
.syntax-error {
  white-space: normal;
}
.syntax-error::before {
  counter-reset: linenumber;
}
.syntax-error > .line {
  display: block;
  white-space: pre;
  counter-increment: linenumber;
  font-family: var(--verso-code-font-family);
}
.syntax-error > .line::before {
  -webkit-user-select: none;
  display: inline-block;
  content: counter(linenumber);
  border-right: 1px solid #ddd;
  width: 2em;
  padding-right: 0.25em;
  margin-right: 0.25em;
  font-family: var(--verso-code-font-family);
  text-align: right;
}

:is(.syntax-error > .line):has(.parse-message)::before {
  color: red;
  font-weight: bold;
}

.syntax-error .parse-message > code.hover-info {
  display:none;
}

.syntax-error .parse-message {
  white-space: pre;
  text-decoration-skip-ink: none;
  color: red;
  font-weight: 600;
}
"
  ]
  extraJs := [
    highlightingJs
  ]
  extraJsFiles := [popperJs, tippyJs]
  extraCssFiles := [tippyCss]
  toHtml :=
    open Verso.Output Html in
    some <| fun _ _ _ data _ => do
      match FromJson.fromJson? data with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code while rendering HTML: " ++ err
        pure .empty
      | .ok (str, (msgs : (Array SyntaxError))) =>
        let mut pos : String.Pos.Raw := ⟨0⟩
        let mut out : Array Html := #[]
        let mut line : Array Html := #[]
        let filemap := FileMap.ofString str
        let mut msgs := msgs.toSubarray
        for lineNum in [1:filemap.getLastLine] do
          pos := filemap.lineStart lineNum
          let lineEnd := (filemap.lineStart (lineNum + 1)).prev str
          repeat
            if h : msgs.size = 0 then break
            else
              let {pos := errPos, endPos, text := errText} := msgs[0]
              let pos' := filemap.ofPosition errPos
              if pos' > lineEnd then break
              let pos'' := filemap.ofPosition endPos

              msgs := msgs.drop 1
              line := line.push <| pos.extract str pos'
              let spanned := pos'.extract str pos''  -- TODO account for cases where the error range spans multiple lines
              -- If the error is just a newline, add a space so there's something to highlight
              let spanned := if spanned.isEmpty || spanned.all (· == '\n') then " " ++ spanned else spanned
              line := line.push {{<span class="parse-message has-info error"><code class="hover-info">{{errText}}</code>{{spanned}}</span>}}
              pos := pos''
          line := line.push <| pos.extract str lineEnd
          out := out.push {{<code class="line">{{line}}</code>}}
          line := #[]
          pos := lineEnd.next str

        pure {{<pre class="syntax-error hl lean">{{out}}</pre>}}


structure SyntaxErrorConfig where
  name : Name
  «show» : Bool := true
  category : Name := `command
  prec : Nat := 0

section
variable [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m]

def SyntaxErrorConfig.parse : ArgParse m SyntaxErrorConfig :=
  SyntaxErrorConfig.mk <$>
    .positional `name (ValDesc.name.as "name for later reference") <*>
    .flag `show true <*>
    .namedD `category (ValDesc.name.as "syntax category (default `command`)") `command <*>
    .namedD `precedence .nat 0

instance : FromArgs SyntaxErrorConfig m := ⟨SyntaxErrorConfig.parse⟩

end

open Lean.Parser in
@[code_block]
def syntaxError : CodeBlockExpanderOf SyntaxErrorConfig
  | config, str => withoutAsync do

    PointOfInterest.save (← getRef) config.name.toString
      (kind := Lsp.SymbolKind.file)
      (detail? := some "Syntax error")

    let s := str.getString
    match runParserCategory' (← getEnv) (← getOptions) config.category s with
    | .ok stx =>
      throwErrorAt str m!"Expected a syntax error for category {config.category}, but got {indentD stx}"
    | .error es =>
      let msgs := es.toList.map fun {pos, endPos, text := msg} =>
        ⟨.error, .text <| mkErrorStringWithPos  "<example>" pos msg (endPos := endPos)⟩

      saveOutputs config.name msgs
      Hover.addCustomHover (← getRef) <| MessageData.joinSep (msgs.map fun ⟨sev, msg⟩ => m!"{sevStr sev.toSeverity}:{indentD msg.toString}") Format.line

      `(Block.other {Block.syntaxError with data := ToJson.toJson ($(quote s), $(quote es))} #[Block.code $(quote s)])
where
  sevStr : MessageSeverity → String
    | .information => "info"
    | .warning => "warning"
    | .error => "error"
