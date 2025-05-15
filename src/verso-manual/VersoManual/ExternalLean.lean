/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso
import VersoManual.Basic
import VersoManual.ExternalLean.Files
import SubVerso.Examples.Messages

set_option linter.missingDocs true

open Lean

open Verso Log Doc Elab ArgParse Genre.Manual Code Output Html Highlighted WebAssets
open SubVerso.Highlighting
open SubVerso.Examples.Messages

open Std

namespace Verso.Genre.Manual.ExternalLean

private def oneCodeStr [Monad m] [MonadError m] (inlines : Array (TSyntax `inline)) : m StrLit := do
  let #[code] := inlines
    | (if inlines.size == 0 then (throwError ·) else (throwErrorAt (mkNullNode inlines) ·)) "Expected one code element"
  let `(inline|code($code)) := code
    | throwErrorAt code "Expected a code element"
  return code

private def oneCodeStr? [Monad m] [MonadError m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
    (inlines : Array (TSyntax `inline)) : m (Option StrLit) := do
  let #[code] := inlines
    | if inlines.size == 0 then
        Lean.logError "Expected a code element"
      else
        logErrorAt (mkNullNode inlines) "Expected one code element"
      return none
  let `(inline|code($code)) := code
    | logErrorAt code "Expected a code element"
      return none
  return some code


private def oneCodeName [Monad m] [MonadError m] (inlines : Array (TSyntax `inline)) : m Ident := do
  let code ← oneCodeStr inlines
  let str := code.getString
  let name := if str.contains '.' then str.toName else Name.str .anonymous str
  return mkIdentFrom code name

section

variable [Monad m] [MonadOptions m] [MonadError m] [MonadLiftT CoreM m]

private def defaultProject : m String := do
  if let some p := verso.exampleProject.get? (← getOptions) then pure p else throwError "No default project specified"

private def defaultModule : m Name := do
  if let some m := verso.exampleModule.get? (← getOptions) then pure m.toName else throwError "No default module specified"

/--
Parses the project directory as a named argument `project`, falling back to the default if specified in the option `verso.exampleProject`.
-/
def projectOrDefault : ArgParse m StrLit :=
  .named `project .strLit false <|>
  (Syntax.mkStrLit <$> .lift "default project" defaultProject) <|>
  .fail none (some m!"No `(project := ...)` argument provided and no default project set.")

/--
Parses the current module as a named argument `module`, falling back to the default if specified in the option `verso.exampleModule`.
-/
def moduleOrDefault : ArgParse m Ident :=
  .named `module .ident false <|>
  (mkIdent <$> .lift "default module" defaultModule) <|>
  .fail none (some m!"No `(module := ...)` argument provided and no default module set.")

/--
A specification of which module to look in to find example code.
-/
structure CodeModuleContext where
  /-- The module's name. -/
  module : Ident

instance : FromArgs CodeModuleContext m where
  fromArgs := CodeModuleContext.mk <$> moduleOrDefault

/--
A specification of which module to look in to find example code, potentially made more specific with
a named anchor.
-/
structure CodeContext extends CodeModuleContext where
  /--
  The relevant `-- ANCHOR: X` to include
  -/
  anchor? : Option Ident

instance : FromArgs CodeContext m where
  fromArgs := CodeContext.mk <$> fromArgs <*> .named `anchor .ident true

/--
A specification of which module to look in to find an example message, with its desired severity,
potentially made more specific with a named anchor.
-/
structure MessageContext extends CodeContext where
  /--
  The desired severity of the message.
  -/
  severity : WithSyntax MessageSeverity

instance : FromArgs MessageContext m where
  fromArgs := (fun s x => MessageContext.mk x s) <$> .positional' `severity <*> fromArgs

/--
A specification of which module to look in to find a quoted name, potentially made more specific with
a named anchor.
-/
structure NameContext extends CodeContext where
  /--
  How to override the display of the name.
  -/
  show? : Option Ident

instance : FromArgs NameContext m where
  fromArgs := NameContext.mk <$> fromArgs <*> .named' `show true

end


block_extension Block.lean (hls : Highlighted) where
  data :=
    let defined := hls.definedNames.toArray
    Json.arr #[ToJson.toJson hls, ToJson.toJson defined]
  traverse _ _ _ := pure none
  toTeX := none
  extraCss := [highlightingStyle]
  extraJs := [highlightingJs]
  extraJsFiles := [("popper.js", popper), ("tippy.js", tippy)]
  extraCssFiles := [("tippy-border.css", tippy.border.css)]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      let .arr #[hlJson, _] := data
        | HtmlT.logError "Expected four-element JSON for Lean code"
          pure .empty
      match FromJson.fromJson? hlJson with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code block while rendering HTML: " ++ err
        pure .empty
      | .ok (hl : Highlighted) =>
        let i := hl.indentation
        let hl := hl.deIndent i
        hl.blockHtml "examples"

inline_extension Inline.lean (hls : Highlighted) where
  data :=
    let defined := hls.definedNames.toArray
    Json.arr #[ToJson.toJson hls, ToJson.toJson defined]
  traverse _ _ _ := pure none
  toTeX := none
  extraCss := [highlightingStyle]
  extraJs := [highlightingJs]
  extraJsFiles := [("popper.js", popper), ("tippy.js", tippy)]
  extraCssFiles := [("tippy-border.css", tippy.border.css)]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ data _ => do
      let .arr #[hlJson, _] := data
        | HtmlT.logError "Expected four-element JSON for Lean code"
          pure .empty
      match FromJson.fromJson? hlJson with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code block while rendering HTML: " ++ err
        pure .empty
      | .ok (hl : Highlighted) =>
        let i := hl.indentation
        let hl := hl.deIndent i
        hl.inlineHtml "examples"

block_extension Block.leanOutput (severity : MessageSeverity) (message : String) (summarize : Bool := false) where
  data := ToJson.toJson (severity, message, summarize)
  traverse _ _ _ := do
    pure none
  toTeX :=
    some <| fun _ go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  extraCss := [highlightingStyle]
  extraJs := [highlightingJs]
  extraJsFiles := [("popper.js", popper), ("tippy.js", tippy)]
  extraCssFiles := [("tippy-border.css", tippy.border.css)]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      match FromJson.fromJson? data with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code while rendering HTML: " ++ err
        pure .empty
      | .ok ((sev, txt, summarize) : MessageSeverity × String × Bool) =>
        let wrap html :=
          if summarize then {{<details><summary>"Expand..."</summary>{{html}}</details>}}
          else html
        pure <| wrap {{<div class={{sev.class}}><pre>{{txt}}</pre></div>}}

inline_extension Inline.leanOutput (severity : MessageSeverity) (message : String) (plain : Bool) where
  data := ToJson.toJson (severity, message, plain)
  traverse _ _ _ := do
    pure none
  toTeX :=
    some <| fun go _ _  content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  extraCss := [highlightingStyle]
  extraJs := [highlightingJs]
  extraJsFiles := [("popper.js", popper), ("tippy.js", tippy)]
  extraCssFiles := [("tippy-border.css", tippy.border.css)]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ data _ => do
      match FromJson.fromJson? data with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code while rendering HTML: " ++ err
        pure .empty
      | .ok ((sev, txt, plain) : MessageSeverity × String × Bool) =>
        let plainHtml := {{<code>{{txt}}</code>}}
        if plain then pure plainHtml
        else pure {{<span class={{sev.class}}>{{plainHtml}}</span>}}

/--
Adds up to 10 suggestions.

`loc` is the location at which the edit should occur, `candidates` are the valid inputs, and `input`
is the provided input. Suggestions are added if they are "sufficiently close" to the input.

A suggestion is sufficiently close if
 * the input is shorter than 5 and their Levenshtein distance is 1 or less,
 * the input is shorter than 10 and their distance is 2 or less, or
 * the distance is shorter than 3
-/
def smartSuggestions (loc : Syntax) (candidates : Array String) (input : String) : DocElabM Unit :=
  let threshold := if input.length < 5 then 1 else if input.length < 10 then 2 else 3
  let toks := candidates.filterMap fun t =>
    EditDistance.levenshtein t input threshold <&> (t, ·)
  let toks := toks.qsort (fun x y => x.2 < y.2 || (x.2 == y.2 && x.1 < y.1))
  let toks := toks.take 10
  -- TODO test thresholds/sorting
  for (t, _) in toks do
    Suggestion.saveSuggestion loc t t


/--
Adds a newline to a string if it doesn't already end with one.
-/
def withNl (s : String) : String := if s.endsWith "\n" then s else s ++ "\n"

/-- Converts all warnings to errors. -/
def warningsToErrors (hl : Highlighted) : Highlighted :=
  match hl with
  | .seq xs => .seq <| xs.map warningsToErrors
  | .point .warning str => .point .error str
  | .point .. => hl
  | .tactics info start stop x => .tactics info start stop <| warningsToErrors x
  | .span infos x => .span (infos.map fun (k, str) => (if k matches .warning then .error else k, str)) (warningsToErrors x)
  | .text .. | .token .. => hl

/-- Extracts all messages from the given code. -/
def allInfo (hl : Highlighted) : Array (MessageSeverity × String × Option Highlighted) :=
  match hl with
  | .seq xs => xs.flatMap allInfo
  | .point k str => #[(toSev k, str, none)]
  | .tactics _ _ _ x => allInfo x
  | .span infos x => (infos.map fun (k, str) => (toSev k, str, some x)) ++ allInfo x
  | .text .. | .token .. => #[]
where
  toSev : Highlighted.Span.Kind → MessageSeverity
    | .error => .error
    | .info => .information
    | .warning => .warning

/--
Loads the contents of a module, parsed by anchor. The results are cached.
-/
def anchored
    [Monad m] [MonadEnv m] [MonadLift IO m] [MonadError m] [MonadOptions m]
    [MonadTrace m] [AddMessageContext m] [MonadAlwaysExcept ε m] [MonadFinally m]
    (moduleName : Ident) (blame : Syntax) :
    m Highlighted.AnchoredExamples := do
  let modName := moduleName.getId
  let modStr := modName.toString

  if let some cached := (loadedModuleAnchorExt.getState (← getEnv)).find? modName then return cached

  let items ← loadModuleContent modStr
  let highlighted := Highlighted.seq (items.map (·.code))

  match highlighted.anchored with
  | .error e => throwErrorAt blame e
  | .ok anchors => return anchors

/--
Includes the contents of the specified example module.
-/
@[code_block_expander module]
def module : CodeBlockExpander
  | args, code => withTraceNode `Elab.Verso (fun _ => pure m!"module") <| do
    let {module := moduleName, anchor?} ← parseThe CodeContext args
    let modStr := moduleName.getId.toString
    let items ← loadModuleContent modStr
    if let some anchor := anchor? then
      try
        let {anchors, ..} ← anchored moduleName anchor
        if let some hl := anchors[anchor.getId.toString]? then
          let _ ← ExpectString.expectString "module contents" code (hl.toString |> withNl)
            (useLine := fun l => !l.trim.isEmpty)
          for (sev, msg, _) in allInfo hl do
            logSilentInfo m!"{sevStr sev}:\n{msg}"
          return #[← ``(Block.other (Block.lean $(quote hl)) #[])]
        else
          logErrorAt anchor "Anchor not found"
          for x in anchors.keys do
            Suggestion.saveSuggestion anchor x x
          return #[]
      catch
        | .error ref e =>
          logErrorAt ref e
          return #[← ``(sorryAx _ true)]
        | e => throw e
    else
      let highlighted := Highlighted.seq (items.map (·.code))
      let _ ← ExpectString.expectString "module contents" code (highlighted.toString |> withNl)
        (useLine := fun l => !l.trim.isEmpty)
      for (sev, msg, _) in allInfo highlighted do
        logSilentInfo m!"{sevStr sev}:\n{msg}"
      return #[← ``(Block.other (Block.lean $(quote highlighted)) #[])]
where
  sevStr
    | .error => "error"
    | .warning => "warning"
    | .information => "info"

macro_rules
  | `(block|```anchor $arg:arg_val $args* | $s ```) =>
    `(block|```module anchor:=$arg $args* | $s ```)
  | `(block|```%$tok anchor $args* | $_s ```) =>
    Macro.throwErrorAt (mkNullNode (#[tok] ++ args)) "Expected a positional identifier as first argument"

/--
Includes the contents of the specified example module.
-/
@[role_expander module]
def moduleInline : RoleExpander
  | args, inls => withTraceNode `Elab.Verso (fun _ => pure m!"moduleInline") <| do
    let {module := moduleName, anchor?} ← parseThe CodeContext args
    let code? ← oneCodeStr? inls

    let modStr := moduleName.getId.toString
    let items ← loadModuleContent modStr
    let highlighted := Highlighted.seq (items.map (·.code))

    if let some anchor := anchor? then
      try
        let {anchors, ..} ← anchored moduleName anchor
        if let some hl := anchors[anchor.getId.toString]? then
          if let some code := code? then
            let _ ← ExpectString.expectString "code" code (hl.toString.trim)

            for (sev, msg, _) in allInfo hl do
              logSilentInfo m!"{sevStr sev}:\n{msg}"

          return #[← ``(Inline.other (Inline.lean $(quote hl)) #[])]
        else
          logErrorAt anchor "Anchor not found"
          for x in anchors.keys do
            Suggestion.saveSuggestion anchor x x
          return #[]
      catch
        | .error ref e =>
          logErrorAt ref e
          return #[← ``(sorryAx _ true)]
        | e => throw e
    else
      return #[← ``(Inline.other (Inline.lean $(quote highlighted)) #[])]
where
  sevStr
    | .error => "error"
    | .warning => "warning"
    | .information => "info"

macro_rules
  | `(inline|role{ anchor $arg:arg_val $args* } [%$t1 $s ]%$t2) =>
    `(inline|role{ module anchor:=$arg $args* } [%$t1 $s ]%$t2)
  | `(inline|role{%$tok anchor $args* } [ $_s ]) =>
    Macro.throwErrorAt (mkNullNode (#[tok] ++ args)) "Expected a positional identifier as first argument"

private partial def allTokens (hl : Highlighted) : HashSet String :=
  match hl with
  | .seq xs => xs.map allTokens |>.foldl (init := {}) HashSet.union
  | .point .. | .text .. => {}
  | .tactics _ _ _ x | .span _ x => allTokens x
  | .token ⟨_, s⟩ => {s}

private partial def allNames (hl : Highlighted) : HashSet String :=
  match hl with
  | .seq xs => xs.map allTokens |>.foldl (init := {}) HashSet.union
  | .point .. | .text .. => {}
  | .tactics _ _ _ x | .span _ x => allTokens x
  | .token ⟨.var .., s⟩ | .token ⟨.const .., s⟩ => {s}
  | .token _ => {}

/--
Quotes the first instance of the given name from the module.
-/
@[role_expander moduleName]
def moduleName : RoleExpander
  | args, inls => withTraceNode `Elab.Verso (fun _ => pure m!"moduleName") <| do
    let {module := moduleName, anchor?, show?} ← parseThe NameContext args
    let name ← oneCodeStr inls
    let nameStr := name.getString

    let modStr := moduleName.getId.toString
    let items ← loadModuleContent modStr
    let highlighted := Highlighted.seq (items.map (·.code))
    let fragment ←
      if let some anchor := anchor? then
        try
          let {anchors, ..} ← anchored moduleName anchor
          if let some hl := anchors[anchor.getId.toString]? then
            pure hl
          else
            logErrorAt anchor "Anchor not found"
            for x in anchors.keys do
              Suggestion.saveSuggestion anchor x x
            return #[← ``(sorryAx _ true)]
          catch
            | .error ref e => logErrorAt ref e; return #[← ``(sorryAx _ true)]
            | e => throw e
      else pure highlighted

    if let some tok@⟨k, _txt⟩ := fragment.matchingName? nameStr then
      let tok := show?.map (⟨k, ·.getId.toString⟩) |>.getD tok
      return #[← ``(Inline.other (Inline.lean $(quote (Highlighted.token tok))) #[])]
    else
      logErrorAt name m!"'{nameStr}' not found in:{indentD fragment.toString}"
      -- TODO test thresholds/sorting
      smartSuggestions name (allNames fragment |>.toArray) nameStr
      return #[← ``(sorryAx _ true)]

macro_rules
  | `(inline|role{%$rs anchorName $a:arg_val $arg* }%$re [%$s $str* ]%$e) =>
    `(inline|role{%$rs moduleName $arg*  anchor:=$a }%$re [%$s $str* ]%$e)

/--
Quotes the first term that matches the provided string.
-/
@[role_expander moduleTerm]
def moduleTerm : RoleExpander
  | args, inls => withTraceNode `Elab.Verso (fun _ => pure m!"moduleTerm") <| do
    let {module := moduleName, anchor?} ← parseThe CodeContext args
    let term ← oneCodeStr inls

    let modStr := moduleName.getId.toString
    let items ← loadModuleContent modStr
    let highlighted := Highlighted.seq (items.map (·.code))
    let fragment ←
      if let some anchor := anchor? then
        try
          let {anchors, ..} ← anchored moduleName anchor
          if let some hl := anchors[anchor.getId.toString]? then
            pure hl
          else
            logErrorAt anchor "Anchor not found"
            for x in anchors.keys do
              Suggestion.saveSuggestion anchor x x
            return #[← ``(sorryAx _ true)]
        catch
          | .error ref e => logErrorAt ref e; return #[← ``(sorryAx _ true)]
          | e => throw e
      else pure highlighted

      if let some e := fragment.matchingExpr? term.getString then
        return #[← ``(Inline.other (Inline.lean $(quote e)) #[])]
      else
        logErrorAt term m!"Not found: '{term.getString}' in{indentD fragment.toString}"
        return #[← ``(sorryAx _ true)]

macro_rules
  | `(inline|role{%$rs anchorTerm $a:arg_val $arg* }%$re [%$s $str* ]%$e) =>
    `(inline|role{%$rs moduleTerm $arg*  anchor:=$a }%$re [%$s $str* ]%$e)

private def severityName {m} [Monad m] [MonadEnv m] [MonadResolveName m] : MessageSeverity → m String
  | .error => unresolveNameGlobal ``MessageSeverity.error <&> (·.toString)
  | .warning => unresolveNameGlobal ``MessageSeverity.warning <&> (·.toString)
  | .information => unresolveNameGlobal ``MessageSeverity.information <&> (·.toString)

deriving instance Repr for MessageSeverity

/--
Displays output from the example module.
-/
@[code_block_expander moduleOut]
def moduleOut : CodeBlockExpander
  | args, str => withTraceNode `Elab.Verso (fun _ => pure m!"moduleOut") <| do
    let {module := moduleName, anchor?, severity} ← parseThe MessageContext args

    let modStr := moduleName.getId.toString
    let items ← loadModuleContent modStr
    let highlighted := Highlighted.seq (items.map (·.code))
    let fragment ←
      if let some anchor := anchor? then
        try
          let {anchors, ..} ← anchored moduleName anchor
          if let some hl := anchors[anchor.getId.toString]? then
            pure hl
          else
            logErrorAt anchor "Anchor not found"
            for x in anchors.keys do
              Suggestion.saveSuggestion anchor x x
            return #[← ``(sorryAx _ true)]
        catch
          | .error ref e => logErrorAt ref e; return #[← ``(sorryAx _ true)]
          | e => throw e
      else pure highlighted

    let infos : Array _ := allInfo fragment

    for (sev, msg, _) in infos do
      if messagesMatch msg str.getString then
        if sev == severity.1 then
          return #[← ``(Block.other (Block.leanOutput $(quote sev) $(quote msg)) #[])]
        else
        let wanted ← severityName sev
          if severity.2.getHeadInfo matches .original .. then
            Suggestion.saveSuggestion severity.2 wanted wanted
          throwError "Mismatched severity. Expected '{repr severity.1}', got '{wanted}'."

    -- Didn't find it. Add suggestions.
    for (_, msg, _) in infos do
      Suggestion.saveSuggestion str (ExpectString.abbreviateString msg) (withNl msg)

    let err := m!"Expected one of:{indentD (m!"\n".joinSep <| infos.toList.map (·.2.1))}\nbut got:{indentD str.getString}"
    logErrorAt str err

    return #[← ``(sorryAx _ true)]

macro_rules
  | `(block|```moduleInfo $arg* | $s ```) =>
    `(block|```moduleOut MessageSeverity.information $arg* | $s ```)
  | `(block|```moduleError $arg* | $s ```) =>
    `(block|```moduleOut MessageSeverity.error $arg* | $s ```)
  | `(block|```moduleWarning $arg* | $s ```) =>
    `(block|```moduleOut MessageSeverity.warning $arg* | $s ```)
  | `(block|```anchorInfo $a:arg_val $arg* | $s ```) =>
    `(block|```moduleOut MessageSeverity.information anchor:=$a $arg* | $s ```)
  | `(block|```anchorError $a:arg_val $arg* | $s ```) =>
    `(block|```moduleOut MessageSeverity.error anchor:=$a $arg* | $s ```)
  | `(block|```anchorWarning $a:arg_val $arg* | $s ```) =>
    `(block|```moduleOut MessageSeverity.warning anchor:=$a $arg* | $s ```)

@[role_expander moduleOut, inherit_doc moduleOut]
def moduleOutRole : RoleExpander
  | args, inls => withTraceNode `Elab.Verso (fun _ => pure m!"moduleOutRole") <| do
    let str? ← oneCodeStr? inls

    let {module := moduleName, anchor?, severity} ← parseThe MessageContext args

    let modStr := moduleName.getId.toString
    let items ← loadModuleContent modStr
    let highlighted := Highlighted.seq (items.map (·.code))
    let fragment ←
      if let some anchor := anchor? then
        try
          let {anchors, ..} ← anchored moduleName anchor
          if let some hl := anchors[anchor.getId.toString]? then
            pure hl
          else
            logErrorAt anchor "Anchor not found"
            for x in anchors.keys do
              Suggestion.saveSuggestion anchor x x
            return #[← ``(sorryAx _ true)]
        catch
          | .error ref e => logErrorAt ref e; return #[← ``(sorryAx _ true)]
          | e => throw e
      else pure highlighted

    let infos := allInfo fragment

    if let some str := str? then
      for (sev, msg, _) in infos do
        if messagesMatch msg str.getString then
          if sev == severity.1 then
            return #[← ``(Inline.other (Inline.leanOutput $(quote sev) $(quote msg) true) #[])]
          else
          let wanted ← severityName sev
            if severity.2.getHeadInfo matches .original .. then
              Suggestion.saveSuggestion severity.2 wanted wanted
            throwError "Mismatched severity. Expected '{repr severity.1}', got '{wanted}'."

      -- Didn't find it. Add suggestions.
      for (_, msg, _) in infos do
        Suggestion.saveSuggestion str (quoteCode <| ExpectString.abbreviateString msg.trim) msg.trim

      let err := m!"Expected one of:{indentD (m!"\n".joinSep <| infos.toList.map (·.2.1))}\nbut got:{indentD str.getString}"
      logErrorAt str err
    else
      let err := m!"Expected one of:{indentD (m!"\n".joinSep <| infos.toList.map (·.2.1))}"
      Lean.logError m!"No expected term provided. {err}"
      if let `(inline|role{$_ $_*} [%$tok1 $contents* ]%$tok2) := (← getRef) then
        let stx :=
          if tok1.getHeadInfo matches .original .. && tok2.getHeadInfo matches .original .. then
            mkNullNode #[tok1, tok2]
          else mkNullNode contents
        for (_, msg, _) in infos do
          Suggestion.saveSuggestion stx (quoteCode <| ExpectString.abbreviateString msg.trim) (quoteCode msg.trim)

    return #[← ``(sorryAx _ true)]

where
  quoteCode (str : String) : String := Id.run do
    let str := if str.startsWith "`" || str.endsWith "`" then " " ++ str ++ " " else str
    let mut n := 1
    let mut run := none
    let mut iter := str.iter
    while h : iter.hasNext do
      let c := iter.curr' h
      iter := iter.next
      if c == '`' then
        run := some (run.getD 0 + 1)
      else if let some k := run then
        if k > n then n := k
        run := none

    let delim := String.mk (List.replicate n '`')
    return delim ++ str ++ delim

macro_rules
  | `(inline|role{%$rs moduleInfo $arg*}%$re [%$s $str* ]%$e) =>
    `(inline|role{%$rs moduleOut MessageSeverity.information $arg*}%$re [%$s $str* ]%$e)
  | `(inline|role{%$rs moduleError $arg*}%$re [%$s $str* ]%$e) =>
    `(inline|role{%$rs moduleOut MessageSeverity.error $arg*}%$re [%$s $str* ]%$e)
  | `(inline|role{%$rs moduleWarning $arg*}%$re [%$s $str* ]%$e) =>
    `(inline|role{%$rs moduleOut MessageSeverity.warning $arg*}%$re [%$s $str* ]%$e)
  | `(inline|role{%$rs anchorInfo $a:arg_val $arg*}%$re [%$s $str* ]%$e) =>
    `(inline|role{%$rs moduleOut MessageSeverity.information anchor:=$a $arg*}%$re [%$s $str* ]%$e)
  | `(inline|role{%$rs anchorError $a:arg_val $arg*}%$re [%$s $str* ]%$e) =>
    `(inline|role{%$rs moduleOut MessageSeverity.error anchor:=$a $arg*}%$re [%$s $str* ]%$e)
  | `(inline|role{%$rs anchorWarning $a:arg_val $arg*}%$re [%$s $str* ]%$e) =>
    `(inline|role{%$rs moduleOut MessageSeverity.warning anchor:=$a $arg*}%$re [%$s $str* ]%$e)
