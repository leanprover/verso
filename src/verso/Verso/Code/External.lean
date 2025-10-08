/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso.Doc
import Verso.Doc.ArgParse
import Verso.Doc.Elab
import Verso.Code.External.Env
import Verso.Code.External.Files
import Verso.EditDistance
import Verso.ExpectString
import Verso.Doc.Suggestion
import Verso.Hint
import Verso.Log

import SubVerso.Highlighting
import SubVerso.Examples.Messages

import Lean.Message
import Lean.Meta.Hint
import Lean.DocString.Syntax

import Std.Data.HashSet

open Verso Doc Elab Log ArgParse
open SubVerso Highlighting Examples.Messages
open Lean Meta Hint
open Std
open Lean.Doc.Syntax

namespace Verso.Code.External

register_option verso.examples.suggest : Bool := {
  defValue := false,
  descr := "Whether to suggest potentially-matching code examples"
}

structure CodeConfig where
  /-- Whether to render proof states -/
  showProofStates : Bool := true
  /--
  Whether to treat names defined in the code as link targets.

  If unspecified, the block or inline element in question may fall back to a default value.
  -/
  defSite : Option Bool := none
deriving DecidableEq, Ord, Repr, Quote, ToExpr, ToJson, FromJson

/--
A genre that supports loading and displaying external Lean code samples.
-/
class ExternalCode (genre : Genre) where
  /-- An inline element for rendering Lean code. -/
  leanInline : Highlighted → CodeConfig → Inline genre
  /-- A block element for rendering Lean code. -/
  leanBlock : Highlighted → CodeConfig → Block genre
  /--
  An inline element for rendering Lean messages. `plain` should suppress the annotation of the
  output with its message severity.
  -/
  leanOutputInline (message : Highlighted.Message) (plain : Bool) (expandTraces : List Lean.Name := []) : Inline genre
  /-- A block element for rendering Lean messages. -/
  leanOutputBlock (message : Highlighted.Message) (summarize : Bool := false) (expandTraces : List Lean.Name := []) : Block genre

open ExternalCode

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
  .fail none (some "No `(project := ...)` argument provided and no default project set.")

/--
Parses the current module as a named argument `module`, falling back to the default if specified in the option `verso.exampleModule`.
-/
def moduleOrDefault : ArgParse m Ident :=
  .named `module .ident false <|>
  (mkIdent <$> .lift "default module" defaultModule) <|>
  .fail none (some "No `(module := ...)` argument provided and no default module set.")

/--
A specification of which module to look in to find example code.
-/
structure CodeModuleContext extends CodeConfig where
  /-- The module's name. -/
  module : Ident
  /-- The path at which the module's project is found -/
  project : StrLit

instance : FromArgs CodeModuleContext m where
  fromArgs := ((·, ·, ·, ·) <$> moduleOrDefault <*> projectOrDefault <*> .flag `showProofStates true <*> .flag `defSite true) <&> fun (m, p, s, d) =>
    ({module := m, project := p, showProofStates := s, defSite := d})

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
  /--
  Traces classes to show expanded by default
  -/
  expandTraces : List Lean.Name
  /--
  Only show the first trace with this title
  -/
  onlyTrace : Option String

private partial def many (p : ArgParse m α) : ArgParse m (List α) :=
  (· :: ·) <$> p <*> many p <|> pure []

instance : FromArgs MessageContext m where
  fromArgs := (fun s ts t x => MessageContext.mk x s ts t) <$> .positional' `severity <*> many (.named `expandTrace .name false) <*> (.named `onlyTrace .string true) <*> fromArgs

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


/--
Adds a newline to a string if it doesn't already end with one.
-/
def withNl (s : String) : String := if s.endsWith "\n" then s else s ++ "\n"

/--
Default suggestion threshold function: a suggestion is sufficiently close if
 * the input is shorter than 5 and their Levenshtein distance is 1 or less,
 * the input is shorter than 10 and their distance is 2 or less, or
 * the distance is shorter than 3.
-/
def suggestionThreshold (input _candidate : String) := if input.length < 5 then 1 else if input.length < 10 then 2 else 3

/--
Adds up to `count` suggestions.

`loc` is the location at which the edit should occur, `candidates` are the valid inputs, and `input`
is the provided input. Suggestions are added if they are "sufficiently close" to the input, as
determined by `threshold`.
-/
def smartSuggestions (candidates : Array String) (input : String) (count : Nat := 10) (threshold := suggestionThreshold) : Array String :=
  let toks := candidates.filterMap fun t =>
    let limit := threshold input t
    EditDistance.levenshtein t input limit <&> (t, ·)
  let toks := toks.qsort (fun x y => x.2 < y.2 || (x.2 == y.2 && x.1 < y.1))
  let toks := toks.take count
  -- TODO test thresholds/sorting
  toks.map fun (t, _) => t

/-- Converts all warnings to errors. -/
def warningsToErrors (hl : Highlighted) : Highlighted :=
  match hl with
  | .seq xs => .seq <| xs.map warningsToErrors
  | .point .warning str => .point .error str
  | .point .. => hl
  | .tactics info start stop x => .tactics info start stop <| warningsToErrors x
  | .span infos x => .span (infos.map fun (k, str) => (if k matches .warning then .error else k, str)) (warningsToErrors x)
  | .text .. | .token .. | .unparsed .. => hl

/-- Extracts all messages from the given code. -/
def allInfo (hl : Highlighted) : Array (Highlighted.Message × Option Highlighted) :=
  match hl with
  | .seq xs => xs.flatMap allInfo
  | .point k str => #[(⟨k, str⟩, none)]
  | .tactics _ _ _ x => allInfo x
  | .span infos x => (infos.map fun (k, str) => (⟨k, str⟩, some x)) ++ allInfo x
  | .text .. | .token .. | .unparsed .. => #[]
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
    [MonadTrace m] [AddMessageContext m] [MonadAlwaysExcept ε m] [MonadFinally m] [MonadQuotation m]
    (project : StrLit) (moduleName : Ident) (blame : Syntax) :
    m Highlighted.AnchoredExamples := do
  let projectPath := project.getString
  let modName := moduleName.getId
  let modStr := modName.toString
  let suppress ← getSuppress

  if let some cached := (loadedModuleAnchorExt.getState (← getEnv))[projectPath]?.getD {} |>.find? modName then
    if let some cached' := cached[suppress]? then
      return cached'

  let items ← loadModuleContent project modStr
  let highlighted := Highlighted.seq (items.map (·.code))

  match highlighted.anchored with
  | .error e => throwErrorAt blame e
  | .ok anchors =>
    modifyEnv fun env => loadedModuleAnchorExt.modifyState env fun mods =>
      mods.alter projectPath fun mods =>
        let mods := mods.getD {}
        let v := (mods.find? modName).getD {}
        some <| mods.insert modName (v.insert suppress anchors)
    return anchors

open MessageData (hint)


local instance : Coe (Array String) (Array Suggestion) where
  coe xs := xs.map ({suggestion := .string ·})

/--
Reports a missing anchor error.
-/
def anchorNotFound (anchorName : Ident) (allAnchors : List String) : DocElabM Term := do
  let anchorStr := anchorName.getId.toString

  let toSuggest := allAnchors.filterMap fun x =>
    EditDistance.levenshtein anchorStr x 30 <&> (·, x)

  let toSuggest := toSuggest.toArray.qsort (fun x y => x.1 < y.1) |>.map (·.snd)
  let h ←
    if toSuggest.isEmpty then pure m!"No anchors defined in module."
    else hintAt anchorName "Use a defined anchor" toSuggest
  logErrorAt anchorName m!"Anchor not found.\n\n{h}"
  ``(sorryAx _ true)

private def sevStr : MessageSeverity → String
  | .error => "error"
  | .warning => "warning"
  | .information => "info"


/--
Silently logs all the messages in `hl`.
-/
def logInfos (hl : Highlighted) : DocElabM Unit := do
  for (⟨sev, msg⟩, _) in allInfo hl do
    logSilentInfo m!"{sev}:\n{msg.toString}"

/--
Given a module name and an anchor name, loads the resulting code and invokes `k` on it, failing if
the code can't be found.
-/
def withAnchored (project : StrLit) (moduleName : Ident) (anchor? : Option Ident)
    (k : Highlighted → DocElabM (Array Term)) : DocElabM (Array Term) := do
  if let some anchor := anchor? then
    try
      let {anchors, ..} ← anchored project moduleName anchor
      if let some hl := anchors[anchor.getId.toString]? then
        k hl
      else
        return #[← anchorNotFound anchor anchors.keys]
    catch
      | .error ref e => logErrorAt ref e; return #[← ``(sorryAx _ true)]
      | e => throw e
  else
    let {code, ..} ← anchored project moduleName moduleName
    k code

-- TODO: public API? Or something higher level that constructs the hint?
private def editCodeBlock [Monad m] [MonadFileMap m] (stx : Syntax) (newContents : String) : m (Option String) := do
  let txt ← getFileMap
  let some rng := stx.getRange?
    | pure none
  let { start := {line := l1, ..}, .. } := txt.utf8RangeToLspRange rng
  let line1 := txt.source.extract (txt.lineStart (l1 + 1)) (txt.lineStart (l1 + 2))
  let line1ws := line1.takeWhile (· == ' ')
  let line1rest := line1.drop line1ws.length
  let newContents := line1ws ++ (withNl newContents).replace "\n" ("\n" ++ line1ws)
  if line1rest.startsWith "```" then
    return some s!"{delims}{line1rest.dropWhile (· == '`') |>.trim}\n{withNl newContents}{delims}"
  else
    return none
where
  delims : String := Id.run do
    let mut n := 3
    let mut run := none
    let mut iter := newContents.iter
    while h : iter.hasNext do
      let c := iter.curr' h
      iter := iter.next
      if c == '`' then
        run := some (run.getD 0 + 1)
      else if let some k := run then
        if k > n then n := k
        run := none
    if let some k := run then
      if k > n then n := k
    n.fold (fun _ _ s => s.push '`') ""

def moduleContentBlock (args : Array Arg) (code : StrLit) : DocElabM (Array Term) := do
    let cfg@{ module := moduleName, project, anchor?, showProofStates := _, defSite := _ } ← parseThe CodeContext args
    withAnchored project moduleName anchor? fun hl => do
      logInfos hl
      let hlString := hl.toString
      if code.getString.trim.isEmpty && !hlString.trim.isEmpty then
        let ref ← getRef
        let h ←
          if let some s ← editCodeBlock ref hlString then
            hint m!"" #[s]
          else pure m!""
        logErrorAt ref <| m!"Missing code." ++ h
      else if let some mismatch ← ExpectString.expectStringOrDiff code (hlString |> withNl) (useLine := fun l => !l.trim.isEmpty) then
        let ref ← getRef
        let h ←
          if let some s ← editCodeBlock ref hlString then
            hint m!"" #[s]
          else pure m!""
        logErrorAt code <| m!"Mismatched code:{indentD mismatch}" ++ h
      pure #[← ``(leanBlock $(quote hl) $(quote cfg.toCodeConfig))]


/--
Includes the contents of the specified example module.

Requires that the genre have an `ExternalCode` instance.
-/
@[code_block_expander module]
def module : CodeBlockExpander
  | args, code => withTraceNode `Elab.Verso (fun _ => pure m!"module") <| do
    moduleContentBlock args code

/--
Includes the contents of the specified anchored example.

Requires that the genre have an `ExternalCode` instance.
-/
@[code_block_expander anchor]
def anchor : CodeBlockExpander
  | args, code => withTraceNode `Elab.Verso (fun _ => pure m!"anchor") <| do
    if let some (Arg.anon a) := args[0]? then
      moduleContentBlock (#[.named .missing (mkIdent `anchor) a] ++ args.drop 1) code
    else
      throwError "Expected a positional argument first (the anchor name)"

def moduleInline (args : Array Arg) (inls : TSyntaxArray `inline) : DocElabM (Array Term) := do
  let cfg@{module := moduleName, project, anchor?, showProofStates := _, defSite := _} ← parseThe CodeContext args
  let code? ← oneCodeStr? inls

  withAnchored project moduleName anchor? fun hl => do
    logInfos hl
    if let some code := code? then
      let _ ← ExpectString.expectString "code" code (hl.toString.trim)

    pure #[← ``(leanInline $(quote hl) $(quote cfg.toCodeConfig))]


/--
Includes the contents of the specified anchor.

Requires that the genre have an `ExternalCode` instance.
-/
@[role_expander module]
def moduleInlineRole : RoleExpander
  | args, inls => withTraceNode `Elab.Verso (fun _ => pure m!"moduleInlineRole") <| do
    moduleInline args inls

@[role_expander anchor]
def anchorInlineRole : RoleExpander
  | args, inls => withTraceNode `Elab.Verso (fun _ => pure m!"anchorInlineRole") <| do
    if let some (Arg.anon a) := args[0]? then
      moduleInline (#[.named .missing (mkIdent `anchor) a] ++ args.drop 1) inls
    else
      throwError "Expected a positional argument first (the anchor name)"

private partial def allTokens (hl : Highlighted) : HashSet String :=
  match hl with
  | .seq xs => xs.map allTokens |>.foldl (init := {}) HashSet.union
  | .point .. | .text .. | .unparsed .. => {}
  | .tactics _ _ _ x | .span _ x => allTokens x
  | .token ⟨_, s⟩ => {s}

private partial def allNames (hl : Highlighted) : HashSet String :=
  match hl with
  | .seq xs => xs.map allTokens |>.foldl (init := {}) HashSet.union
  | .point .. | .text .. | .unparsed .. => {}
  | .tactics _ _ _ x | .span _ x => allTokens x
  | .token ⟨.var .., s⟩ | .token ⟨.const .., s⟩ => {s}
  | .token _ => {}

private def tokenHover : Token → Option String
  | ⟨.const _ sig doc? _, _⟩ => some (mkHover sig doc?)
  | ⟨.var _ ty, s⟩ => some (mkHover s!"{s} : {ty}" none)
  | _ => none
where mkHover (sig : String) (doc? : Option String) : String :=
  s!"```{sig}```" ++
  if let some d := doc? then
    s!"\n\n----------\n\n{d}"
  else ""

def moduleNameInline (args : Array Arg) (inls : TSyntaxArray `inline) : DocElabM (Array Term) := do
  let cfg@{module := moduleName, project, anchor?, show?, showProofStates := _, defSite := _} ← parseThe NameContext args
  let name ← oneCodeStr inls
  let nameStr := name.getString

  withAnchored project moduleName anchor? fun hl => do
    if let some tok@⟨k, _txt⟩ := hl.matchingName? nameStr then

      let tok := show?.map (⟨k, ·.getId.toString⟩) |>.getD tok
      if let some h := tokenHover tok then
        Hover.addCustomHover name (.markdown h)
      return #[← ``(leanInline $(quote (Highlighted.token tok)) $(quote cfg.toCodeConfig))]
    else
      -- TODO test thresholds/sorting
      let ss := smartSuggestions (allNames hl |>.toArray) nameStr
      let h ←
        if ss.isEmpty then pure m!""
        else hintAt name "Use a known name" ss
      logErrorAt name m!"'{nameStr}' not found in:{indentD <| ExpectString.abbreviateString (maxLength := 100) hl.toString}{h}"

      return #[← ``(sorryAx _ true)]

/--
Quotes the first instance of the given name from the module.

Requires that the genre have an `ExternalCode` instance.
-/
@[role_expander moduleName]
def moduleName : RoleExpander
  | args, inls => withTraceNode `Elab.Verso (fun _ => pure m!"moduleName") <| moduleNameInline args inls

/--
Quotes the first instance of the given name from the anchor.

Requires that the genre have an `ExternalCode` instance.
-/
@[role_expander anchorName]
def anchorName : RoleExpander
  | args, inls =>
    withTraceNode `Elab.Verso (fun _ => pure m!"moduleName") <|
    if let some (Arg.anon a) := args[0]? then
      moduleNameInline (#[.named .missing (mkIdent `anchor) a] ++ args.drop 1) inls
    else
      throwError "Expected a positional argument first (the anchor name)"


private def suggestTerms (hl : Highlighted) (input : String) : Array String := Id.run do
  let delimTokens : Array String := #["def", "axiom", "example", "theorem", ":=", "inductive", "where", "structure", "class", "instance"]

  -- Avoid performance issues with processing very large documents
  let hl := hl.take 1000

  let ns := allTokens hl |>.filter (· ∉ #[":", "[", "]", "=>", "match", "(", ")", "{", "}", ",", "with", ":=", "=", "by", "#[", ";", "@", "if", "then", "else"] ++ delimTokens)

  let lines := hl.lines.map (·.toString.trim) |>.filter (·.any (· ∉ [' ', '(', ')', '=', ':']))

  let tms := hl.split (· ∈ delimTokens) |>.filterMap fun h => do
    let more := h.split (· == "=") |>.map (·.toString)
    let s := h.toString.trim
    let s := if let some s' := s.dropPrefix? ": " then s'.toString.trimLeft else s
    guard (s.length < 80)
    return #[s] ++ if more.size > 1 then more.map (fun x => (x.dropPrefix? ": " |>.map (·.toString)).getD "") else #[]
  let tms := tms.flatten
  let out := ns.insertMany tms
  lines ++ (smartSuggestions out.toArray input (threshold := (max ·.length ·.length)) (count := 15))


def moduleTermInline (args : Array Arg) (inls : TSyntaxArray `inline) : DocElabM (Array Term) := do
  let cfg@{module := moduleName, project, anchor?, showProofStates := _, defSite := _} ← parseThe CodeContext args
  let term ← oneCodeStr inls

  withAnchored project moduleName anchor? fun hl => do
    if term.getString.trim.isEmpty then
      let suggs := suggestTerms hl term.getString
      let h ← hintAt term "Use one of these" suggs
      let expectedString := ExpectString.abbreviateString (maxLength := 100) <| hl.toString
      let mut msg := m!"No expected term provided.\n"
      msg := msg ++ m!"in:{indentD <| m!"\n".joinSep <| (m!"{·}") <$> expectedString.splitOn "\n"}"
      msg := msg ++ h
      logErrorAt term msg
      return #[← ``(sorryAx _ true)]
    else if let some e := hl.matchingExpr? term.getString then
      logInfos e
      return #[← ``(leanInline $(quote e) $(quote cfg.toCodeConfig))]
    else
      let suggs := suggestTerms hl term.getString
      let h ← hintAt term "Use one of these" suggs
      let expectedString := ExpectString.abbreviateString (maxLength := 100) <| hl.toString
      let mut msg := m!"Not found: `{term.getString}`\n"
      msg := msg ++ m!"in:{indentD <| m!"\n".joinSep <| (m!"{·}") <$> expectedString.splitOn "\n"}"
      msg := msg ++ h
      logErrorAt term msg
      return #[← ``(sorryAx _ true)]

/--
Quotes the first term that matches the provided string.

Requires that the genre have an `ExternalCode` instance.
-/
@[role_expander moduleTerm]
def moduleTerm : RoleExpander
  | args, inls => withTraceNode `Elab.Verso (fun _ => pure m!"moduleTerm") <| moduleTermInline args inls

/--
Quotes the first term in the given anchor that matches the provided string.

Requires that the genre have an `ExternalCode` instance.
-/
@[role_expander anchorTerm]
def anchorTerm : RoleExpander
  | args, inls => withTraceNode `Elab.Verso (fun _ => pure m!"anchorTerm") <|
    if let some (Arg.anon a) := args[0]? then
      moduleTermInline (#[.named .missing (mkIdent `anchor) a] ++ args.drop 1) inls
    else
      throwError "Expected a positional argument first (the anchor name)"


def moduleTermBlock (args : Array Arg) (term : StrLit) : DocElabM (Array Term) := do
  let cfg@{module := moduleName, project, anchor?, showProofStates := _, defSite := _} ← parseThe CodeContext args

  withAnchored project moduleName anchor? fun hl => do
    let str := term.getString.trim
    if str.isEmpty then
      let ref ← getRef
      let suggs := suggestTerms hl str
      let suggs ← suggs.filterMapM fun s =>
        editCodeBlock ref s
      let h ←
        if suggs.size > 0 then
          hint m!"Use one of these" suggs
        else pure m!""
      let wanted := String.trim <| ExpectString.abbreviateString (maxLength := 100) <| hl.toString
      let wanted := wanted.splitOn "\n" |>.map (Std.Format.text ·) |> Std.Format.nil.joinSuffix
      logErrorAt term (m!"No sub-term of the following was specified: {indentD <| wanted}" ++ h)
      return #[← ``(sorryAx _ true)]
    if let some e := hl.matchingExpr? str then
      logInfos e
      return #[← ``(leanBlock $(quote e) $(quote cfg.toCodeConfig))]
    else
      let ref ← getRef
      let suggs := suggestTerms hl str
      let suggs ← suggs.filterMapM fun s =>
        editCodeBlock ref s
      let h ← hint "Use one of these" suggs
      logErrorAt term (m!"Not found: '{str}' in: {indentD <| ExpectString.abbreviateString (maxLength := 100) <| hl.toString}" ++ h)
      return #[← ``(sorryAx _ true)]


@[code_block_expander moduleTerm, inherit_doc moduleTerm]
def moduleTermBlockExp : CodeBlockExpander
  | args, term => withTraceNode `Elab.Verso (fun _ => pure m!"moduleTerm") <| moduleTermBlock args term

@[code_block_expander anchorTerm, inherit_doc anchorTerm]
def anchorTermBlockExp : CodeBlockExpander
  | args, term => withTraceNode `Elab.Verso (fun _ => pure m!"moduleTerm") <|
    if let some (Arg.anon a) := args[0]? then
      moduleTermBlock (#[.named .missing (mkIdent `anchor) a] ++ args.drop 1) term
    else
      throwError "Expected a positional argument first (the anchor name)"

private def severityName {m} [Monad m] [MonadEnv m] [MonadResolveName m] : MessageSeverity → m String
  | .error => unresolveNameGlobal ``MessageSeverity.error <&> (·.toString)
  | .warning => unresolveNameGlobal ``MessageSeverity.warning <&> (·.toString)
  | .information => unresolveNameGlobal ``MessageSeverity.information <&> (·.toString)

deriving instance Repr for MessageSeverity

private def severityHint (wanted : String) (stx : Syntax) : DocElabM MessageData := do
  if stx.getHeadInfo matches .original .. then
    hintAt stx m!"Use '{wanted}'" #[wanted]
  else pure m!""


open SubVerso.Highlighting Highlighted in
private partial def findTrace? (header : String) : MessageContents Highlighted → Option (MessageContents Highlighted)
  | .text .. | .term .. | .goal .. => none
  | .append xs =>
    xs.findSome? (findTrace? header)
  | t@(.trace _ msg chs _) =>
    if msg.toString == header then pure t
    else chs.findSome? (findTrace? header)

def outputBlock (args : Array Arg) (str : StrLit) : DocElabM (Array Term) := do
  let {module := moduleName, project, anchor?, severity, expandTraces, onlyTrace, showProofStates := _, defSite := _} ← parseThe MessageContext args

  withAnchored project moduleName anchor? fun hl => do
    let infos : Array _ := allInfo hl

    let mut candidates : Array Highlighted.Message := #[]

    for (msg, _) in infos do
      let msg ←
        if let some tr := onlyTrace then
          if let some msg' := findTrace? tr msg.contents then
            pure {msg with contents := msg'}
          else continue
        else pure <| msg
      candidates := candidates.push msg
      if messagesMatch (msg.toString (expandTraces := expandTraces)) str.getString then
        if msg.severity == .ofSeverity severity.1 then
          return #[← ``(leanOutputBlock $(quote msg) (expandTraces := $(quote expandTraces)))]
        else
        let wanted ← severityName msg.severity.toSeverity
          throwError "Mismatched severity. Expected '{repr severity.1}', got '{wanted}'.{← severityHint wanted severity.2}"

    let suggs : Array Suggestion := candidates.map fun msg => {
      suggestion := withNl (msg.toString (expandTraces := expandTraces)),
      preInfo? := some s!"{sevStr msg.severity.toSeverity}: "
    }

    let ref ← getRef

    let mut err : MessageData := "Expected"

    err := err ++ (m!"\nor".joinSep <| candidates.toList.map fun msg => indentD (msg.toString (expandTraces := expandTraces)) ++ "\n")

    if str.getString.trim.isEmpty then
      err := err ++ "but nothing was provided."
    else
      err := err ++ m!"but got:{indentD str.getString.trim}"
    if suggs.size = 1 then
      err := err ++ (← hintAt str "Use this:\n" suggs)
    else if suggs.size > 1 then
      err := err ++ (← hintAt str "Use one of these:\n" suggs)

    logErrorAt ref err

    return #[← ``(sorryAx _ true)]


/--
Displays output from the example module.

Requires that the genre have an `ExternalCode` instance.
-/
@[code_block_expander moduleOut]
def moduleOut : CodeBlockExpander
  | args, str => withTraceNode `Elab.Verso (fun _ => pure m!"moduleOut") <| outputBlock args str

/--
Displays information output from the example module.

Requires that the genre have an `ExternalCode` instance.
-/
@[code_block_expander moduleInfo]
def moduleInfo : CodeBlockExpander
  | args, str => withTraceNode `Elab.Verso (fun _ => pure m!"moduleInfo") <|
    outputBlock (#[.anon <| .name <| mkIdent ``MessageSeverity.information] ++ args) str

/--
Displays error output from the example module.

Requires that the genre have an `ExternalCode` instance.
-/
@[code_block_expander moduleError]
def moduleError : CodeBlockExpander
  | args, str => withTraceNode `Elab.Verso (fun _ => pure m!"moduleError") <|
    outputBlock (#[.anon <| .name <| mkIdent ``MessageSeverity.error] ++ args) str

/--
Displays warning output from the example module.

Requires that the genre have an `ExternalCode` instance.
-/
@[code_block_expander moduleWarning]
def moduleWarning : CodeBlockExpander
  | args, str => withTraceNode `Elab.Verso (fun _ => pure m!"moduleWarning") <|
    outputBlock (#[.anon <| .name <| mkIdent ``MessageSeverity.warning] ++ args) str

/--
Displays information output from the example module's anchor.

Requires that the genre have an `ExternalCode` instance.
-/
@[code_block_expander anchorInfo]
def anchorInfo : CodeBlockExpander
  | args, str => withTraceNode `Elab.Verso (fun _ => pure m!"anchorInfo") <| do
    if let some (Arg.anon a) := args[0]? then
      outputBlock (#[.anon <| .name <| mkIdent ``MessageSeverity.information, .named .missing (mkIdent `anchor) a] ++ args.drop 1) str
    else
      throwError "Expected a positional argument first (the anchor name)"

/--
Displays error output from the example module's anchor.

Requires that the genre have an `ExternalCode` instance.
-/
@[code_block_expander anchorError]
def anchorError : CodeBlockExpander
  | args, str => withTraceNode `Elab.Verso (fun _ => pure m!"anchorError") <| do
    if let some (Arg.anon a) := args[0]? then
      outputBlock (#[.anon <| .name <| mkIdent ``MessageSeverity.error, .named .missing (mkIdent `anchor) a] ++ args.drop 1) str
    else
      throwError "Expected a positional argument first (the anchor name)"
/--
Displays warning output from the example module's anchor.

Requires that the genre have an `ExternalCode` instance.
-/
@[code_block_expander anchorWarning]
def anchorWarning : CodeBlockExpander
  | args, str => withTraceNode `Elab.Verso (fun _ => pure m!"anchorWarning") <| do
    if let some (Arg.anon a) := args[0]? then
      outputBlock (#[.anon <| .name <| mkIdent ``MessageSeverity.warning, .named .missing (mkIdent `anchor) a] ++ args.drop 1) str
    else
      throwError "Expected a positional argument first (the anchor name)"


def moduleOutInline (args : Array Arg) (inls : TSyntaxArray `inline) : DocElabM (Array Term) := do
  let str? ← oneCodeStr? inls

  let {module := moduleName, project, anchor?, expandTraces, onlyTrace, severity, showProofStates := _, defSite := _} ← parseThe MessageContext args

  withAnchored project moduleName anchor? fun hl => do
    let infos := allInfo hl
    if let some str := str? then
      let mut candidates : Array Highlighted.Message := #[]
      for (msg, _) in infos do
        let msg ←
          if let some tr := onlyTrace then
            if let some msg' := findTrace? tr msg.contents then
              pure {msg with contents := msg'}
            else continue
          else pure <| msg
        candidates := candidates.push msg

        if messagesMatch (msg.toString (expandTraces := expandTraces)) str.getString then
          if msg.severity == .ofSeverity severity.1 then
            return #[← ``(leanOutputInline $(quote msg) true (expandTraces := $(quote expandTraces)))]
          else
            let wanted ← severityName msg.severity.toSeverity
            throwError "Mismatched severity. Expected '{repr severity.1}', got '{wanted}'.{← severityHint wanted severity.2}"

      let ref :=
        if let `(inline|role{ $_ $_* }[ $x ]) := (← getRef) then x.raw else str

      let suggs : Array Suggestion := candidates.map fun msg => {
        suggestion := quoteCode (msg.toString (expandTraces := expandTraces)).trim,
        preInfo? := s!"{sevStr msg.severity.toSeverity}: "
      }
      let h ←
        if suggs.isEmpty then pure m!""
        else hintAt ref "Use one of these." suggs

      let err :=
        m!"Expected one of:{indentD (m!"\n".joinSep <| candidates.toList.map (·.toString (expandTraces := expandTraces)))}" ++
        m!"\nbut got:{indentD str.getString}\n" ++ h
      logErrorAt str err
    else
      let candidates := infos.filterMap fun (msg, _) =>
          if let some tr := onlyTrace then
            if let some msg' := findTrace? tr msg.contents then
              pure {msg with contents := msg'}
            else none
          else pure <| msg
      let err := m!"Expected one of:{indentD (m!"\n".joinSep <| candidates.toList.map (·.toString (expandTraces := expandTraces)))}"
      Lean.logError m!"No expected term provided. {err}"
      if let `(inline|role{$_ $_*} [%$tok1 $contents* ]%$tok2) := (← getRef) then
        let stx :=
          if tok1.getHeadInfo matches .original .. && tok2.getHeadInfo matches .original .. then
            mkNullNode #[tok1, tok2]
          else mkNullNode contents
        for (msg, _) in infos do
          let str := msg.toString
          Suggestion.saveSuggestion stx (quoteCode <| ExpectString.abbreviateString str.trim) (quoteCode str.trim)

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


@[role_expander moduleOut, inherit_doc moduleOut]
def moduleOutRole : RoleExpander
  | args, inls => withTraceNode `Elab.Verso (fun _ => pure m!"moduleOutRole") <| moduleOutInline args inls

@[role_expander moduleInfo, inherit_doc moduleInfo]
def moduleOutInfoRole : RoleExpander
  | args, inls => withTraceNode `Elab.Verso (fun _ => pure m!"moduleOutInfoRole") <|
    moduleOutInline (#[.anon <| .name <| mkIdent ``MessageSeverity.information] ++ args) inls

@[role_expander moduleError, inherit_doc moduleError]
def moduleOutErrorRole : RoleExpander
  | args, inls => withTraceNode `Elab.Verso (fun _ => pure m!"moduleOutErrorRole") <|
    moduleOutInline (#[.anon <| .name <| mkIdent ``MessageSeverity.error] ++ args) inls

@[role_expander moduleWarning, inherit_doc moduleWarning]
def moduleOutWarningRole : RoleExpander
  | args, inls => withTraceNode `Elab.Verso (fun _ => pure m!"moduleOutWarningRole") <|
    moduleOutInline (#[.anon <| .name <| mkIdent ``MessageSeverity.warning] ++ args) inls

def anchorOutAsRole (severity : Name) (args : Array Arg) (inls : TSyntaxArray `inline) : DocElabM (Array Term) :=
  if let some (Arg.anon a) := args[0]? then
    moduleOutInline (#[.anon <| .name <| mkIdent severity, .named .missing (mkIdent `anchor) a] ++ args.drop 1) inls
  else
    throwError "Expected a positional argument first (the anchor name)"

@[role_expander anchorInfo, inherit_doc anchorInfo]
def anchorOutInfoRole : RoleExpander
  | args, inls => withTraceNode `Elab.Verso (fun _ => pure m!"anchorOutInfoRole") <|
    anchorOutAsRole ``MessageSeverity.information args inls

@[role_expander anchorWarning, inherit_doc anchorWarning]
def anchorOutWarningRole : RoleExpander
  | args, inls => withTraceNode `Elab.Verso (fun _ => pure m!"anchorOutWarningRole") <|
    anchorOutAsRole ``MessageSeverity.warning args inls

@[role_expander anchorError, inherit_doc anchorError]
def anchorOutErrorRole : RoleExpander
  | args, inls => withTraceNode `Elab.Verso (fun _ => pure m!"anchorOutErrorRole") <|
    anchorOutAsRole ``MessageSeverity.error args inls

/--
Explicitly indicates that a code element is intended to be literal character values without any
further semantics.
-/
@[role_expander lit]
def lit : RoleExpander
  | args, inls => do
    ArgParse.done.run args
    let kw ← oneCodeStr inls
    return #[← ``(Inline.code $(quote kw.getString))]


private def hasSubstring (s pattern : String) : Bool :=
  if h : pattern.endPos.1 = 0 then false
  else
    have hPatt := Nat.zero_lt_of_ne_zero h
    let rec loop (pos : String.Pos) :=
      if h : pos.byteIdx + pattern.endPos.byteIdx > s.endPos.byteIdx then
        false
      else
        have := Nat.lt_of_lt_of_le (Nat.add_lt_add_left hPatt _) (Nat.ge_of_not_lt h)
        if s.substrEq pos pattern 0 pattern.endPos.byteIdx then
          have := Nat.sub_lt_sub_left this (Nat.add_lt_add_left hPatt _)
          true
        else
          have := Nat.sub_lt_sub_left this (s.lt_next pos)
          loop (s.next pos)
      termination_by s.endPos.1 - pos.1
    loop 0


/--
Internal detail of anchor suggestion mechanism.
-/
@[inline_expander Lean.Doc.Syntax.code]
private def suggest : InlineExpander
  |  `(inline| code( $str )) => do
    let str' := str.getString

    unless verso.examples.suggest.get (← getOptions) do
      -- Delegate to the next handler
      Elab.throwUnsupportedSyntax

    let mut termSuggestions : NameMap (HashSet String) := {}
    let mut nameSuggestions : NameMap (HashSet String) := {}

    let anchors := loadedModuleAnchorExt.getState (← getEnv)
    if let some defaultProject := verso.exampleProject.get? (← getOptions) then
      for (modName, modAnchors) in anchors[defaultProject]?.getD {} do
        for (_, examples) in modAnchors do
          for (anchorName, anchorContents) in examples.anchors.toArray do

            if str'.all (fun c => !c.isWhitespace) then
              if let some _ := anchorContents.matchingName? str' then
                nameSuggestions := nameSuggestions.insert modName <|
                  ((nameSuggestions.find? modName).getD {}).insert anchorName

            if let some _ := anchorContents.matchingExpr? str' then
              termSuggestions :=
                termSuggestions.insert modName <|
                  ((termSuggestions.find? modName).getD {}).insert anchorName

    let mut defaultSuggestions : Array (String × String) := #[]
    let mut otherSuggestions : Array (String × String × String) := #[]
    let modName? := (verso.exampleModule.get? (← getOptions)).map (·.toName)

    if let some modName := modName? then
      let mut names : HashSet String := {}
      for xs in nameSuggestions.find? modName do
        for x in xs do
          defaultSuggestions := defaultSuggestions.push  ("anchorName", x)
          names := names.insert x
      for xs in termSuggestions.find? modName do
        for x in xs do
          unless x ∈ names do
            defaultSuggestions := defaultSuggestions.push ("anchorTerm", x)

    let mut names : HashSet (Name × String) := {}
    for (m, xs) in nameSuggestions do
      if modName?.isEqSome m then continue
      for x in xs do
        otherSuggestions := otherSuggestions.push ("anchorName", x, m.toString)
        names := names.insert (m, x)
    for (m, xs) in termSuggestions do
      if modName?.isEqSome m then continue
      for x in xs do
        unless (m, x) ∈ names do
          otherSuggestions := otherSuggestions.push ("anchorTerm", x, m.toString)

    let text ← getFileMap
    let region? := (← getRef).getPos? |>.map fun p =>
      let {line, ..} := text.utf8PosToLspPos p
      text.source.extract (text.lineStart (line - 4)) (text.lineStart (line + 4))
    let region := region?.getD ""

    let (close, far) := defaultSuggestions.partition (fun (_, x) => hasSubstring region x)
    have : Ord (String × String) := lexOrd
    let close := close.qsortOrd
    let far := far.qsortOrd

    let suggestions : Array Meta.Hint.Suggestion :=
      close.map (fun (r, x) => {suggestion := .string ("{" ++ r ++ " " ++ x ++ "}`" ++ str' ++ "`"), postInfo? := some " (used nearby)"}) ++
      far.map (fun (r, x) => {suggestion := .string ("{" ++ r ++ " " ++ x ++ "}`" ++ str' ++ "`")}) ++
      otherSuggestions.map (fun (r, x, m) => "{" ++ r ++ " " ++ x ++ s!" (module:={m})" ++ "}`" ++ str' ++ "`")

    if suggestions.isEmpty then
      let h ← hint m!"Add the `lit` role to indicate that it denotes literal characters:" #["{lit}`" ++ str' ++ "`"]
      logWarning <| m!"Code element is missing a role." ++ h
    else
      let h ← hint m!"Try one of these:" suggestions
      logWarning <| m!"Code element could be highlighted." ++ h

    return (← ``(Inline.code $(quote str.getString)))
  | _ => Elab.throwUnsupportedSyntax
