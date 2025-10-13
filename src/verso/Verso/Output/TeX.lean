/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.Elab.Term
import Lean.Meta.Hint

open Lean

namespace Verso.Output

/--
TeX output
-/
inductive TeX where
  /-- Text to be shown in the document, escaped as needed. -/
  | text (string : String)
  /-- Raw TeX code to be included without escaping. -/
  | raw (string : String)
  /-- A LaTeX command, with the provided optional and mandatory arguments (in square and curly brackets, respectively) -/
  | command (name : String) (optArgs : Array TeX) (args : Array TeX)
  /-- A LaTeX environment, with the provided optional and mandatory arguments (in square and curly brackets, respectively) -/
  | environment (name : String)  (optArgs : Array TeX) (args : Array TeX) (content : Array TeX)
  /-- A paragraph break, rendered to TeX as a blank line -/
  | paragraphBreak
  /-- Concatenation of TeX -/
  | seq (contents : Array TeX)
deriving Repr, Inhabited

instance : Coe (Array TeX) TeX where
  coe := .seq

instance : Coe (List TeX) TeX where
  coe xs := .seq xs.toArray

instance : Coe String TeX where
  coe := .text

instance : Append TeX where
  append
    | .seq xs, .seq ys => .seq (xs ++ ys)
    | .seq xs, y => .seq (xs.push y)
    | x, .seq ys => .seq (#[x] ++ ys)
    | x, y => .seq #[x, y]

namespace TeX

/-- The empty TeX document -/
def empty : TeX := .seq #[]

/-- Converts a TeX document to a string to be processed by LaTeX -/
partial def asString (doc : TeX) : String :=
  match doc with
  | .text str => escape str
  | .raw str => str
  | .command name opt req =>
    s!"\\{name}" ++ opt.foldl (· ++ "[" ++ ·.asString ++ "]") "" ++ req.foldl (· ++ "{" ++ ·.asString ++ "}") ""
  | .environment name opt req content =>
    "\\begin{" ++ name ++ "}" ++ opt.foldl (· ++ "[" ++ ·.asString ++ "]") "" ++ req.foldl (· ++ "{" ++ ·.asString ++ "}") "" ++ "\n" ++
    String.join (content.map (·.asString) |>.toList) ++ "\n" ++
    "\\end{" ++ name ++ "}\n"
  | .paragraphBreak => "\n\n"
  | .seq texs => String.join (texs.map (·.asString) |>.toList)
where
  escape s := s.replace "\\" "\\\\" |>.replace "{" "\\{" |>.replace "}" "\\}" |>.replace "^" "\\string^"
    |>.replace "_" "\\_" |>.replace "%" "\\%" --TODO make correct!

declare_syntax_cat macro_name
scoped syntax ident : macro_name
scoped syntax "section" : macro_name

partial def _root_.Lean.TSyntax.macroName : TSyntax `macro_name → String
  | ⟨.node _ _ #[.atom _ x]⟩ => x
  | ⟨.node _ _ #[.ident _ _ x ..]⟩ => x.eraseMacroScopes.toString
  | _ => "unknown"


declare_syntax_cat tex

scoped syntax "\\TeX{" tex* "}" : term

scoped syntax "\\Lean{" term "}" : tex
scoped syntax "\\begin{" macro_name "}" ("[" tex* "]")* ("{" tex* "}")* tex* "\\end{" macro_name "}" : tex
scoped syntax "\\" macro_name ("[" tex* "]")* ("{" tex* "}")* : tex
scoped syntax "s!" interpolatedStr(term) : tex

scoped syntax str : tex

open Lean Elab Term in
partial def elabTeX (stx : TSyntax `tex) : TermElabM Expr := withRef stx do
  match stx with
  | `(tex|\Lean{$e}) => do
    elabTermEnsuringType e (some (.const ``TeX []))
  | `(tex|$s:str ) => do
    let s ← elabTermEnsuringType s (some (.const ``String []))
    Meta.mkAppM ``TeX.text #[s]
  | `(tex|s!$s) => do
    let s ← elabTermEnsuringType (← `(s!$s:interpolatedStr)) (some (.const ``String []))
    Meta.mkAppM ``TeX.raw #[s]
  | `(tex|\begin{ $env:macro_name } $[ [ $opt* ] ]* $[ { $req* } ]* $contents:tex* \end{ $env':macro_name}) => do
    if env.macroName != env'.macroName then
      let hint ← MessageData.hint m!"Make the environment names match" #[env.macroName] (ref? := some env')
      throwErrorAt env' "Mismatched closing environment. Expected `{env.macroName}`, but got `{env'.macroName}.`\n{hint}"
    let opt ← opt.mapM fun texs => do
      if h : texs.size = 1 then
        elabTeX texs[0]
      else
        let arg ← Meta.mkArrayLit (.const ``TeX []) (← texs.mapM elabTeX).toList
        Meta.mkAppM ``TeX.seq #[arg]
    let opt ← Meta.mkArrayLit (.const ``TeX []) opt.toList
    let req ← req.mapM fun texs => do
      if h : texs.size = 1 then
        elabTeX texs[0]
      else
        let arg ← Meta.mkArrayLit (.const ``TeX []) (← texs.mapM elabTeX).toList
        Meta.mkAppM ``TeX.seq #[arg]
    let req ← Meta.mkArrayLit (.const ``TeX []) req.toList
    let contents ← contents.mapM elabTeX
    let contents ← Meta.mkArrayLit (.const ``TeX []) contents.toList
    Meta.mkAppM ``TeX.environment #[toExpr env.macroName, opt, req, contents]
  | `(tex| \ $command:macro_name $[ [ $opt* ] ]* $[ { $req* } ]*) => do
    let opt ← opt.mapM fun texs => do
      if h : texs.size = 1 then
        elabTeX texs[0]
      else
        let arg ← Meta.mkArrayLit (.const ``TeX []) (← texs.mapM elabTeX).toList
        Meta.mkAppM ``TeX.seq #[arg]
    let opt ← Meta.mkArrayLit (.const ``TeX []) opt.toList
    let req ← req.mapM fun texs => do
      if h : texs.size = 1 then
        elabTeX texs[0]
      else
        let arg ← Meta.mkArrayLit (.const ``TeX []) (← texs.mapM elabTeX).toList
        Meta.mkAppM ``TeX.seq #[arg]
    let req ← Meta.mkArrayLit (.const ``TeX []) req.toList
    Meta.mkAppM ``TeX.command #[toExpr command.macroName, opt, req]
  | stx =>
    throwUnsupportedSyntax

elab_rules : term
  | `(term|\TeX{$TeX:tex*}) => do
    if TeX.size = 0 then
      return .const ``TeX.empty []
    else if h : TeX.size = 1 then elabTeX TeX[0]
    else
      let args ← Meta.mkArrayLit (.const ``TeX []) (← TeX.mapM elabTeX).toList
      Meta.mkAppM ``TeX.seq #[args]


/-- info: Verso.Output.TeX.seq #[] -/
#guard_msgs in
#eval repr <| \TeX{}

/-- info: Verso.Output.TeX.text "Hello, world!" -/
#guard_msgs in
#eval repr <| \TeX{"Hello, world!"}

/--
info: Verso.Output.TeX.command "hyperlink" #[] #[Verso.Output.TeX.raw "foo", Verso.Output.TeX.text ""]
-/
#guard_msgs in
#eval repr<| \TeX{\hyperlink{\Lean{.raw "foo" }}{\Lean{""}}}

/--
info: Verso.Output.TeX.seq
  #[Verso.Output.TeX.text "Hello, ", Verso.Output.TeX.command "textbf" #[] #[Verso.Output.TeX.text "world"]]
-/
#guard_msgs in
#eval repr <| \TeX{"Hello, " \textbf{"world"}}

/--
info: Verso.Output.TeX.environment
  "Verbatim"
  #[]
  #[Verso.Output.TeX.raw "commandChars=\\\\"]
  #[Verso.Output.TeX.text "Hello, ", Verso.Output.TeX.command "textbf" #[] #[Verso.Output.TeX.text "world"]]
-/
#guard_msgs in
#eval repr <| \TeX{\begin{Verbatim}{s!"commandChars=\\\\"}"Hello, " \textbf{"world"}\end{Verbatim}}
