/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Elab.Term
meta import Lean.Elab.Term
public meta import Lean.Meta.Hint
import Lean.Meta.Hint
public import MultiVerso.Slug

open Lean

namespace Verso.Output

/--
TeX output
-/
public inductive TeX where
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

public instance : Coe (Array TeX) TeX where
  coe := .seq

public instance : Coe (List TeX) TeX where
  coe xs := .seq xs.toArray

public instance : Coe String TeX where
  coe := .text

public instance : Append TeX where
  append
    | .seq xs, .seq ys => .seq (xs ++ ys)
    | .seq xs, y => .seq (xs.push y)
    | x, .seq ys => .seq (#[x] ++ ys)
    | x, y => .seq #[x, y]

namespace TeX

/-- The empty TeX document -/
public def empty : TeX := .seq #[]

/-- Checks whether the document contains only whitespace. -/
public partial def isWhitespace : TeX → Bool
  | .seq xs => xs.all isWhitespace
  | .paragraphBreak => true
  | .environment .. => false
  | .command .. => false
  | .text s => s.all Char.isWhitespace
  | .raw s => s.all Char.isWhitespace

/-- Converts a TeX document to a string to be processed by LaTeX -/
public partial def asString (doc : TeX) : String :=
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
    |>.replace "_" "\\_" |>.replace "%" "\\%" |>.replace "#" "\\#" --TODO make correct!

public section
declare_syntax_cat macro_name
scoped syntax ident : macro_name
scoped syntax "section" : macro_name
end

meta partial def _root_.Lean.TSyntax.macroName : TSyntax `macro_name → String
  | ⟨.node _ _ #[.atom _ x]⟩ => x
  | ⟨.node _ _ #[.ident _ _ x ..]⟩ => x.eraseMacroScopes.toString
  | _ => "unknown"


public section
declare_syntax_cat tex

scoped syntax "\\TeX{" tex* "}" : term

scoped syntax "\\Lean{" term "}" : tex
scoped syntax "\\begin{" macro_name "}" ("[" tex* "]")* ("{" tex* "}")* tex* "\\end{" macro_name "}" : tex
scoped syntax "\\" macro_name ("[" tex* "]")* ("{" tex* "}")* : tex
scoped syntax "s!" interpolatedStr(term) : tex
scoped syntax "~" : tex

scoped syntax str : tex
end

open Lean Elab Term in
meta partial def elabTeX (stx : TSyntax `tex) : TermElabM Expr := withRef stx do
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
  | `(tex|~) => do
    Meta.mkAppM ``TeX.raw #[toExpr "~"]
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


private def hexDigits := "0123456789ABCDEF".toList.toArray

@[grind =, simp]
theorem hexDigits_size : hexDigits.size = 16 := by decide

private def toHex (n : Nat) : String := Id.run do
  let mut n := n
  let mut digits := #[]
  repeat
    if h : n < 16 then
      digits := digits.push hexDigits[n]
      break
    else
      digits := digits.push <| hexDigits[n % 16]'(by grind)
      n := n >>> 4
  -- Pad
  let padding := (4 - digits.size).fold (init := "") (fun _ _ p => p.push '0')
  digits.foldr (init := padding) fun c s => s.push c

open Multi in
/--
Converts a slug to a valid LaTeX label, which may contain only letters 'a'-'Z' or 'A'-'Z', numbers
'0'-'9', and hyphen. Hyphens are encoded as "--", and are used to encode other characters as their
hex code.
-/
public def labelForTeX (slug : Slug) : String := Id.run do
  let mut out := ""
  for c in slug.toString.chars do
    if c.isAlphanum then
      out := out.push c
    else if c == '-' then
      out := out |>.push '-' |>.push '-'
    else
      out := out ++ s!"-{toHex c.toNat}"
  return out
