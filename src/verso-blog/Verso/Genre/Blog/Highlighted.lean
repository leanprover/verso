import Lean

open Lean

namespace Verso.Genre

inductive Highlighted.Token.Kind where
  | keyword (name : Option Name) (docs : Option String)
  | const (name : Name) (docs : Option String)
  | var (name : FVarId)
  | sort
  | unknown
deriving Repr, Inhabited

open Highlighted.Token.Kind in
open Syntax (mkCApp) in
instance : Quote Highlighted.Token.Kind where
  quote
    | .keyword n docs => mkCApp ``keyword #[quote n, quote docs]
    | .const n docs => mkCApp ``const #[quote n, quote docs]
    | .var (.mk n) => mkCApp ``var #[mkCApp ``FVarId.mk #[quote n]]
    | .sort => mkCApp ``sort #[]
    | .unknown => mkCApp ``unknown #[]

structure Highlighted.Token where
  kind : Token.Kind
  content : String
deriving Repr, Inhabited

open Syntax in
open Highlighted in
instance : Quote Highlighted.Token where
  quote
    | (.mk kind content) =>
      mkCApp ``Token.mk #[quote kind, quote content]

inductive Highlighted.Span.Kind where
  | error
  | warning
  | info
deriving Repr, DecidableEq, Inhabited

open Highlighted Span Kind in
open Syntax in
instance : Quote Kind where
  quote
    | .error => mkCApp ``error #[]
    | .warning => mkCApp ``warning #[]
    | .info => mkCApp ``info #[]

inductive Highlighted where
  | token (tok : Highlighted.Token)
  | text (str : String)
  | seq (highlights : Array Highlighted)
  -- TODO replace messages as strings with structured info
  | span (kind : Highlighted.Span.Kind) (info : String) (content : Highlighted)
  | point (kind : Highlighted.Span.Kind) (info : String)
deriving Repr

def Highlighted.empty : Highlighted := .seq #[]
instance : Append Highlighted where
  append
    | .text str1, .text str2 => .text (str1 ++ str2)
    | .seq xs, .seq ys => .seq (xs ++ ys)
    | .seq xs,  x => .seq (xs ++ #[x])
    | x, .seq xs => .seq (#[x] ++ xs)
    | x, y => .seq #[x, y]

open Lean Syntax in
open Highlighted in
partial instance : Quote Highlighted where
 quote := quote'
where
  quoteArray {α : _} (_inst : Quote α) (xs : Array α) : TSyntax `term :=
    mkCApp ``List.toArray #[quote xs.toList]

  quote'
    | .token tok => mkCApp ``token #[quote tok]
    | .text str => mkCApp ``text #[quote str]
    | .seq hls => mkCApp ``seq #[quoteArray ⟨quote'⟩ hls]
    | .span k info content => mkCApp ``span #[quote k, quote info, quote' content]
    | .point k info => mkCApp ``point #[quote k, quote info]
