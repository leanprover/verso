import Lean

open Lean

namespace LeanDoc.Genre

inductive Highlighted.Token.Kind where
  | keyword
  | const (name : Name)
  | var (name : Name)
  | sort
  | unknown
deriving Repr, DecidableEq, Inhabited

open Highlighted.Token.Kind in
open Syntax (mkCApp) in
instance : Quote Highlighted.Token.Kind where
  quote
    | .keyword => mkCApp ``keyword #[]
    | .const n => mkCApp ``const #[quote n]
    | .var n => mkCApp ``var #[quote n]
    | .sort => mkCApp ``sort #[]
    | .unknown => mkCApp ``unknown #[]

structure Highlighted.Token where
  pre : String
  content : String
  post : String
  kind : Token.Kind
deriving Repr, DecidableEq, Inhabited

open Syntax in
open Highlighted in
instance : Quote Highlighted.Token where
  quote
    | (.mk pre content post kind) =>
      mkCApp ``Token.mk #[quote pre, quote content, quote post, quote kind]

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
  | seq (highlights : Array Highlighted)
  | span (kind : Highlighted.Span.Kind) (content : Highlighted)
deriving Repr

def Highlighted.empty : Highlighted := .seq #[]
instance : Append Highlighted where
  append
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
    | .seq hls => mkCApp ``seq #[quoteArray ⟨quote'⟩ hls]
    | .span k content => mkCApp ``span #[quote k, quote' content]
