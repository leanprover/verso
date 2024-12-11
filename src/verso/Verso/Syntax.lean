/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso.SyntaxUtils

open Lean.Parser (rawIdent)

namespace Verso.Syntax

declare_syntax_cat arg_val
syntax (name:=arg_str) str : arg_val
syntax (name:=arg_ident) ident : arg_val
syntax (name:=arg_num) num : arg_val

declare_syntax_cat argument
syntax (name:=anon) arg_val : argument
syntax (name:=named) ident ":=" arg_val : argument

declare_syntax_cat link_target
syntax (name:=url) "(" str ")" : link_target
syntax (name:=ref) "[" str "]" : link_target

declare_syntax_cat inline
syntax (name:=text) str : inline
/-- Emphasis (often rendered as italics) -/
syntax (name:=emph) "_{" inline* "}" : inline
/-- Bold emphasis   -/
syntax (name:=bold) "*{" inline* "}" : inline
/-- Link -/
syntax (name:=link) "link[" inline* "]" link_target : inline
/-- Image -/
syntax (name:=image) "image[" str* "]" link_target : inline
/-- A footnote use -/
syntax (name:=footnote) "[^" str "]" : inline
/-- Line break -/
syntax (name:=linebreak) "line!" str : inline
/-- Literal code. If the first and last characters are space, and it contains at least one non-space
  character, then the resulting string has a single space stripped from each end.-/
syntax (name:=code) "code{" str "}" : inline
syntax (name:=role) "role{" ident argument* "}" "[" inline "]"  : inline
syntax (name:=inline_math) "${" inline "}" : inline
syntax (name:=display_math) "$${" inline "}" : inline

declare_syntax_cat list_item
/-- List item -/
syntax (name:=li) "*" str : list_item

declare_syntax_cat block
declare_syntax_cat desc_item
syntax (name:=desc) ":" inline+ "=>" block+ : desc_item

syntax (name:=para) "para{" inline+ "}" : block
/-- Unordered List -/
syntax (name:=ul) "ul{" list_item* "}" : block
/-- Definition list -/
syntax (name:=dl) "dl{" desc_item* "}" : block
/-- Ordered list -/
syntax (name:=ol) "ol{" num list_item* "}" : block
/-- Literal code -/
syntax (name:=codeblock) "```" str "```" : block
/-- Quotation -/
syntax (name:=blockquote) str : block
/-- A link reference definition -/
syntax (name:=link_ref)  "[" str "]:" str : block
/-- A footnote definition -/
syntax (name:=footnote_ref)  "[^" str "]:" inline* : block
/-- Custom directive -/
syntax (name:=directive) "directive{" rawIdent argument* "}" "[" block* "]": block
/-- A header -/
syntax (name:=header) inline* : block
open Lean.Parser.Term in

open Lean.Parser Term in
def metadataContents := structInstFields (sepByIndent structInstField ", " (allowTrailingSep := true))

/-- Metadata for this section, defined by the current genre -/
syntax (name:=metadata_block) "%%%" metadataContents "%%%" : block
syntax (name:=block_role) "block_role{" rawIdent argument* "}" ("[" block "]")?  : block
