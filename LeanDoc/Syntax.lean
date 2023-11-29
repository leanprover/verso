/-
Copyright (c) 2023 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import LeanDoc.SyntaxUtils

namespace LeanDoc.Syntax

declare_syntax_cat arg_val
syntax str : arg_val
syntax ident : arg_val
syntax num : arg_val

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
/-- Line break -/
syntax (name:=linebreak) "line!" : inline
/-- Literal characters-/
syntax (name:=code) "code{" str "}" : inline
syntax (name:=role) "role{" ident argument* "}" "[" inline "]"  : inline

declare_syntax_cat list_item
/-- List item -/
syntax (name:=li) "*" str : list_item

declare_syntax_cat block
syntax (name:=para) "para{" inline+ "}" : block
/-- List -/
syntax (name:=ul) "ul{" list_item* "}" : block
/-- Literal code -/
syntax (name:=codeblock) str : block
/-- Quotation -/
syntax (name:=blockquote) str : block
/-- Custom directive -/
syntax (name:=directive) str : block
/-- A header -/
syntax (name:=header) inline* : block

syntax (name:=block_role) "role{" ident argument* "}" "[" block "]"  : block


open LeanDoc.SyntaxUtils Lean Elab Term Std in
macro "#seeStx" tm:term : command =>
  `(#eval (ppSyntax <$> $tm : TermElabM Std.Format) )

#seeStx `(inline| "foo")
#seeStx `(inline| _{ "foo" "bar" })
#seeStx `(inline| *{ "foo" "bar" })
#seeStx `(inline| link[_{"FPiL" line! "book"}]("https://..."))
#seeStx `(inline| code{ "foo" })


end LeanDoc.Syntax
