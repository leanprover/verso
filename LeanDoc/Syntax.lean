namespace LeanDoc.Syntax

declare_syntax_cat inline
syntax (name:=text) str : inline
/-- Emphasis (often rendered as italics) -/
syntax (name:=emph) str : inline
/-- Bold emphasis   -/
syntax (name:=bold) str : inline
/-- Link -/
syntax (name:=link) str : inline
/-- Line break -/
syntax (name:=linebreak) str : inline

declare_syntax_cat list_item
/-- List item -/
syntax (name:=li) str : inline

declare_syntax_cat block
syntax (name:=para) str : block
/-- List -/
syntax (name:=ul) str : block
/-- Literal code -/
syntax (name:=code) str : block
/-- Quotation -/
syntax (name:=blockquote) str : block
/-- Custom directive -/
syntax (name:=directive) str : block
/-- A header -/
syntax (name:=header) str : block



end LeanDoc.Syntax
