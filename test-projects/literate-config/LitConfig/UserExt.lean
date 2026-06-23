import VersoLiterate

set_option doc.verso true

namespace LitConfig.UserExt

open Lean Elab Term Verso.Doc VersoLiterate

/-!
This test checks that handlers for custom data elements in Verso docstrings work as they should in
literate mode:
1. Handlers should run.
2. User handlers should take precedence over those that ship with Verso.
3. When a handler is missing, a warning is issued and the fallback is used.
-/

/--
Intercepts {name}`Lean.Doc.Data.Const` docstring extensions and replaces them with a bogus
{name (full:=VersoLiterate.Ext.data)}`data` payload. This checks that user-registered handlers are
loaded and given precedence over built-in handlers.
-/
@[inline_to_literate]
def customConst : InlineToLiterate
  | ``Lean.Doc.Data.Const, _val, _content =>
    return some <| .other (.data "USER-CONST-MARKER") #[.text "(looks like you're defining a const)"]
  | _, _, _ => return none

/--
Intercepts {name}`Lean.Doc.Data.LeanBlock` docstring extensions and replaces them with a bogus
{name (full:=VersoLiterate.Ext.data)}`data` payload. This checks that user-registered handlers are
loaded and given precedence over built-in handlers.
-/
@[block_to_literate]
def customLeanBlock : BlockToLiterate
  | ``Lean.Doc.Data.LeanBlock, _val, _content =>
    return some <| .other (.data "USER-LEANBLOCK-MARKER") #[.blockquote #[.para #[.text "Replacement For A Lean Block"]]]
  | _, _, _ => return none

/-- Payload type for the unknown-extension fixture role. -/
structure FallbackPayload where
  marker : String
deriving TypeName

/--
A role that emits an {name}`Inline.other` whose extension is not handled, so the conversion's
warning-and-fallback path is exercised.

The content of the role is ignored.
-/
@[doc_role]
def unknownRole (_ : TSyntaxArray `inline) : Lean.Doc.DocM (Lean.Doc.Inline ElabInline) := do
  return .other
    { name := `LitConfig.UserExt.FallbackPayload,
      val := .mk (FallbackPayload.mk "no-handler-fallback") }
    #[.text "THIS IS THE FALLBACK"]

end LitConfig.UserExt

/-! Fixture declarations exercising the user handlers and the no-handler fallback. -/

/-- This definition's name is used later in a test docstring.-/
def REFER_TO_ME : Nat := 0

/--
A docstring with a reference to {name}`REFER_TO_ME` and a Lean block:

```lean
example : True := trivial
```

If the custom handlers are picked up, the JSON for this module contains
{lit}`USER-CONST-MARKER` (inline) and {lit}`USER-LEANBLOCK-MARKER` (block).
-/
def customDemo : Nat := REFER_TO_ME

open LitConfig.UserExt in
/--
A docstring that shows a fallback: {unknownRole}[some unknown role].
-/
def fallbackDemo : Nat := 0
