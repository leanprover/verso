import Lean

namespace Verso.Hover

open Lean Elab

structure CustomHover where
  /-- A Markdown string to send as the hover -/
  markedString : String
deriving TypeName, Repr

def addCustomHover [Monad m] [MonadInfoTree m] (stx : Syntax) (markdown : String) : m Unit := do
  pushInfoLeaf <| .ofCustomInfo ⟨stx, .mk <| CustomHover.mk markdown⟩
