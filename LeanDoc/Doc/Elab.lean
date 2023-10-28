import Lean
import LeanDoc.Doc
import LeanDoc.SyntaxUtils

namespace LeanDoc.Doc.Elab

open Lean Elab
open LeanDoc.SyntaxUtils

structure HeaderContext where
  currentLevel : Nat
  startIndex : Nat
  inPrelude : Option Nat
deriving Repr

structure DocElabM.State where
  stack : Array (TSyntax `term) := #[]
  headerContext : Option HeaderContext
  headerStack : Array Nat
deriving Repr

def DocElabM (α : Type) : Type := StateT DocElabM.State TermElabM α

def DocElabM.run (st : DocElabM.State) (act : DocElabM α) : TermElabM (α × DocElabM.State) :=
  StateT.run act st

instance : MonadRef DocElabM := inferInstanceAs <| MonadRef (StateT DocElabM.State TermElabM)

instance : MonadQuotation DocElabM := inferInstanceAs <| MonadQuotation (StateT DocElabM.State TermElabM)

instance : Monad DocElabM := inferInstanceAs <| Monad (StateT DocElabM.State TermElabM)

instance : MonadLift TermElabM DocElabM := inferInstanceAs <| MonadLift TermElabM (StateT DocElabM.State TermElabM)

instance : MonadExceptOf Exception DocElabM := inferInstanceAs <| MonadExceptOf Exception (StateT DocElabM.State TermElabM)

instance : MonadState DocElabM.State DocElabM := inferInstanceAs <| MonadState DocElabM.State (StateT DocElabM.State TermElabM)

instance : MonadStateOf DocElabM.State DocElabM := inferInstanceAs <| MonadStateOf DocElabM.State (StateT DocElabM.State TermElabM)

instance : MonadFinally DocElabM := inferInstanceAs <| MonadFinally (StateT DocElabM.State TermElabM)


def DocElabM.size : DocElabM Nat := (·.stack.size) <$> get

def DocElabM.push (stx : TSyntax `term) : DocElabM Unit := modify fun st => {st with stack := st.stack.push stx}

def DocElabM.mkNode (k : SyntaxNodeKind) (iniStackSz : Nat) : DocElabM Unit := do
  let stack ← (·.stack) <$> get
  let newNode := Syntax.node SourceInfo.none k (stack.extract iniStackSz stack.size)
  modify fun st => {st with stack := stack.shrink iniStackSz |>.push ⟨newNode⟩}

def DocElabM.mkCApp (ctor : Name) (iniStackSz : Nat) : DocElabM Unit := do
  let stack ← (·.stack) <$> get
  let newNode := Syntax.mkCApp ctor (stack.extract iniStackSz stack.size)
  modify fun st => {st with stack := stack.shrink iniStackSz |>.push ⟨newNode⟩}

def DocElabM.mkArray (iniStackSz : Nat) : DocElabM Unit := do
  let stack ← (·.stack) <$> get
  let elts := stack.extract iniStackSz stack.size
  let newNode ← `(#[$[$elts],*])
  modify fun st => {st with stack := stack.shrink iniStackSz |>.push ⟨newNode⟩}

def DocElabM.within (ctor : Name) (act : DocElabM Unit) : DocElabM Unit := do
  let iniSz ← size
  act
  mkCApp ctor iniSz

def DocElabM.array (act : DocElabM Unit) : DocElabM Unit := do
  let iniSz ← size
  act
  mkArray iniSz

def DocElabM.inBlock (act : DocElabM Unit) : DocElabM Unit := do
  let ctxt := (← get).headerContext
  try
    modify fun st => {st with headerContext := none}
    act
  finally
    modify fun st => {st with headerContext := ctxt}

def DocElabM.debug (msg : String) : DocElabM Unit := do
  let st ← get
  dbg_trace "DEBUG: {msg}"
  dbg_trace "  headerContext: {repr st.headerContext}"
  dbg_trace "  headerStack:   {repr st.headerStack}"
  dbg_trace (Format.pretty (s!"  Stack ({st.stack.size}):" ++ Format.nest 4 (Format.line ++ ppStack st.stack true)) 50)
  dbg_trace ""
  pure ()

structure DocListInfo where
  bullets : Array Syntax
deriving Repr, TypeName

open DocElabM

partial def elabInline (inline : Syntax) : DocElabM Unit :=
  withRef inline <|
  match inline with
  | `<low|(text ~(.atom _ s))> => do
    push <| ← ``(Inline.text $(quote s))
  | `<low|(linebreak ~(.atom _ s))> => do
    push <| ← ``(Inline.linebreak $(quote s))
  | `<low|(emph ~_open ~(.node _ `null args) ~_close)> => do
    within ``Inline.emph do
      array for a in args do elabInline a
  | _ =>
    dbg_trace "didn't understand inline {inline}"
    throwUnsupportedSyntax

partial def closeSectionsUntil (outer : Nat) : DocElabM Unit := do
  let some ⟨level, ptr, inPrelude⟩ := (← get).headerContext
    | throwError "Not at the section level"
  if outer ≤ level then
    -- Close the prelude if we're in it
    if let some i := inPrelude then
      mkArray i
    mkArray (ptr + 2) -- just after the prelude
    mkCApp ``Part.mk ptr
    modify fun st => {st with
      headerContext := some ⟨level - 1, st.headerStack.back, none⟩,
      headerStack := st.headerStack.pop
    }
    if outer < level then closeSectionsUntil outer

mutual
  partial def elabLi (block : Syntax) : DocElabM Syntax :=
    withRef block <|
    match block with
    | `<low| (li (bullet (column ~(.atom _ n)) ~dot) ~(.node _ `null args) )> => do
      within ``ListItem.mk do
        push ⟨Syntax.mkNumLit n⟩
        inBlock <| array do
          for b in args do
            elabBlock b
      pure dot
    | _ =>
      dbg_trace "unexpected block {block}"
      throwUnsupportedSyntax

  partial def elabBlock (block : Syntax) : DocElabM Unit :=
    withRef block <|
    match block with
    | `<low| (para ~(.node _ `null args) )> => do
      within ``Block.para do
        array do for i in args do elabInline i
    | `<low| (ul ~_ ~(.node _ `null itemStxs) )> => do
      within ``Block.ul do
        array do
          let mut bullets : Array Syntax := #[]
          for i in itemStxs do
            let b ← elabLi i
            bullets := bullets.push b
          let info := DocListInfo.mk bullets
          for b in bullets do
            pushInfoLeaf <| .ofCustomInfo {stx := b, value := Dynamic.mk info}
    | `<low| (blockquote ~_ ~(.node _ `null innerBlocks) )> => do
      within ``Block.blockquote <| inBlock <| array do
        for b in innerBlocks do elabBlock b
    | `<low| (code (column ~_col) ~_open ~_name ~_args ~(.atom _ contents) ~_close )> =>
      -- TODO name and args and indent
      within ``Block.code do
        push <| ← ``(Option.none)
        push <| ← ``(#[])
        push <| ← ``(0)
        push <| quote contents
    | `<low| (header ~(.atom _ hashes ) ~(.node _ `null inlines) ) > => do
      let some ⟨level, ptr, inPrelude⟩ := (← get).headerContext
        | throwErrorAt block "Can't put a header here"
      let lvl := hashes.length
      if lvl > level + 1 then throwErrorAt block "Wrong header nesting"
      -- Do we add a new subheader?
      else if lvl = level + 1 then
        -- If so, the prelude is done
        if let some ptr' := inPrelude then
          mkArray ptr'
          modify fun st => {st with headerContext := some ⟨level, ptr, none⟩}
        -- Push the current part start pointer, then save the current location as the start of the part
        modify fun st =>
          {st with
            headerContext := some {currentLevel := lvl, startIndex := st.stack.size, inPrelude := some (st.stack.size + 1)},
            headerStack := st.headerStack.push ptr
          }
      else
        closeSectionsUntil level
        -- Start a new section
        modify fun st => {st with
          headerContext := some {currentLevel := lvl, startIndex := st.stack.size, inPrelude := some st.stack.size}
        }
      array do for i in inlines do elabInline i
    | _ =>
      dbg_trace "unexpected block {block}"
      throwUnsupportedSyntax
end
