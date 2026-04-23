/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
import Lean.Parser.Term
import Lean.Elab.Command
import Lean.Elab.Tactic.Doc
public import Lean.Data.Position
public import Lean.Message
public import Lean.Data.Lsp
public import Lean.Elab.Tactic.Doc
meta import Verso.Instances.Deriving

open Lean
open Syntax

open Lean Elab Command
open Lean.Parser.Term
open Lean.Parser.Command


instance : Quote String (k := ``docComment) where
  quote str := ⟨.node .none ``docComment #[ .atom .none "/--", .atom .none (str ++ "-/")]⟩

deriving instance Quote for String.Pos.Raw

deriving instance Quote for SourceInfo

deriving instance Quote for Position

deriving instance Quote for Int

deriving instance Quote for System.FilePath

deriving instance Quote for MessageSeverity

deriving instance Quote for Lsp.Position

deriving instance Quote for Lsp.Range

deriving instance Quote for BinderInfo
deriving instance ToJson for BinderInfo
deriving instance FromJson for BinderInfo

deriving instance Quote for QuotKind
deriving instance ToJson for QuotKind
deriving instance FromJson for QuotKind

deriving instance Quote for DefinitionSafety
deriving instance ToJson for DefinitionSafety
deriving instance FromJson for DefinitionSafety

public instance : Quote NameSet where
  quote xs := mkCApp ``Std.TreeSet.ofList #[quote xs.toList, ⟨mkHole .missing⟩]
public instance : ToJson NameSet where
  toJson xs := toJson (xs.toArray : Array Name)
public instance : FromJson NameSet where
  fromJson? xs := do
    let arr ← fromJson? (α := Array Name) xs
    pure <| Std.TreeSet.ofArray arr _
deriving instance Repr for NameSet

section
open Lean.Elab.Tactic.Doc

deriving instance Quote for TacticDoc
deriving instance ToJson for TacticDoc
deriving instance FromJson for TacticDoc
deriving instance Repr for TacticDoc

end

deriving instance TypeName for String

deriving instance Repr for OpenDecl

/--
Hashes a `Float` by its IEEE 754 bit pattern. `+0.0` and `-0.0` are collapsed to the same hash to
preserve the `BEq`/`Hashable` contract (they compare equal under `BEq Float`, but have different
bit patterns). It is provided so that structures containing `Float` fields can derive `Hashable`.

`NaN` values are hashed consistently by bit pattern. This trivially preserves the `BEq`/`Hashable`
contract: `BEq Float` follows IEEE semantics and reports every `NaN` as distinct from every value
including itself, so the contract holds vacuously.
-/
public instance : Hashable Float where
  hash x :=
    if x == 0.0 then hash (0 : UInt64)
    else hash x.toBits

public instance : ToJson (Fin n) where
  toJson i := toJson i.val

public instance : FromJson (Fin n) where
  fromJson? v := do
    let i : Nat ← fromJson? v
    if h : i < n then return ⟨i, h⟩
    else throw s!"Expected a value less than {n} but got {i}"
