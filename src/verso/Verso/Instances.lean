/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Parser.Term
import Lean.Elab.Command
import Lean.Elab.Tactic.Doc
import Verso.Instances.Deriving

open Lean
open Syntax

open Lean Elab Command
open Lean.Parser.Term
open Lean.Parser.Command


instance : Quote String (k := ``docComment) where
  quote str := ⟨.node .none ``docComment #[ .atom .none "/--", .atom .none (str ++ "-/")]⟩

deriving instance Quote for String.Pos

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

instance : Quote NameSet where
  quote xs := mkCApp ``Std.TreeSet.ofList #[quote xs.toList, ⟨mkHole .missing⟩]
instance : ToJson NameSet where
  toJson xs := toJson (xs.toArray : Array Name)
instance : FromJson NameSet where
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
