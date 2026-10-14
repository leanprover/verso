module

import Errata
import all Verso.Doc.Lsp

/-!
Tests that Verso semantic tokens override Lean's tokens without hiding Lean highlighting in code.
-/

open Verso.Lsp

namespace VersoTests.SemanticTokens

private meta def tok (line start length type : Nat) : SemanticTokenEntry :=
  ⟨line, start, length, type, 0⟩

private meta def region (line start stop : Nat) : SemanticTokenRegion :=
  ⟨⟨line, start⟩, ⟨line, stop⟩⟩

#test_guard overlaySemanticTokens #[tok 0 2 6 18] #[tok 0 2 6 0] == #[tok 0 2 6 18]

#test_guard overlaySemanticTokens #[tok 0 3 2 18] #[tok 0 0 10 0] ==
  #[tok 0 0 3 0, tok 0 3 2 18, tok 0 5 5 0]

#test_guard overlaySemanticTokens #[tok 0 0 1 0, tok 0 9 1 0] #[tok 0 0 10 18] ==
  #[tok 0 0 1 0, tok 0 1 8 18, tok 0 9 1 0]

#test_guard overlaySemanticTokens #[tok 1 1 2 18] #[tok 0 1 2 0, tok 2 1 2 0] ==
  #[tok 0 1 2 0, tok 1 1 2 18, tok 2 1 2 0]

#test_guard
  mergeSemanticTokens
    { tokens := #[tok 0 1 12 18]
      regions := #[region 0 0 14]
      leanRegions := #[region 0 1 13] }
    #[tok 0 0 14 0, tok 0 1 12 0, tok 0 5 4 3, tok 0 10 2 0] ==
  #[tok 0 1 4 18, tok 0 5 4 3, tok 0 9 1 18, tok 0 10 2 0, tok 0 12 1 18]
