/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import SubVerso.Examples
open SubVerso.Examples

%example Tree
inductive Tree (α : Type u) : Type u where
  | leaf
  | branch (left : Tree α) (val : α) (right : Tree α)
%end

%example Tree.flip
def Tree.flip : Tree α → Tree α
  | .leaf => .leaf
  | .branch l v r => %ex{flopped}{.branch r.flip v l.flip}
%end

%show_name Tree.flip as FLIP
