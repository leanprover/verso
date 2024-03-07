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
