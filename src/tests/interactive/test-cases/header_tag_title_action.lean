import VersoManual
--^ sync

/-!
Tests that `headerTagActions` offers the header tag linter's quick fixes for the document's title on
the title's line. The comment with the request is the document's first block, so the fixes insert a
metadata block before it.
-/

set_option linter.verso.manual.headerTags true

#doc (Verso.Genre.Manual) "Fallen Leaves" =>
                          --^ codeAction

Leaves fall from the trees in autumn.
