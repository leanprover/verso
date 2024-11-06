/-
Copyright (c) 2023 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Verso.Doc.Elab
import Verso.Doc.Html
import Verso.Output
import Verso.Output.Html
import Verso.Doc.Concrete
import Verso.Doc.Lsp

import VersoBlog
import VersoManual

open Verso Doc Output Html Concrete ToHtml Elab Monad
open Lean Elab Term

set_option pp.rawOnError true

@[role_expander vanish]
def vanish : RoleExpander
   | _args, _stxs => pure #[]

@[role_expander rev]
def rev : RoleExpander
  | _args, stxs => .reverse <$> stxs.mapM elabInline

def html [Monad m] (doc : Part .none) : m Html := (·.fst) <$> Genre.none.toHtml {logError := fun _ => pure ()} () () {} {} {} doc .empty

def main : IO Unit := do
  IO.println <| Html.asString <| Html.embody <| ← html <| #doc (.none) "My wonderful document" =>

This is an example document. There's still bogus syntax highlighting
and no LSP features, but it does seem to run things.

There is *bold* and _emphasis_ available.

# Next steps

There are a number of basic things to fix:

 * No math or numbered lists yet
 * The parser is a bit of a kludge, with too much lookahead making up
   for lack of a clear structure
 * Custom roles/directives are not yet extensible with custom elaborators
 * Gratuitous line breaks a la GitHub-flavored Markdown in rendering

For demo-worthiness, we also need:

 * Fancier LSP support - at least highlight list elements and show the breadcrumbs
   * Some works now, but it's hacky
   * Only Emacs seems to show the bullet point highlights, so I need VS Code help
   * Still, it's *fun*!
 * At least one or two "global" document operations, like resolving cross-references
 * Embedded Lean examples with elaboration

As someone said:

> It's still a start! And we have `inline code`. And {vanish}[there can be secrets and] {rev}[documents *in* code].

```
Block code too
```

[foo][my link][^foo]

## Other idea

[my link]: https://example.com

[^foo]: blah blah blah *BLAH*!

## Further subsection
