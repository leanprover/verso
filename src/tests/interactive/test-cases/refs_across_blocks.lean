import Verso

/-!
These tests check go to definition and document highlight for links and footnotes whose definitions
and uses are in different top-level blocks. They cover requests while the document elaborates and
after it has finished. They matter when changing how Verso records link and footnote definitions
and uses for the editor, or the language server handlers that answer these requests.

In this section, each top-level block of the `#doc` document is its own command, so each answer
combines definitions and uses from several snapshots. The requests are, in order: go to definition
and highlight from a link use and a footnote use before their definitions, highlight from the link
definition, and go to definition from a link use and a footnote use after their definitions. The
`#docs` document `otherDoc` defines the same link label `site`. Highlight on its use lists only its
own use and definition.

Each answer lists the definition, or the definition and every use, of the label in the same
document. An answer without a definition in a later block would mean that the request read only
the snapshot under the cursor. An answer with a range in `otherDoc` would mean that the requests
confused the two documents.
-/

#docs (.none) otherDoc "Other" :=
:::::::
Another [use][site].
            --^ sync
            --^ textDocument/documentHighlight

[site]: https://example.org
:::::::

#doc (.none) "Links and footnotes across blocks" =>

A [forward link][site] and a forward footnote.[^note]
               --^ textDocument/definition
               --^ textDocument/documentHighlight
                                              --^ textDocument/definition
                                              --^ textDocument/documentHighlight

[site]: https://example.com
--^ textDocument/documentHighlight

[^note]: A footnote.

A [backward link][site] and a backward footnote.[^note]
                --^ textDocument/definition
                                                --^ textDocument/definition
-- RESET
import Verso

/-!
Go to definition and highlight answer while the document is still elaborating. The answers use the
top-level blocks that have finished.

The `waitFor` directive waits for the error message of the block `{marker}[]`, so the blocks before
it have finished. The role `slow` then keeps the document elaborating for ten seconds, well after
the requests are answered. The answers list the definitions and uses before `{slow}[]`, and none of
the uses in the last block. An answer with the last block's uses would mean that the request
waited for the end of the document.
-/

open Verso Doc Elab

@[role]
def slow : RoleExpanderOf Unit
  | (), _ => do
    IO.sleep 10000
    ``(Inline.text "slow")

#doc (.none) "Before the document finishes" =>
--^ waitFor: No registered role `marker`.

A [forward link][site] and a forward footnote.[^note]
               --^ textDocument/definition
               --^ textDocument/documentHighlight
                                              --^ textDocument/definition
                                              --^ textDocument/documentHighlight

[site]: https://example.com

[^note]: A footnote.

A [backward link][site] and a backward footnote.[^note]
                --^ textDocument/definition

{marker}[]

{slow}[]

A [late link][site] and a late footnote.[^note]
-- RESET
import Verso

/-!
A link and a footnote with the same label are separate. Definitions and uses in different parts of
one document are related.

In the `#docs` document, a link and a footnote both have the label `same`. Go to definition and
highlight from the link list only the link's definition and use. Highlight from the footnote lists
only the footnote's. An answer that mixed them would mean that the requests ignored which kind of
label each is.

In the `#doc` document, the uses are in the first section, and the definitions are in a subsection
of the second section. The third section has another use. Go to definition and highlight find the
definitions and uses in the other sections. An answer without the definitions would mean that each
part was treated as its own document.
-/

#docs (.none) kinds "Kinds" :=
:::::::
A [link][same] and a footnote.[^same]
       --^ sync
       --^ textDocument/definition
       --^ textDocument/documentHighlight
                              --^ textDocument/documentHighlight

[same]: https://example.com/same

[^same]: The footnote.
:::::::

#doc (.none) "Parts" =>

# First section

A [link][same] and a footnote.[^same]
       --^ textDocument/definition
       --^ textDocument/documentHighlight
                              --^ textDocument/definition
                              --^ textDocument/documentHighlight

# Second section

## A subsection

[same]: https://example.com/same

[^same]: The footnote.

# Third section

Another [link][same].
             --^ textDocument/definition
-- RESET
import Verso

/-!
Requests from a use in a failing block work, and their answers include that use.

A failing block leaves its definitions and uses out of the document's state in the environment. Go
to definition and highlight from the use of `site` in the failing block still work, and the
highlight lists that use. An answer taken only from the environment would leave out the use under
the cursor.
-/

#doc (.none) "Failing block" =>

A [link][site].

A failing block with a [link][site] and {nosuchrole}[x].
                            --^ sync
                            --^ textDocument/definition
                            --^ textDocument/documentHighlight

[site]: https://example.com/site

The end.
-- RESET
import Verso

/-!
Go to definition and highlight work from uses in a footnote's contents whose definitions come later
in the document. The answers point into this file.
-/

#doc (.none) "Footnote contents" =>

A sentence with a footnote.[^note]

[^note]: A footnote with a [link][site] and another footnote.[^later]
                                  --^ sync
                                  --^ textDocument/definition
                                  --^ textDocument/documentHighlight
                                                              --^ textDocument/definition
                                                              --^ textDocument/documentHighlight

[site]: https://example.com/site

[^later]: The later footnote.
