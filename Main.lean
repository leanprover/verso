import LeanDoc

open LeanDoc Doc Html Concrete ToHtml

set_option pp.rawOnError true

def main : IO Unit := do
  IO.println <| Html.format <| Html.embody <| toHtml <| #doc "My wonderful document" =>

This is an example document. There's still bogus syntax highlighting
and no LSP features, but it does seem to run things.

# Next steps

There are a number of basic things to fix:

 * Emphasis isn't how it should be - there's only one kind (*no bold!*)
 * No inline code or math or numbered lists yet
 * The parser is a bit of a kludge, with too much lookahead making up for lack of a clear structure
 * Custom directives are block-only for now, and are not yet extensible with custom elaborators

For demo-worthiness, we also need:

 * Fancier LSP support - at least highlight list elements and show the breadcrumbs
   * Some works now, but it's hacky
 * Still, it's fun!
