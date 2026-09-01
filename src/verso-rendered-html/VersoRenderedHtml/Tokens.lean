/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public section

set_option linter.missingDocs true

namespace Verso.RenderedHtml

/--
The root token that a producer uses unless the fragment's own text contains it.
-/
def defaultRootToken : String := "%verso:root%"

/--
Checks whether a token occurs in a fragment's text.
-/
def hasToken (token : String) (text : String) : Bool :=
  !token.isEmpty && (text.splitOn token).length > 1

/--
Returns a root token that does not occur in a fragment's text.

It is `Verso.RenderedHtml.defaultRootToken`, uniquified when that token occurs in the text, so a
page whose prose spells the default token changes the token of one fragment and leaves the rest of
the directory unaffected.
-/
partial def chooseToken (text : String) : String :=
  if hasToken defaultRootToken text then attempt 1 else defaultRootToken
where
  attempt (i : Nat) : String :=
    let candidate := s!"%verso:root:{i}%"
    if hasToken candidate text then attempt (i + 1) else candidate

/--
Replaces every occurrence of a fragment's root token with the prefix at which the mounted content is
served.

A consumer chooses the prefix so that the token followed by `/x` resolves to `x` under the mount
point in the document that the consumer produces. Which prefix that is depends on the consuming
document: a page carrying a `<base href>` at the site root needs the mount path relative to the site
root, and a page without one needs a prefix relative to the page itself. The prefix carries no
trailing slash, because the content writes the separator.

Substitution is plain string replacement.
-/
def substitute (token : String) (root : String) (text : String) : String :=
  text.replace token root

end Verso.RenderedHtml
