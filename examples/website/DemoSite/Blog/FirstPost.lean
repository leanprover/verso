/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoBlog
import Lean.Parser
import Verso.Parser
open Verso Genre Blog LexedText

open Lean.Parser in
open Verso.Parser in
def jsonHl : Highlighter where
  name := "json"
  lexer :=
    token `brace (chFn '{' <|> chFn '}') <|>
    token `arr (chFn '[' <|> chFn ']') <|>
    token `delim (chFn ',' <|> chFn ':') <|>
    token `bool (strFn "true" <|> strFn "false") >> notFollowedByFn (satisfyFn Char.isAlphanum) "number or letter" <|>
    token `null (strFn "null" <|> strFn "false") <|>
    token `num (many1Fn (satisfyFn Char.isDigit) >> optionalFn (chFn '.' >> many1Fn (satisfyFn Char.isDigit))) <|>
    token `str (chFn '"' >> manyFn (satisfyEscFn (· != '"')) >> chFn '"') <|>
    token `ident (many1Fn (satisfyFn (· ∉ "() \t\n".toList)))
  tokenClass := fun s => some (toString s.getKind)

define_lexed_text json ← jsonHl

#doc (Post) "First Post" =>


This post introduces the blog and says what it will do.

Here is some syntax-highlighted JSON:

```json
{"one thing": ["and", "another"],
 "and numbers": 1.5,
 "and more": [true, false, null, {}]}
```

And a random code block:
```
hello
```

Verso supports [links][named link] defined later!

[named link]: https://lean-lang.org
