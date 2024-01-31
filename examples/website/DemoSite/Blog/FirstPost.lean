import Verso.Genre.Blog
import Verso.Parser
import Lean.Parser
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

#defineLexerBlock json ← jsonHl

#doc (Post) "First Post" =>
%%%
authors := ["Fictional Author"]
date := {year := 2008, month := 2, day := 15}
%%%

This post introduces the blog and says what it will do.

Here is some syntax-highlighted JSON:

```json
{"one thing": ["and", "another"],
 "and numbers": 1.5,
 "and more": [true, false, null, {}]}
```
