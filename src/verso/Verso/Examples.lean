/-
Copyright (c) 2023 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Std.Tactic.GuardMsgs

import Verso.Doc.Concrete


namespace Verso.Examples

set_option pp.rawOnError true

#docs (.none) noDoc "Nothing" :=
:::::::
:::::::

/-- info: Verso.Doc.Part.mk #[Verso.Doc.Inline.text "Nothing"] "Nothing" none #[] #[] -/
#guard_msgs in
  #eval noDoc

#docs (.none) a "My title here" :=
:::::::

Hello, I'm a paragraph. Yes I am!

:::::::



/--
info: Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "My title here"]
  "My title here"
  none
  #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "Hello, I'm a paragraph. Yes I am!"]]
  #[]
-/
#guard_msgs in
  #eval a

#docs (.none) a' "My title here" :=
:::::::

* Just a list with one item

:::::::

/--
info: Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "My title here"]
  "My title here"
  none
  #[Verso.Doc.Block.ul
      #[{ indent := 0, contents := #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "Just a list with one item"]] }]]
  #[]
-/
#guard_msgs in
  #eval a'


#docs (.none) b "My title here" :=
:::::::

# Section 1

a paragraph


:::::::

/--
info: Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "My title here"]
  "My title here"
  none
  #[]
  #[Verso.Doc.Part.mk
      #[Verso.Doc.Inline.text "Section 1"]
      "Section 1"
      none
      #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "a paragraph"]]
      #[]]
-/
#guard_msgs in
  #eval b

#docs (.none) c "My title here" :=
:::::::

# Section 1

a paragraph

## Section 1.1

More text:

* and a list
* with two
 * and nested



:::::::

/--
info: Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "My title here"]
  "My title here"
  none
  #[]
  #[Verso.Doc.Part.mk
      #[Verso.Doc.Inline.text "Section 1"]
      "Section 1"
      none
      #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "a paragraph"]]
      #[Verso.Doc.Part.mk
          #[Verso.Doc.Inline.text "Section 1.1"]
          "Section 1.1"
          none
          #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "More text:"],
            Verso.Doc.Block.ul
              #[{ indent := 0, contents := #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "and a list"]] },
                { indent := 0,
                  contents := #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "with two"],
                                Verso.Doc.Block.ul
                                  #[{ indent := 1,
                                      contents := #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "and nested"]] }]] }]]
          #[]]]
-/
#guard_msgs in
  #eval c

#docs (.none) d "More writing" :=
:::::::

# Section 1

Here's a quote;

> I like quotes
  * Also with lists in them

Also, 2 > 3.

:::::::

/--
info: Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "More writing"]
  "More writing"
  none
  #[]
  #[Verso.Doc.Part.mk
      #[Verso.Doc.Inline.text "Section 1"]
      "Section 1"
      none
      #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "Here's a quote;"],
        Verso.Doc.Block.blockquote
          #[(Verso.Doc.Block.para #[Verso.Doc.Inline.text "I like quotes"]),
            (Verso.Doc.Block.ul
               #[{ indent := 2,
                   contents := #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "Also with lists in them"]] }])],
        Verso.Doc.Block.para #[Verso.Doc.Inline.text "Also, 2 > 3."]]
      #[]]
-/
#guard_msgs in
  #eval d

#docs (.none) e "More writing" :=
:::::::

# Section 1

Here's some code

```
(define (zero f z) z)
(define (succ n) (lambda (f x) (f (n f z))))
```

:::::::

/--
info: Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "More writing"]
  "More writing"
  none
  #[]
  #[Verso.Doc.Part.mk
      #[Verso.Doc.Inline.text "Section 1"]
      "Section 1"
      none
      #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "Here's some code"],
        Verso.Doc.Block.code none #[] 0 "(define (zero f z) z)\n(define (succ n) (lambda (f x) (f (n f z))))\n"]
      #[]]
-/
#guard_msgs in
  #eval e

#docs (.none) f "More code writing" :=
:::::::

# Section 1

Here's some `code`!

```
(define (zero f z) z)
(define (succ n) (lambda (f x) (f (n f z))))
```

:::::::

/--
info: Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "More code writing"]
  "More code writing"
  none
  #[]
  #[Verso.Doc.Part.mk
      #[Verso.Doc.Inline.text "Section 1"]
      "Section 1"
      none
      #[Verso.Doc.Block.para
          #[Verso.Doc.Inline.text "Here's some ", Verso.Doc.Inline.code "code", Verso.Doc.Inline.text "!"],
        Verso.Doc.Block.code none #[] 0 "(define (zero f z) z)\n(define (succ n) (lambda (f x) (f (n f z))))\n"]
      #[]]
-/
#guard_msgs in
  #eval f

#docs (.none) g "Ref link before" :=
:::::::

# Section 1

[to here]: http://example.com

Here's [a link][to here]!

:::::::

/--
info: Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Ref link before"]
  "Ref link before"
  none
  #[]
  #[Verso.Doc.Part.mk
      #[Verso.Doc.Inline.text "Section 1"]
      "Section 1"
      none
      #[Verso.Doc.Block.para
          #[Verso.Doc.Inline.text "Here's ",
            Verso.Doc.Inline.link #[(Verso.Doc.Inline.text "a link")] "http://example.com", Verso.Doc.Inline.text "!"]]
      #[]]
-/
#guard_msgs in
  #eval g

#docs (.none) g' "Ref link after" :=
:::::::

# Section 1

Here's [a link][to here]!

[to here]: http://example.com

:::::::

/--
info: Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Ref link after"]
  "Ref link after"
  none
  #[]
  #[Verso.Doc.Part.mk
      #[Verso.Doc.Inline.text "Section 1"]
      "Section 1"
      none
      #[Verso.Doc.Block.para
          #[Verso.Doc.Inline.text "Here's ",
            Verso.Doc.Inline.link #[(Verso.Doc.Inline.text "a link")] "http://example.com", Verso.Doc.Inline.text "!"]]
      #[]]
-/
#guard_msgs in
  #eval g'
