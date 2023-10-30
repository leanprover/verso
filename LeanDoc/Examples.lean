import Std.Tactic.GuardMsgs

import LeanDoc.Doc.Concrete


namespace LeanDoc.Examples

set_option pp.rawOnError true

#docs none "Nothing" :=
:::::::
:::::::

/-- info: LeanDoc.Doc.Part.mk #[LeanDoc.Doc.Inline.text "Nothing"] #[] #[] -/
#guard_msgs in
  #eval none

#docs a "My title here" :=
:::::::

Hello, I'm a paragraph. Yes I am!

:::::::



/--
info: LeanDoc.Doc.Part.mk
  #[LeanDoc.Doc.Inline.text "My title here"]
  #[LeanDoc.Doc.Block.para #[LeanDoc.Doc.Inline.text "Hello, I'm a paragraph. Yes I am!"]]
  #[]
-/
#guard_msgs in
  #eval a


#docs b "My title here" :=
:::::::

# Section 1

a paragraph


:::::::

/--
info: LeanDoc.Doc.Part.mk
  #[LeanDoc.Doc.Inline.text "My title here"]
  #[]
  #[LeanDoc.Doc.Part.mk
      #[LeanDoc.Doc.Inline.text "Section 1"]
      #[LeanDoc.Doc.Block.para #[LeanDoc.Doc.Inline.text "a paragraph"]]
      #[]]
-/
#guard_msgs in
  #eval b

#docs c "My title here" :=
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
info: LeanDoc.Doc.Part.mk
  #[LeanDoc.Doc.Inline.text "My title here"]
  #[]
  #[LeanDoc.Doc.Part.mk
      #[LeanDoc.Doc.Inline.text "Section 1"]
      #[LeanDoc.Doc.Block.para #[LeanDoc.Doc.Inline.text "a paragraph"]]
      #[LeanDoc.Doc.Part.mk
          #[LeanDoc.Doc.Inline.text "Section 1.1"]
          #[LeanDoc.Doc.Block.para #[LeanDoc.Doc.Inline.text "More text:"],
            LeanDoc.Doc.Block.ul
              #[{ indent := 0,
                  contents := #[LeanDoc.Doc.Block.para
                                  #[LeanDoc.Doc.Inline.text "and a list", LeanDoc.Doc.Inline.linebreak "\n"]] },
                { indent := 0,
                  contents := #[LeanDoc.Doc.Block.para
                                  #[LeanDoc.Doc.Inline.text "with two", LeanDoc.Doc.Inline.linebreak "\n"],
                                LeanDoc.Doc.Block.ul
                                  #[{ indent := 1,
                                      contents := #[LeanDoc.Doc.Block.para
                                                      #[LeanDoc.Doc.Inline.text "and nested"]] }]] }]]
          #[]]]
-/
#guard_msgs in
  #eval c

#docs d "More writing" :=
:::::::

# Section 1

Here's a quote;

> I like quotes
  * Also with lists in them

Also, 2 > 3.

:::::::

/--
info: LeanDoc.Doc.Part.mk
  #[LeanDoc.Doc.Inline.text "More writing"]
  #[]
  #[LeanDoc.Doc.Part.mk
      #[LeanDoc.Doc.Inline.text "Section 1"]
      #[LeanDoc.Doc.Block.para #[LeanDoc.Doc.Inline.text "Here's a quote;"],
        LeanDoc.Doc.Block.blockquote
          #[LeanDoc.Doc.Block.para #[LeanDoc.Doc.Inline.text "I like quotes", LeanDoc.Doc.Inline.linebreak "\n"],
            LeanDoc.Doc.Block.ul
              #[{ indent := 2,
                  contents := #[LeanDoc.Doc.Block.para #[LeanDoc.Doc.Inline.text "Also with lists in them"]] }]],
        LeanDoc.Doc.Block.para #[LeanDoc.Doc.Inline.text "Also, 2 > 3."]]
      #[]]
-/
#guard_msgs in
  #eval d

-- TODO buggy parsing of backtick (but probably a lean token parser issue)
#docs e "More writing" :=
:::::::

# Section 1

Here's some code

``` code
(define (zero f z) z)
(define (succ n) (lambda (f x) (f (n f z))))
```

:::::::

/--
info: LeanDoc.Doc.Part.mk
  #[LeanDoc.Doc.Inline.text "More writing"]
  #[]
  #[LeanDoc.Doc.Part.mk
      #[LeanDoc.Doc.Inline.text "Section 1"]
      #[LeanDoc.Doc.Block.para #[LeanDoc.Doc.Inline.text "Here's some code"],
        LeanDoc.Doc.Block.code none #[] 0 "(define (zero f z) z)\n(define (succ n) (lambda (f x) (f (n f z))))\n"]
      #[]]
-/
#guard_msgs in
  #eval e

