/-
Copyright (c) 2023 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Verso
namespace Verso.BasicTest
set_option guard_msgs.diff true
set_option pp.rawOnError true


/- ----- -/

#docs (.none) noDoc "Nothing" :=
:::::::
:::::::
/-- info: Verso.Doc.Part.mk #[Verso.Doc.Inline.text "Nothing"] "Nothing" none #[] #[] -/
#guard_msgs in
  #eval noDoc.force


/- ----- -/

#docs (.none) littleParagraph "My title here" :=
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
  #eval littleParagraph.force


/- ----- -/

#docs (.none) listOneItem "My title here" :=
:::::::

* Just a list with one item

:::::::
/--
info: Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "My title here"]
  "My title here"
  none
  #[Verso.Doc.Block.ul #[{ contents := #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "Just a list with one item"]] }]]
  #[]
-/
#guard_msgs in
  #eval listOneItem.force


/- ----- -/

#docs (.none) sectionAndPara "My title here" :=
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
  #eval sectionAndPara.force


/- ----- -/

#docs (.none) nestedDoc1 "My title here" :=
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
              #[{ contents := #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "and a list"]] },
                { contents := #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "with two"],
                                Verso.Doc.Block.ul
                                  #[{ contents := #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "and nested"]] }]] }]]
          #[]]]
-/
#guard_msgs in
  #eval nestedDoc1.force


/- ----- -/

#docs (.none) nestedDoc2 "My title here" :=
:::::::

# Section 1

a paragraph

## Section 1.1

More text:

1. and a list
2. with two
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
            Verso.Doc.Block.ol
              1
              #[{ contents := #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "and a list"]] },
                { contents := #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "with two"]] }],
            Verso.Doc.Block.ul #[{ contents := #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "and nested"]] }]]
          #[]]]
-/
#guard_msgs in
  #eval nestedDoc2.force


/- ----- -/

#docs (.none) nestedDoc3 "My title here" :=
:::::::

# Section 1

a paragraph

## Section 1.1

More text:

: A list

  a list

: With stuff

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
            Verso.Doc.Block.dl
              #[{ term := #[Verso.Doc.Inline.text " A list"],
                  desc := #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "a list"]] },
                { term := #[Verso.Doc.Inline.text " With stuff"],
                  desc := #[Verso.Doc.Block.ul
                              #[{ contents := #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "and nested"]] }]] }]]
          #[]]]
-/
#guard_msgs in
  #eval nestedDoc3.force


/- ----- -/

#docs (.none) nestedDoc4 "More writing" :=
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
               #[{ contents := #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "Also with lists in them"]] }])],
        Verso.Doc.Block.para #[Verso.Doc.Inline.text "Also, 2 > 3."]]
      #[]]
-/
#guard_msgs in
  #eval nestedDoc4.force


/- ----- -/

-- https://github.com/leanprover/verso/pull/541
/-- error: Wrong header nesting - got #### but expected at most ### -/
#guard_msgs in
#docs (.none) h "Bad nesting" :=
:::::::

# Section
## Subsection
#### Sub^3section

:::::::
