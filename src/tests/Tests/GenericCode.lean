/-
Copyright (c) 2023 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Verso
namespace Verso.GenericCodeTest
set_option guard_msgs.diff true
set_option pp.rawOnError true


/- ----- -/

#docs (.none) code1 "More writing" :=
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
        Verso.Doc.Block.code "(define (zero f z) z)\n(define (succ n) (lambda (f x) (f (n f z))))\n"]
      #[]]
-/
#guard_msgs in
  #eval code1.toPart
/--
info: Verso.Output.Html.tag
  "section"
  #[]
  (Verso.Output.Html.seq
    #[Verso.Output.Html.tag "h1" #[] (Verso.Output.Html.seq #[Verso.Output.Html.text true "More writing"]),
      Verso.Output.Html.tag
        "section"
        #[]
        (Verso.Output.Html.seq
          #[Verso.Output.Html.tag "h2" #[] (Verso.Output.Html.seq #[Verso.Output.Html.text true "Section 1"]),
            Verso.Output.Html.tag "p" #[] (Verso.Output.Html.seq #[Verso.Output.Html.text true "Here's some code"]),
            Verso.Output.Html.tag
              "pre"
              #[]
              (Verso.Output.Html.text true "(define (zero f z) z)\n(define (succ n) (lambda (f x) (f (n f z))))\n")])])
-/
#guard_msgs in
  #eval Doc.Genre.none.toHtml (m:=Id) {logError := fun _ => ()} () () {} {} {} code1.toPart |>.run .empty |>.fst


/- ----- -/

#docs (.none) code2 "More code writing" :=
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
        Verso.Doc.Block.code "(define (zero f z) z)\n(define (succ n) (lambda (f x) (f (n f z))))\n"]
      #[]]
-/
#guard_msgs in
  #eval code2.toPart
