/-
Copyright (c) 2023 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Rob Simmons
-/
import Errata
import Verso
namespace Verso.RefsTest
set_option guard_msgs.diff true

/-!
These tests check link and footnote resolution in documents elaborated with `#docs`, which doesn't
do block-level incrementality.  They also check the messages about undefined uses, unused
definitions and duplicate definitions.

A use of a label resolves to the definition with that label in the same document. When Verso
finishes the document, it checks the links and footnotes. A use without a definition is an error,
and a definition without a use is a warning.

Each test elaborates a small document. Some tests observe the messages and their order. Others
evaluate `toPart` and observe the URL or footnote contents that each use resolved to.
-/

/- ----- -/

#docs (.none) regularLink "Regular link" :=
:::::::
Here's [a link](http://example.com)
:::::::
/--
info: Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Regular link"]
  "Regular link"
  none
  #[Verso.Doc.Block.para
      #[Verso.Doc.Inline.text "Here's ",
        Verso.Doc.Inline.link #[(Verso.Doc.Inline.text "a link")] "http://example.com"]]
  #[]
-/
#test_msgs in
  #eval regularLink.toPart


/- ----- -/

#docs (.none) refLink "Ref link" :=
:::::::
Here's [a link][to here]

[to here]: http://example.com
:::::::
/--
info: Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Ref link"]
  "Ref link"
  none
  #[Verso.Doc.Block.para
      #[Verso.Doc.Inline.text "Here's ",
        Verso.Doc.Inline.link #[(Verso.Doc.Inline.text "a link")] "http://example.com"]]
  #[]
-/
#test_msgs in
  #eval refLink.toPart


/- ----- -/

#docs (.none) noteLink "Footnote" :=
:::::::
Here's something that needs context[^note]!

[^note]: The footnote text
:::::::
/--
info: Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Footnote"]
  "Footnote"
  none
  #[Verso.Doc.Block.para
      #[Verso.Doc.Inline.text "Here's something that needs context",
        Verso.Doc.Inline.footnote "note" #[(Verso.Doc.Inline.text "The footnote text")], Verso.Doc.Inline.text "!"]]
  #[]
-/
#test_msgs in
  #eval noteLink.toPart


/- ----- -/

instance : BEq (Doc.Part Doc.Genre.none) where
  beq x y := BEq.beq (self := Doc.instBEqPart) x y

#docs (.none) refAndLink "Ref/link ordering" :=
:::::::
[to here]: http://example.com

Here's [a link][to here][^note]!

[^note]: The footnote text
:::::::
/--
info: Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Ref/link ordering"]
  "Ref/link ordering"
  none
  #[Verso.Doc.Block.para
      #[Verso.Doc.Inline.text "Here's ", Verso.Doc.Inline.link #[(Verso.Doc.Inline.text "a link")] "http://example.com",
        Verso.Doc.Inline.footnote "note" #[(Verso.Doc.Inline.text "The footnote text")], Verso.Doc.Inline.text "!"]]
  #[]
-/
#test_msgs in
  #eval refAndLink.toPart

#docs (.none) refAndLink2 "Ref/link ordering" :=
:::::::
Here's [a link][to here][^note]!

[to here]: http://example.com
[^note]: The footnote text
:::::::

#docs (.none) refAndLink3 "Ref/link ordering" :=
:::::::
[to here]: http://example.com
[^note]: The footnote text

Here's [a link][to here][^note]!
:::::::

#docs (.none) refAndLink4 "Ref/link ordering" :=
:::::::
[^note]: The footnote text

Here's [a link][to here][^note]!

[to here]: http://example.com
:::::::

/-- info: true -/
#test_msgs in #eval refAndLink.toPart == refAndLink2.toPart

/-- info: true -/
#test_msgs in #eval refAndLink.toPart == refAndLink3.toPart

/-- info: true -/
#test_msgs in #eval refAndLink.toPart == refAndLink4.toPart

#docs (.none) refAndLinkRecursion "Ref/link recursion" :=
:::::::
[^nestedTwice]: C'mon, man.

[^nestedOnce]: A footnote?[^nestedTwice]

[to here]: http://example.com
[^plain]: Footnotes can have recursive footnotes[^nestedOnce] and [links][to here].

Example[^plain]
:::::::
/--
info: Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Ref/link recursion"]
  "Ref/link recursion"
  none
  #[Verso.Doc.Block.para
      #[Verso.Doc.Inline.text "Example",
        Verso.Doc.Inline.footnote
          "plain"
          #[(Verso.Doc.Inline.text "Footnotes can have recursive footnotes"),
            (Verso.Doc.Inline.footnote
               "nestedOnce"
               #[(Verso.Doc.Inline.text "A footnote?"),
                 (Verso.Doc.Inline.footnote "nestedTwice" #[(Verso.Doc.Inline.text "C'mon, man.")])]),
            (Verso.Doc.Inline.text " and "),
            (Verso.Doc.Inline.link #[(Verso.Doc.Inline.text "links")] "http://example.com"),
            (Verso.Doc.Inline.text ".")]]]
  #[]
-/
#test_msgs in
  #eval refAndLinkRecursion.toPart

/-
A duplicate link definition error states where the first definition is.

The document defines the link label `foo` twice. The error is at the second definition. It specifies
the label, the position of the first definition, and both URLs.
-/

/--
error: Duplicate definition of link label [foo]. It is already defined at line 194, column 1, with the URL 'https://example.com'. This definition has the URL 'http://example.com'.
-/
#test_msgs in
#docs (.none) failDupLink "Fail" :=
:::::::
[foo]: https://example.com
[foo]: http://example.com

[Go to foo][foo]!
:::::::

/-
A duplicate footnote definition error states where the first definition is.

The document defines the footnote label `note` twice. The error is at the second definition.
-/

/--
error: Duplicate definition of footnote label [^note]. It is already defined at line 212, column 2.
-/
#test_msgs in
#docs (.none) failDupFoot "Fail" :=
:::::::
[^note]: Note

[^note]: Note2

There are no caveats.[^note]
:::::::

/-
A footnote's contents may use a footnote that is defined later in the document.
-/

#docs (.none) footnoteUsesLaterFootnote "Later footnote" :=
:::::::
A sentence with a footnote.[^foo]

[^foo]: A footnote that uses a later one.[^bar]

[^bar]: The later footnote.
:::::::

/--
info: Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Later footnote"]
  "Later footnote"
  none
  #[Verso.Doc.Block.para
      #[Verso.Doc.Inline.text "A sentence with a footnote.",
        Verso.Doc.Inline.footnote
          "foo"
          #[(Verso.Doc.Inline.text "A footnote that uses a later one."),
            (Verso.Doc.Inline.footnote "bar" #[(Verso.Doc.Inline.text "The later footnote.")])]]]
  #[]
-/
#test_msgs in
  #eval footnoteUsesLaterFootnote.toPart

/-
A footnote's contents may use a link that is defined later in the document.
-/

#docs (.none) footnoteUsesLaterLink "Later link" :=
:::::::
A sentence with a footnote.[^foo]

[^foo]: A footnote with a [later link][bar].

[bar]: http://example.com
:::::::

/--
info: Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Later link"]
  "Later link"
  none
  #[Verso.Doc.Block.para
      #[Verso.Doc.Inline.text "A sentence with a footnote.",
        Verso.Doc.Inline.footnote
          "foo"
          #[(Verso.Doc.Inline.text "A footnote with a "),
            (Verso.Doc.Inline.link #[(Verso.Doc.Inline.text "later link")] "http://example.com"),
            (Verso.Doc.Inline.text ".")]]]
  #[]
-/
#test_msgs in
  #eval footnoteUsesLaterLink.toPart

/-
A footnote whose contents use the footnote itself, directly or through other footnotes, is an
error. The error lists the labels of the other footnotes in the cycle. The use that closes the cycle
has empty contents.
-/

/--
error: Footnote [^x] is used inside its own contents, through [^y]
---
error: Footnote [^self] is used inside its own contents
---
error: Footnote [^p] is used inside its own contents, through [^q] and [^r]
-/
#test_msgs in
#docs (.none) footnoteCycle "Footnote cycle" :=
:::::::
A sentence with three footnotes.[^x][^self][^p]

[^x]: The first footnote uses the second.[^y]

[^y]: The second footnote uses the first.[^x]

[^self]: A footnote that uses itself.[^self]

[^p]: The first of three uses the second.[^q]

[^q]: The second of three uses the third.[^r]

[^r]: The third of three uses the first.[^p]
:::::::

/--
info: Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Footnote cycle"]
  "Footnote cycle"
  none
  #[Verso.Doc.Block.para
      #[Verso.Doc.Inline.text "A sentence with three footnotes.",
        Verso.Doc.Inline.footnote
          "x"
          #[(Verso.Doc.Inline.text "The first footnote uses the second."),
            (Verso.Doc.Inline.footnote
               "y"
               #[(Verso.Doc.Inline.text "The second footnote uses the first."), (Verso.Doc.Inline.footnote "x" #[])])],
        Verso.Doc.Inline.footnote
          "self"
          #[(Verso.Doc.Inline.text "A footnote that uses itself."), (Verso.Doc.Inline.footnote "self" #[])],
        Verso.Doc.Inline.footnote
          "p"
          #[(Verso.Doc.Inline.text "The first of three uses the second."),
            (Verso.Doc.Inline.footnote
               "q"
               #[(Verso.Doc.Inline.text "The second of three uses the third."),
                 (Verso.Doc.Inline.footnote
                    "r"
                    #[(Verso.Doc.Inline.text "The third of three uses the first."),
                      (Verso.Doc.Inline.footnote "p" #[])])])]]]
  #[]
-/
#test_msgs in
  #eval footnoteCycle.toPart


/-
Warnings about unused definitions appear in source order.
-/

/--
warning: Unused footnote [^baz]
---
warning: Unused footnote [^hidden]
-/
#test_msgs in
#docs (.none) fail4 "Fail" :=
:::::::
[^baz]: Unused footnote

[^hidden]: Unused footnote
:::::::

/--
error: No definition for footnote [^caveat]
-/
#test_msgs in
#docs (.none) fail "Fail" :=
:::::::
There's no caveat.[^caveat]
:::::::

/--
warning: Unused link [forlorn]
-/
#test_msgs in
#docs (.none) warnForlorn "Fail" :=
:::::::
[forlorn]: http://example.com
:::::::

/--
error: No definition for link [fourOhFour]
-/
#test_msgs in
#docs (.none) failHangingLink "Fail" :=
:::::::
There's no [destination][fourOhFour]
:::::::

/-
Every undefined use and every unused definition is reported, in source order.

The document has undefined uses, including two uses of `[one]`, and definitions without uses. Each
undefined use gets its own error, and each unused definition gets a warning.
-/

/--
error: No definition for link [one]
---
warning: Unused footnote [^unused]
---
error: No definition for footnote [^two]
---
error: No definition for link [one]
---
warning: Unused link [spare]
---
error: No definition for link [three]
-/
#test_msgs in
#docs (.none) severalUndefined "Several undefined uses" :=
:::::::
First [use][one].

[^unused]: A footnote that nothing uses.

A footnote use.[^two]

Second [use][one].

[spare]: https://example.com/spare

Third [use][three].
:::::::

/-
A document with undefined uses is still defined, and its blocks still compile.
-/

/--
error: No definition for link [missing]
---
error: No definition for footnote [^absent]
-/
#test_msgs in
#docs (.none) undefinedStillCompiles "Undefined uses" :=
:::::::
A [link][missing] and a footnote.[^absent] A [defined link][present].

[present]: https://example.com/present
:::::::

/--
info: Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Undefined uses"]
  "Undefined uses"
  none
  #[Verso.Doc.Block.para
      #[Verso.Doc.Inline.text "A ", Verso.Doc.Inline.link #[(Verso.Doc.Inline.text "link")] "",
        Verso.Doc.Inline.text " and a footnote.", Verso.Doc.Inline.footnote "absent" #[], Verso.Doc.Inline.text " A ",
        Verso.Doc.Inline.link #[(Verso.Doc.Inline.text "defined link")] "https://example.com/present",
        Verso.Doc.Inline.text "."]]
  #[]
-/
#test_msgs in
  #eval undefinedStillCompiles.toPart

/-
Each use resolves to the definition in its own document, even when another document in the same
module defines the same label.
-/

#docs (.none) sameNameFirst "First" :=
:::::::
A [link][shared].[^shared]

[shared]: https://example.com/first
[^shared]: The first document's footnote.
:::::::

#docs (.none) sameNameSecond "Second" :=
:::::::
[shared]: https://example.com/second
[^shared]: The second document's footnote.

A [link][shared].[^shared]
:::::::

/--
info: Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "First"]
  "First"
  none
  #[Verso.Doc.Block.para
      #[Verso.Doc.Inline.text "A ", Verso.Doc.Inline.link #[(Verso.Doc.Inline.text "link")] "https://example.com/first",
        Verso.Doc.Inline.text ".",
        Verso.Doc.Inline.footnote "shared" #[(Verso.Doc.Inline.text "The first document's footnote.")]]]
  #[]
-/
#test_msgs in
  #eval sameNameFirst.toPart

/--
info: Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Second"]
  "Second"
  none
  #[Verso.Doc.Block.para
      #[Verso.Doc.Inline.text "A ",
        Verso.Doc.Inline.link #[(Verso.Doc.Inline.text "link")] "https://example.com/second", Verso.Doc.Inline.text ".",
        Verso.Doc.Inline.footnote "shared" #[(Verso.Doc.Inline.text "The second document's footnote.")]]]
  #[]
-/
#test_msgs in
  #eval sameNameSecond.toPart

/-
A link use in a header's title resolves.

A header's title is elaborated in the document's root term, outside any block. The URL in the value
of the document shows that uses in the root term resolve too.
-/

#docs (.none) headerLink "Header link" :=
:::::::
# A [header][h]

[h]: https://example.com/header
:::::::

/--
info: Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Header link"]
  "Header link"
  none
  #[]
  #[Verso.Doc.Part.mk
      #[Verso.Doc.Inline.text "A ",
        Verso.Doc.Inline.link #[(Verso.Doc.Inline.text "header")] "https://example.com/header"]
      "A  header"
      none
      #[]
      #[]]
-/
#test_msgs in
  #eval headerLink.toPart

/-
Link uses resolve in a block that a part command adds without its own
`blockInternalDocReconstructionPlaceholder`.

The part command `plainDirective` adds such a block. The value of the document shows the URL of the
link use in it. For such a block, `addBlock` binds the context's `docReconstructionPlaceholder`.
Without this binding, elaboration would fail with an unknown identifier.
-/

section
open Lean Elab Verso.Doc.Elab PartElabM

@[part_command Lean.Doc.Parser.Block.directive]
meta def plainDirective : PartCommand
  | .directive v => do
    unless v.name.getId == `plain do throwUnsupportedSyntax
    let blocks ← liftDocElabM <| v.content.mapM elabBlock
    addBlock (← ``(Verso.Doc.Block.concat #[$blocks,*]))
  | _ => throwUnsupportedSyntax

end

#docs (.none) partCommandBlock "Part command block" :=
:::::::
[ref]: https://example.com/part-command

:::plain
A [link][ref].
:::
:::::::

/--
info: Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Part command block"]
  "Part command block"
  none
  #[Verso.Doc.Block.concat
      #[(Verso.Doc.Block.para
           #[Verso.Doc.Inline.text "A ",
             Verso.Doc.Inline.link #[(Verso.Doc.Inline.text "link")] "https://example.com/part-command",
             Verso.Doc.Inline.text "."])]]
  #[]
-/
#test_msgs in
  #eval partCommandBlock.toPart

/-
An error in a footnote's contents is reported once, at the footnote.

The role `illTyped` gives the footnote's contents a type error, and the error appears once.
Footnote contents are elaborated twice: at the definition, where their errors are reported, and in
the document's root term. Contents with errors are recorded as empty, so the root term has no error
to report.
-/

section
open Verso.Doc.Elab

/-- A role that elaborates to an ill-typed inline. -/
@[role]
def illTyped : RoleExpanderOf Unit
  | (), _ => ``(Verso.Doc.Inline.text (5 : Nat))

end

/--
error: Application type mismatch: The argument
  5
has type
  Nat
but is expected to have type
  String
in the application
  Doc.Inline.text 5
-/
#test_msgs in
#docs (.none) footnoteError "Footnote error" :=
:::::::
Text.[^a]

[^a]: A {illTyped}[] body.
:::::::
