/-
Copyright (c) 2023 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Rob Simmons
-/
import Verso
namespace Verso.RefsTest
set_option guard_msgs.diff true

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
#guard_msgs in
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
#guard_msgs in
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
#guard_msgs in
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
#guard_msgs in
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
#guard_msgs in #eval refAndLink.toPart == refAndLink2.toPart

/-- info: true -/
#guard_msgs in #eval refAndLink.toPart == refAndLink3.toPart

/-- info: true -/
#guard_msgs in #eval refAndLink.toPart == refAndLink4.toPart

/--
error: Already defined link [foo] as 'https://example.com'
-/
#guard_msgs in
#docs (.none) failDupLink "Fail" :=
:::::::
[foo]: https://example.com
[foo]: http://example.com

[Go to foo][foo]!
:::::::

/--
error: Already defined footnote [^note]
-/
#guard_msgs in
#docs (.none) failDupFoot "Fail" :=
:::::::
[^note]: Note

[^note]: Note2

There are no caveats.[^note]
:::::::

/--
error: Footnote reference [^bar] is not defined yet when it occurs
-/
#guard_msgs in
#docs (.none) failForwardRef "Fail" :=
:::::::
[^foo]: Disallowing forward reference in footnotes[^bar]

[^bar]: Even though it's defined later

And used[^bar]
:::::::

/--
warning: Unused footnote [^hidden]
---
warning: Unused footnote [^baz]
-/
#guard_msgs in
#docs (.none) fail4 "Fail" :=
:::::::
[^baz]: Unused footnote

[^hidden]: Unused footnote
:::::::

/--
error: No definition for footnote [^caveat]
-/
#guard_msgs in
#docs (.none) fail "Fail" :=
:::::::
There's no caveat.[^caveat]
:::::::

/--
warning: Unused link [forlorn]
-/
#guard_msgs in
#docs (.none) warnForlorn "Fail" :=
:::::::
[forlorn]: http://example.com
:::::::

/--
error: No definition for link [fourOhFour]
-/
#guard_msgs in
#docs (.none) failHangingLink "Fail" :=
:::::::
There's no [destination][fourOhFour]
:::::::
