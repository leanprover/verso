/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

set_option linter.missingDocs true
set_option doc.verso true

namespace Verso.Search.Stemmer.Porter

/-!
This module implements a fairly naïve Porter stemmer, as described by the inventor
[here](https://tartarus.org/martin/PorterStemmer/). This is the algorithm used by
{lit}`elasticlunr.js`, so there's no need to use anything more powerful.

Profiling shows that index generation is fast, and costs are dominated by generating and emitting
JSON. If it ever becomes a performance bottleneck, there are a number of optimizations that can be
implemented:

 1. Rule selection can be smarter, based on string contents rather than just trying them
    top-to-bottom. Many rules are almost uniquely determined by the last or second-last letter of
    the word. See the linked page for more details.

 2. There is some unnecessary allocation of strings. A substring could be profitably used when
    shortening strings, and setting values when lengthening them, similarly to a Lisp fill pointer
    or C byte array.

This implementation is based off the declarative description on the web page, rather than the C
reference implementation or the paper, and it is tested against Porter's provided input data.
-/

/--
Checks whether the character at position {name}`i` is a consonant. {lean}`'y'` is a consonant if not
preceded by a consonant.
-/
def isConsonant (i : String.ValidPos str) : Bool :=
  match i.get! with
  | 'a' | 'e' | 'i' | 'o' | 'u' => false
  | 'y' =>
    if h : i = str.startValidPos then true
    else !isConsonant (i.prev h)
  | _ => true
termination_by i.offset.byteIdx
decreasing_by
  simp only [String.ValidPos.prev, ← i.offset_toSlice, String.Slice.Pos.ofset_ofSlice, ← String.Pos.Raw.lt_iff, ← String.Slice.Pos.lt_iff]
  exact String.Slice.Pos.prev_lt

/--
The measure of a word is the number of v+c+ clusters (vowels followed by consonants).
-/
def measure (word : String) : Nat :=
  let rec aux (pos : String.ValidPos word) (inVowel : Bool) (count : Nat) : Nat :=
    if h : pos = word.endValidPos then count
    else
      let next := pos.next h
      if !isConsonant pos then
        aux next true count
      else if inVowel then
        aux next false (count + 1)
      else
        aux next false count
  termination_by word.endValidPos.offset.byteIdx - pos.offset.byteIdx
  decreasing_by
    all_goals
    apply Nat.sub_lt_sub_left
    . apply String.ValidPos.byteIdx_lt_utf8ByteSize
      grind
    . simp [String.ValidPos.offset_next, (pos.get h).utf8Size_pos]

  aux word.startValidPos false 0

/-- info: 0 -/
#guard_msgs in
#eval measure "tr"
/-- info: 0 -/
#guard_msgs in
#eval measure "ee"
/-- info: 0 -/
#guard_msgs in
#eval measure "tree"

/-- info: 2 -/
#guard_msgs in
#eval measure "private"

/--
Checks whether the provided word contains a vowel.
-/
def containsVowel (word : String) : Bool := Id.run do
  let mut pos := word.startValidPos
  repeat
    let some next := pos.next?
      | break
    if isConsonant pos then pos := next
    else return true
  return false

/--
Checks whether the word ends with a double consonant.
-/
def endsWithDoubleConsonant (word : String) : Bool :=
  let endPos := word.endValidPos
  if h : endPos = word.startValidPos then false
  else
    let i :=  endPos.prev h
    if h : i = word.startValidPos then false
    else
      let j := i.prev h
      isConsonant i && i.get! == j.get!

/--
Checks whether a word ends with a CVC pattern where the final consonant is not {lean}`'w'`,
{lean}`'x'`, or {lean}`'y'`.
-/
def endsWithCvc (word : String) : Bool :=
  let endPos := word.endValidPos
  if h : endPos = word.startValidPos then false
  else
    let i := endPos.prev h
    if hi : i = word.startValidPos then false
    else
      let j := i.prev hi
      if hj : j = word.startValidPos then false
      else
        let k := j.prev hj
        isConsonant i && !isConsonant j && isConsonant k &&
        let ch := i.get!
        ch != 'w' && ch != 'x' && ch != 'y'

/--
Replaces the given {name}`suffix` with {name}`replacement` if the remaining word after removing the suffix
satisfies the {name}`condition`.
-/
def replaceSuffix (word : String) (suffix : String) (replacement : String)
  (condition : String → Bool) : String :=
  if word.endsWith suffix then
    let stem := word.dropRight suffix.length ++ replacement
    if condition stem then stem else word
  else word

/--
A rule, as described in Porter's paper.
-/
structure Rule where
  /-- A suffix that must match exactly. -/
  suffix : String
  /-- A replacement in case the suffix and condition match -/
  replacement : String
  /-- A condition that must be fulfilled by the word up to the suffix. -/
  condition : String → Bool := fun _ => true

/-- A convenience function for constructing a rewrite rule. -/
def Rule.rw (suffix replacement : String) (condition : String → Bool := fun _ => true) : Rule :=
  { suffix, replacement, condition }

/-- Applies a rule to a string, returning the modified string if it matches. -/
def Rule.apply? (rule : Rule) (word : String) : Option String := do
  if word.endsWith rule.suffix then
    let word' := word.dropRight rule.suffix.length
    if rule.condition word' then
      return word' ++ rule.replacement
    else return word
  none

/--
Returns the result of applying the first rule that matches, or the original string if none match.
-/
def applyRules (rules : List Rule) (word : String) : String := Id.run do
  for rule in rules do
    if let some word' := rule.apply? word then
      return word'
  return word

/--
Returns the result of applying the first rule that matches, or {name}`none` if none match.
-/
def applyRules? (rules : List Rule) (word : String) : Option String := Id.run do
  for rule in rules do
    if let some word' := rule.apply? word then return some word'
  return none

/--
Step 1a of Porter's algorithm. Simplifies plural markers.
-/
def step1a : String → String :=
  applyRules [
    .rw "sses" "ss",
    .rw "ies" "i",
    .rw "ss" "ss",
    .rw "s" ""
  ]

/-- info: "abiliti" -/
#guard_msgs in
#eval step1a "abilities"

/--
Step 1b of Porter's algorithm.
-/
def step1b (word : String) : String :=
  if let some w := (Rule.rw "eed" "ee" (measure · > 0)).apply? word then w
  else if let some w := applyRules? [.rw "ed" "" containsVowel, .rw "ing" "" containsVowel] word then
    if w != word then extra w else word
  else word
where
  extra (word : String) : String := Id.run do
    if word.endsWith "at" then return word ++ "e"
    if word.endsWith "bl" then return word ++ "e"
    if word.endsWith "iz" then return word ++ "e"
    let endPos := word.endValidPos
    let some i := endPos.prev?
      | return word
    let some j := i.prev?
      | return word
    if isConsonant i && i.get! == j.get! && i.get! ∉ ['l', 's', 'z'] then
      return word.dropRight 1
    if measure word == 1 && endsWithCvc word then return word ++ "e"
    word


/-- info: "abiliti" -/
#guard_msgs in
#eval step1b "abiliti"

/-- info: "caress" -/
#guard_msgs in
#eval step1b (step1a "caresses")
/-- info: "poni" -/
#guard_msgs in
#eval step1b (step1a "ponies")
/-- info: "ti" -/
#guard_msgs in
#eval step1b (step1a "ties")
/-- info: "caress" -/
#guard_msgs in
#eval step1b (step1a "caress")
/-- info: "cat" -/
#guard_msgs in
#eval step1b (step1a "cats")

/-- info: "feed" -/
#guard_msgs in
#eval step1b (step1a "feed")
/-- info: "agree" -/
#guard_msgs in
#eval step1b (step1a "agreed")
/-- info: "disable" -/
#guard_msgs in
#eval step1b (step1a "disabled")

/-- info: "mat" -/
#guard_msgs in
#eval step1b (step1a "matting")
/-- info: "mate" -/
#guard_msgs in
#eval step1b (step1a "mating")
/-- info: "meet" -/
#guard_msgs in
#eval step1b (step1a "meeting")
/-- info: "mill" -/
#guard_msgs in
#eval step1b (step1a "milling")
/-- info: "mess" -/
#guard_msgs in
#eval step1b (step1a "messing")

/-- info: "meet" -/
#guard_msgs in
#eval step1b (step1a "meetings")

/--
Step 1c of Porter's algorithm.
-/
def step1c (word : String) : String :=
  applyRules [.rw "y" "i" containsVowel] word

/-- info: "happi" -/
#guard_msgs in
#eval step1c "happy"

/-- info: "abiliti" -/
#guard_msgs in
#eval step1c "abiliti"


/--
Step 2 of Porter's algorithm. Simplifies many common suffixes.
-/
def step2 (word : String) : String := Id.run do
  unless measure word > 0 do return word
  for (s, s') in suffixes do
    let rule := Rule.mk s s' (measure · > 0)
    if let some w := rule.apply? word then return w
  word
where
  suffixes := [
    ("ational", "ate"),
    ("ization", "ize"),
    ("iveness", "ive"),
    ("fulness", "ful"),
    ("ousness", "ous"),
    ("tional", "tion"),
    ("biliti", "ble"),
    ("entli", "ent"),
    ("ousli", "ous"),
    ("ation", "ate"),
    ("alism", "al"),
    ("aliti", "al"),
    ("iviti", "ive"),
    ("enci", "ence"),
    ("anci", "ance"),
    ("izer", "ize"),
    ("alli", "al"),
    ("ator", "ate"),
    ("logi", "log"),
    ("bli", "ble"),
    ("eli", "e")]

/-- info: "sensible" -/
#guard_msgs in
#eval step2 "sensibiliti"

/-- info: "abiliti" -/
#guard_msgs in
#eval step2 "abiliti"


/--
Step 3 of Porter's algorithm. Simplifies further common suffixes.
-/
def step3 (word : String) : String := Id.run do
  unless measure word > 0 do return word
  for (s, s') in suffixes do
    let rule := Rule.mk s s' (measure · > 0)
    if let some w := rule.apply? word then return w
  word
where
  suffixes := [
    ("icate", "ic"),
    ("ative", ""),
    ("alize", "al"),
    ("iciti", "ic"),
    ("ical", "ic"),
    ("ful", ""),
    ("ness", "")
  ]

/-- info: "form" -/
#guard_msgs in
#eval step3 "formative"

/-- info: "able" -/
#guard_msgs in
#eval step3 "able"

/--
Step 4 of Porter's algorithm. Removes many derivational suffixes.
-/
def step4 : String → String :=
  applyRules rules
where
  rules : List Rule := [
    .mk "ance" "" (measure · > 1),
    .mk "ence" "" (measure · > 1),
    .mk "able" "" (measure · > 1),
    .mk "ible" "" (measure · > 1),
    .mk "ement" "" (measure · > 1),
    .mk "ment" "" (measure · > 1),
    .mk "ent" "" (measure · > 1),
    .mk "ant" "" (measure · > 1),
    .mk "ion" "" fun w => measure w > 1 && (w.endsWith "s" || w.endsWith "t"),
    .mk "ism" "" (measure · > 1),
    .mk "ate" "" (measure · > 1),
    .mk "iti" "" (measure · > 1),
    .mk "ous" "" (measure · > 1),
    .mk "ive" "" (measure · > 1),
    .mk "ize" "" (measure · > 1),
    .mk "ou" "" (measure · > 1),
    .mk "er" "" (measure · > 1),
    .mk "al" "" (measure · > 1),
    .mk "ic" "" (measure · > 1)]

/--
Step 5a of Porter's algorithm. Removes extra trailing {lean}`'e'`.
-/
def step5a : String → String :=
  applyRules [
    .rw "e" "" fun w => measure w > 1 || (measure w == 1 && !endsWithCvc w)
  ]

/--
Step 5b of Porter's algorithm. Converts trailing {lean}`"ll"` to {lean}`"l"`.
-/
def step5b (word : String) : String :=
  if measure word > 1 ∧ endsWithDoubleConsonant word ∧ word.endsWith "l" then
    word.dropRight 1
  else word



/-- info: "control" -/
#guard_msgs in
#eval step5b "controll"
/-- info: "roll" -/
#guard_msgs in
#eval step5b "roll"

/--
Heuristically computes the stem of an English word using
[Martin Porter's algorithm](https://tartarus.org/martin/PorterStemmer/).
-/
def porterStem (word : String) : String :=
  if word.length <= 2 then word
  else
    let word := word.toLower
    let word := step1a word
    let word := step1b word
    let word := step1c word
    let word := step2 word
    let word := step3 word
    let word := step4 word
    let word := step5a word
    let word := step5b word
    word

-- Debugging function
private def trace (word : String) : IO Unit := do
  if word.length <= 2 then IO.println s!"Short: {word}"
  else
    let word := word.toLower
    IO.println s!"Lower: {word}"
    let word := step1a word
    IO.println s!"1a: {word}"
    let word := step1b word
    IO.println s!"1b: {word}"
    let word := step1c word
    IO.println s!"1c: {word}"
    let word := step2 word
    IO.println s!"2: {word}"
    let word := step3 word
    IO.println s!"3: {word}"
    let word := step4 word
    IO.println s!"4: {word}"
    let word := step5a word
    IO.println s!"5a: {word}"
    let word := step5b word
    IO.println s!"5b: {word}"
