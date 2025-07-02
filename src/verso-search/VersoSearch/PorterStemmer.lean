
namespace Verso.Search.Stemmer.Porter

def isConsonant (str : String) (i : String.Pos) : Bool :=
  match str.get! i with
  | 'a' | 'e' | 'i' | 'o' | 'u' => false
  | 'y' =>
    if i = 0 then true
    else !isConsonant str (str.prev i)
  | _ => true
termination_by i.byteIdx
decreasing_by
  simp [String.prev, *, String.utf8PrevAux_lt_of_pos]


-- Measure of a word (number of VC patterns)
def measure (word : String) : Nat :=
  let rec aux (iter : String.Iterator) (inVowel : Bool) (count : Nat) : Nat :=
    if h : iter.hasNext then
      if !isConsonant iter.s iter.i then
        aux (iter.next' h) true count
      else if inVowel then
        aux (iter.next' h) false (count + 1)
      else
        aux (iter.next' h) false count
    else count
  termination_by iter.s.endPos.byteIdx - iter.i.byteIdx
  decreasing_by
    all_goals
      cases iter
      unfold String.Iterator.hasNext at h
      simp at h
      simp_all [String.next, String.Iterator.next', Char.utf8Size]
      repeat (split; omega)
      omega

  aux word.iter false 0

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

-- Check if word contains a vowel
def containsVowel (word : String) : Bool := Id.run do
  let mut iter := word.iter
  while h : iter.hasNext do
    if isConsonant word iter.i then iter := iter.next' h
    else return true
  return false


-- Check if word ends with double consonant
def endsWithDoubleConsonant (word : String) : Bool :=
  word.length ≥ 2 &&
    let i := word.prev word.endPos
    let j := word.prev i
    isConsonant word i && word.get! i == word.get! j


-- Check if word ends with cvc pattern where final c is not w, x, or y
def endsWithCvc (word : String) : Bool :=
  word.length ≥ 3 &&
    let i := word.prev word.endPos
    let j := word.prev i
    let k := word.prev j
    isConsonant word i && !isConsonant word j && isConsonant word k &&
      let ch := word.get! i
      ch != 'w' && ch != 'x' && ch != 'y'

-- Helper to remove suffix if conditions are met
def replaceSuffix (word : String) (suffix : String) (replacement : String)
  (condition : String → Bool) : String :=
  if word.endsWith suffix then
    let stem := word.dropRight suffix.length ++ replacement
    if condition stem then stem else word
  else word

structure Rule where
  suffix : String
  replacement : String
  condition : String → Bool := fun _ => true

def Rule.rw (suffix replacement : String) (condition : String → Bool := fun _ => true) : Rule := {suffix, replacement, condition}

def Rule.apply? (rule : Rule) (word : String) : Option String := do
  if word.endsWith rule.suffix then
    let word' := word.dropRight rule.suffix.length
    if rule.condition word' then
      return word' ++ rule.replacement
    else return word
  none


def applyRules (rules : List Rule) (word : String) : String := Id.run do
  for rule in rules do
    if let some word' := rule.apply? word then
      return word'
  return word

def applyRules? (rules : List Rule) (word : String) : Option String := Id.run do
  for rule in rules do
    if let some word' := rule.apply? word then return some word'
  return none

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

-- Step 1b
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
    let i := word.prev word.endPos
    let j := word.prev i
    if isConsonant word i && word.get! i == word.get! j && word.get! i ∉ ['l', 's', 'z'] then
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

-- Step 1c
def step1c (word : String) : String :=
  applyRules [.rw "y" "i" containsVowel] word

/-- info: "happi" -/
#guard_msgs in
#eval step1c "happy"

/-- info: "abiliti" -/
#guard_msgs in
#eval step1c "abiliti"

-- Step 2

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


-- Step 3
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


-- Step 5a
def step5a : String → String :=
  applyRules [
    .rw "e" "" fun w => measure w > 1 || (measure w == 1 && !endsWithCvc w)
  ]

-- Step 5b
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

-- Main Porter stemmer function
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


def trace (word : String) : IO Unit := do
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

def voc := include_str "../../../voc.txt"
def output := include_str "../../../output.txt"

def data := voc.splitOn "\n"
def outData := output.splitOn "\n"


/-- info: 0 failures -/
#guard_msgs in
#eval show IO Unit from do
  let mut failures := #[]
  for x in data, y in outData do
    let s := porterStem x
    unless s == y do
      failures := failures.push (x, s, y)
  IO.println s!"{failures.size} failures"
  for (x, s, y) in failures do
    IO.println s!"{x} --> {s} (wanted '{y}')"
