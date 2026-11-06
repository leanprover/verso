/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import VersoGen.TextEdit.Basic

set_option doc.verso true

/-!
Reordering of a sequence of replacements in a way that keeps the text that they give. Two
consecutive replacements are exchanged when neither touches the other, and their positions are
adjusted. Theorems show that an exchange keeps the final text, and so does a reordering made of
exchanges.
-/

namespace VersoGen.TextEdit

/-! # Bytes -/

section

open ByteArray

/-- Bytes extracted up to a point at or after the end are the bytes up to the end. -/
private theorem byteArray_extract_eq_extract_size_of_le {a : ByteArray} {i j : Nat}
    (h : a.size ≤ j) :
    a.extract i j = a.extract i a.size := by
  ext1
  simp only [data_extract]
  exact Array.extract_eq_extract_right.2 (by simp only [size_data]; grind)

/--
The first bytes of an append, up to a point in its left part, are the first bytes of that part.
-/
private theorem byteArray_extract_zero_append_of_le_size {a b : ByteArray} {i : Nat}
    (h : i ≤ a.size) :
    (a ++ b).extract 0 i = a.extract 0 i := by
  rw [extract_append, Nat.sub_eq_zero_of_le h, Nat.zero_sub, extract_same, append_empty]

/--
The first bytes of an append, up to a point in its right part, are its left part followed by the
first bytes of its right part.
-/
private theorem byteArray_extract_zero_append_size_add {a b : ByteArray} {k : Nat} :
    (a ++ b).extract 0 (a.size + k) = a ++ b.extract 0 k := by
  rw [extract_append, Nat.add_sub_cancel_left, Nat.zero_sub,
    byteArray_extract_eq_extract_size_of_le (by grind), extract_zero_size]

/-- The last bytes of an append, from a point in its right part, are the last bytes of that part. -/
private theorem byteArray_extract_append_size_add_size {a b : ByteArray} {k : Nat} :
    (a ++ b).extract (a.size + k) (a ++ b).size = b.extract k b.size := by
  rw [size_append, extract_append_size_add]

/--
The last bytes of an append, from a point in its left part, are the last bytes of the left part
followed by the right part.
-/
private theorem byteArray_extract_append_size_of_le_size {a b : ByteArray} {i : Nat}
    (h : i ≤ a.size) : (a ++ b).extract i (a ++ b).size = a.extract i a.size ++ b := by
  rw [extract_append, size_append, Nat.sub_eq_zero_of_le h, Nat.add_sub_cancel_left,
    extract_zero_size, byteArray_extract_eq_extract_size_of_le (a := a) (by grind)]

/--
The bytes between two points of the bytes between two outer points are the bytes between the two
inner points, moved by the first outer point.
-/
private theorem byteArray_extract_extract_of_le {a : ByteArray} {i j k l : Nat} (hl : i + l ≤ j) :
    (a.extract i j).extract k l = a.extract (i + k) (i + l) := by
  rw [extract_extract, Nat.min_eq_left hl]

/--
The bytes of {name}`X` with the bytes from {name}`start` up to {name}`stop` replaced by {name}`T`.
-/
private def replaceBytes (X : ByteArray) (start stop : Nat) (T : ByteArray) : ByteArray :=
  X.extract 0 start ++ T ++ X.extract stop X.size

/--
Two byte replacements that don't overlap can be made in either order. Replacing the bytes from
{name}`fs` to {name}`fe` with {name}`T1` and then the bytes from {name}`a` to {name}`b`, moved by
the first replacement's change, with {name}`T2` gives the same bytes as making the second
replacement first.
-/
private theorem replaceBytes_replaceBytes_comm {X T1 T2 : ByteArray} {fs fe a b : Nat}
    (h1 : fs ≤ fe) (h2 : fe ≤ a) (h3 : a ≤ b) (h4 : b ≤ X.size) :
    replaceBytes (replaceBytes X fs fe T1) (fs + T1.size + (a - fe)) (fs + T1.size + (b - fe)) T2 =
      replaceBytes (replaceBytes X a b T2) fs fe T1 := by
  simp only [replaceBytes]
  have hP : (X.extract 0 fs ++ T1).size = fs + T1.size := by
    simp only [size_append, size_extract]; grind
  have hA : (X.extract 0 a).size = a := by simp only [size_extract]; grind
  rw [← hP, byteArray_extract_zero_append_size_add, byteArray_extract_append_size_add_size,
    byteArray_extract_zero_append_of_le_size (by simp only [size_append]; grind),
    byteArray_extract_zero_append_of_le_size (by grind),
    byteArray_extract_append_size_of_le_size (by simp only [size_append]; grind),
    byteArray_extract_append_size_of_le_size (by grind)]
  simp only [size_extract]
  rw [byteArray_extract_extract_of_le (by grind), byteArray_extract_extract_of_le (by grind),
    byteArray_extract_extract_of_le (by grind), byteArray_extract_extract_of_le (by grind)]
  simp only [Nat.add_zero, Nat.zero_add, Nat.min_self, Nat.sub_zero, append_assoc]
  rw [show fe + (a - fe) = a by grind, show fe + (b - fe) = b by grind,
    show fe + (X.size - fe) = X.size by grind, Nat.min_eq_left (by grind : a ≤ X.size)]

/--
Two byte replacements that don't overlap can be made in either order, with the positions of the
second one after the first one given as {name}`ss` and {name}`se`.
-/
private theorem replaceBytes_replaceBytes_comm_of_eq {X T1 T2 : ByteArray} {fs fe a b ss se : Nat}
    (h1 : fs ≤ fe) (h2 : fe ≤ a) (h3 : a ≤ b) (h4 : b ≤ X.size)
    (hss : ss = fs + T1.size + (a - fe)) (hse : se = fs + T1.size + (b - fe)) :
    replaceBytes (replaceBytes X fs fe T1) ss se T2 =
      replaceBytes (replaceBytes X a b T2) fs fe T1 := by
  subst hss hse
  exact replaceBytes_replaceBytes_comm h1 h2 h3 h4

end

/-! # Positions in Strings -/

section

open String String.Pos.Raw

/-- The text before a valid position has as many bytes as the position's offset. -/
private theorem utf8ByteSize_extract_startPos {s : String} {p : String.Pos.Raw} (hp : p.IsValid s) :
    (s.extract s.startPos (s.pos p hp)).utf8ByteSize = p.byteIdx := by
  have := hp.le_utf8ByteSize
  rw [← size_toByteArray]
  simp only [toByteArray_extract, offset_pos, offset_startPos, ByteArray.size_extract,
    size_toByteArray, byteIdx_zero]
  grind

/-- The text before a valid position, followed by the text after it, is the whole string. -/
private theorem extract_startPos_append_extract_endPos {s : String} {p : String.Pos.Raw}
    (hp : p.IsValid s) :
    s.extract s.startPos (s.pos p hp) ++ s.extract (s.pos p hp) s.endPos = s := by
  simp only [← toByteArray_inj, toByteArray_append, toByteArray_extract, offset_pos,
    offset_startPos, offset_endPos, ByteArray.extract_append_extract, byteIdx_rawEndPos]
  simp [← size_toByteArray]

/-- Valid positions at or before {name}`p` are valid in the text before {name}`p`. -/
private theorem isValid_extract_startPos {s : String} {p q : String.Pos.Raw} (hp : p.IsValid s)
    (hq : q.IsValid s) (hle : q ≤ p) : q.IsValid (s.extract s.startPos (s.pos p hp)) := by
  rw [← extract_startPos_append_extract_endPos hp, isValid_append] at hq
  rcases hq with hq | ⟨hend, -⟩
  · exact hq
  · have hsize := utf8ByteSize_extract_startPos hp
    have : q = (s.extract s.startPos (s.pos p hp)).rawEndPos := by
      simp only [le_iff, byteIdx_rawEndPos] at hend hle
      ext; simp only [byteIdx_rawEndPos]; grind
    exact this ▸ isValid_rawEndPos

/--
Valid positions at or after {name}`p` are valid in the text after {name}`p`, counted from
{name}`p`.
-/
private theorem isValid_unoffsetBy_extract_endPos {s : String} {p q : String.Pos.Raw}
    (hp : p.IsValid s) (hq : q.IsValid s) (hle : p ≤ q) :
    (q.unoffsetBy p).IsValid (s.extract (s.pos p hp) s.endPos) := by
  have hsize := utf8ByteSize_extract_startPos hp
  rw [← extract_startPos_append_extract_endPos hp, isValid_append] at hq
  rcases hq with hq | ⟨-, hq⟩
  · have hq' := hq.le_utf8ByteSize
    have : q.unoffsetBy p = 0 := by
      simp only [le_iff] at hle; ext; simp only [byteIdx_unoffsetBy, byteIdx_zero]; grind
    exact this ▸ isValid_zero
  · have : q.unoffsetBy p = q - s.extract s.startPos (s.pos p hp) := by
      ext; simp only [byteIdx_unoffsetBy, byteIdx_sub_string]; grind
    exact this ▸ hq

/-- Valid positions in the text before {name}`p` are valid in the whole string. -/
private theorem isValid_of_isValid_extract_startPos {s : String} {p q : String.Pos.Raw}
    {hp : p.IsValid s} (hq : q.IsValid (s.extract s.startPos (s.pos p hp))) : q.IsValid s := by
  rw [← extract_startPos_append_extract_endPos hp]
  exact hq.append_right _

/--
Valid positions in the text after {name}`p`, counted from {name}`p`, are valid in the whole string
when they are counted from the start.
-/
private theorem isValid_offsetBy_of_isValid_extract_endPos {s : String} {p q : String.Pos.Raw}
    {hp : p.IsValid s} (hq : q.IsValid (s.extract (s.pos p hp) s.endPos)) :
    (q.offsetBy p).IsValid s := by
  have hsize := utf8ByteSize_extract_startPos hp
  have := hq.append_left (s.extract s.startPos (s.pos p hp))
  rw [extract_startPos_append_extract_endPos hp] at this
  have heq : q.offsetBy p = s.extract s.startPos (s.pos p hp) + q := by
    ext; simp only [byteIdx_offsetBy, byteIdx_string_add]; grind
  exact heq ▸ this

end

open String.Pos.Raw

/-! # Positions before and after a Replacement -/

namespace Replacement

open String

/--
Replacements with valid positions in order apply and give the text before their start, their new
text and the text after their stop.
-/
theorem apply?_eq_of_isValid {r : Replacement} {s : String} (hstart : r.start.IsValid s)
    (hstop : r.stop.IsValid s) (hle : r.start ≤ r.stop) :
    r.apply? s = some (s.extract s.startPos (s.pos r.start hstart) ++ r.text ++
      s.extract (s.pos r.stop hstop) s.endPos) :=
  apply?_eq_some_iff.2 ⟨hstart, hstop, hle, rfl⟩

/-- The bytes of a replacement's result are the replacement made on the bytes. -/
theorem toByteArray_eq_of_apply?_eq_some {r : Replacement} {s t : String}
    (h : r.apply? s = some t) : t.toByteArray =
      replaceBytes s.toByteArray r.start.byteIdx r.stop.byteIdx r.text.toByteArray := by
  obtain ⟨-, -, -, rfl⟩ := apply?_eq_some_iff.1 h
  simp [replaceBytes]

/-- Valid positions at or before a replacement's start are valid in its result. -/
theorem isValid_of_apply?_eq_some_of_le_start {r : Replacement} {s t : String} {q : String.Pos.Raw}
    (h : r.apply? s = some t) (hq : q.IsValid s) (hle : q ≤ r.start) : q.IsValid t := by
  obtain ⟨hstart, -, -, rfl⟩ := apply?_eq_some_iff.1 h
  exact ((isValid_extract_startPos hstart hq hle).append_right _).append_right _

/--
Valid positions of a replacement's result at or before its start are valid in the text that the
replacement applies to.
-/
theorem isValid_of_apply?_eq_some_of_le_start' {r : Replacement} {s t : String} {q : String.Pos.Raw}
    (h : r.apply? s = some t) (hq : q.IsValid t) (hle : q ≤ r.start) : q.IsValid s := by
  obtain ⟨hstart, hstop, -, rfl⟩ := apply?_eq_some_iff.1 h
  have hsize := utf8ByteSize_extract_startPos hstart
  rw [isValid_append, isValid_append] at hq
  rcases hq with (hq | ⟨hend, -⟩) | ⟨hend, -⟩
  · exact isValid_of_isValid_extract_startPos (hp := hstart) hq
  all_goals
    have : q = r.start := by
      simp only [le_iff, byteIdx_rawEndPos, utf8ByteSize_append] at hend hle; ext; grind
    exact this ▸ hstart

/--
Valid positions at or after a replacement's stop are valid in its result, moved by the change in
length.
-/
theorem isValid_of_apply?_eq_some_of_stop_le {r : Replacement} {s t : String} {q : String.Pos.Raw}
    (h : r.apply? s = some t) (hq : q.IsValid s) (hle : r.stop ≤ q) :
    ((q.unoffsetBy r.stop).offsetBy (r.start + r.text)).IsValid t := by
  obtain ⟨hstart, hstop, -, rfl⟩ := apply?_eq_some_iff.1 h
  have hsize := utf8ByteSize_extract_startPos hstart
  have := (isValid_unoffsetBy_extract_endPos hstop hq hle).append_left
    (s.extract s.startPos (s.pos r.start hstart) ++ r.text)
  have heq : (q.unoffsetBy r.stop).offsetBy (r.start + r.text) =
      s.extract s.startPos (s.pos r.start hstart) ++ r.text + q.unoffsetBy r.stop := by
    ext; simp only [byteIdx_offsetBy, byteIdx_add_string, byteIdx_string_add, utf8ByteSize_append]
    grind
  exact heq ▸ this

/--
Valid positions of a replacement's result at or after its new text are valid in the text that the
replacement applies to, moved back by the change in length.
-/
theorem isValid_of_apply?_eq_some_of_stop_le' {r : Replacement} {s t : String} {q : String.Pos.Raw}
    (h : r.apply? s = some t) (hq : q.IsValid t) (hle : r.start + r.text ≤ q) :
    ((q.unoffsetBy (r.start + r.text)).offsetBy r.stop).IsValid s := by
  obtain ⟨hstart, hstop, -, rfl⟩ := apply?_eq_some_iff.1 h
  have hsize := utf8ByteSize_extract_startPos hstart
  rw [isValid_append] at hq
  rcases hq with hq | ⟨-, hq⟩
  · have := hq.le_utf8ByteSize
    have : (q.unoffsetBy (r.start + r.text)).offsetBy r.stop = r.stop := by
      simp only [le_iff, byteIdx_add_string, utf8ByteSize_append] at hle this
      ext; simp only [byteIdx_offsetBy, byteIdx_unoffsetBy, byteIdx_add_string]; grind
    rw [this]
    exact hstop
  · have heq : (q.unoffsetBy (r.start + r.text)).offsetBy r.stop =
        (q - (s.extract s.startPos (s.pos r.start hstart) ++ r.text)).offsetBy r.stop := by
      ext; simp only [byteIdx_offsetBy, byteIdx_unoffsetBy, byteIdx_add_string,
        byteIdx_sub_string, utf8ByteSize_append]; grind
    exact heq ▸ isValid_offsetBy_of_isValid_extract_endPos (hp := hstop) hq

end Replacement

/-! # Exchanging Two Replacements -/

/--
Exchanges two consecutive replacements. {name}`first` applies before {name}`second`, whose positions
are in the text that {name}`first` gives. The result applies the second replacement first and then
the first one. The second one's positions are in the text before {name}`first`, and the first one's
positions are in the text that the second one gives. The result is {name}`none` when the two
replacements touch or overlap.
-/
public def swap (first second : Replacement) : Option (Replacement × Replacement) :=
  let firstInsertedStop := first.start + first.text
  if firstInsertedStop < second.start then
    -- The second replacement is after the first one's new text, so before the first one it is
    -- after the first one's stop.
    let back (p : String.Pos.Raw) := (p.unoffsetBy firstInsertedStop).offsetBy first.stop
    some ({ second with start := back second.start, stop := back second.stop }, first)
  else if second.stop < first.start then
    -- The second replacement is before the first one, which moves by the second one's change.
    let shift (p : String.Pos.Raw) :=
      (p.unoffsetBy second.stop).offsetBy (second.start + second.text)
    some (second, { first with start := shift first.start, stop := shift first.stop })
  else none

namespace Replacement

open String

/--
When the second replacement starts after the first one's new text, making it first, at positions
moved back by the first one's change, gives the same text.
-/
theorem apply?_bind_apply?_of_start_add_lt_start {first second : Replacement}
    {text mid fin : String} (hlt : first.start + first.text < second.start)
    (hfirst : first.apply? text = some mid) (hsecond : second.apply? mid = some fin) :
    (({ second with
        start := (second.start.unoffsetBy (first.start + first.text)).offsetBy first.stop,
        stop := (second.stop.unoffsetBy (first.start + first.text)).offsetBy first.stop } :
        Replacement).apply? text).bind first.apply? = some fin := by
  obtain ⟨hfs, hfe, hfle, -⟩ := apply?_eq_some_iff.1 hfirst
  obtain ⟨hss, hse, hsle, -⟩ := apply?_eq_some_iff.1 hsecond
  have ha := isValid_of_apply?_eq_some_of_stop_le' hfirst hss (by grind)
  have hb := isValid_of_apply?_eq_some_of_stop_le' hfirst hse (by grind)
  simp only [le_iff, String.Pos.Raw.lt_iff, byteIdx_add_string] at hfle hsle hlt
  obtain ⟨mid2, hsecond'⟩ : ∃ mid2, ({ second with
      start := (second.start.unoffsetBy (first.start + first.text)).offsetBy first.stop,
      stop := (second.stop.unoffsetBy (first.start + first.text)).offsetBy first.stop } :
      Replacement).apply? text = some mid2 := ⟨_, apply?_eq_of_isValid ha hb
    (by simp only [le_iff, byteIdx_offsetBy, byteIdx_unoffsetBy, byteIdx_add_string]; grind)⟩
  have hfs' := isValid_of_apply?_eq_some_of_le_start hsecond' hfs
    (by simp only [le_iff, byteIdx_offsetBy, byteIdx_unoffsetBy, byteIdx_add_string]; grind)
  have hfe' := isValid_of_apply?_eq_some_of_le_start hsecond' hfe
    (by simp only [le_iff, byteIdx_offsetBy, byteIdx_unoffsetBy, byteIdx_add_string]; grind)
  obtain ⟨fin2, hfin2⟩ : ∃ fin2, first.apply? mid2 = some fin2 :=
    ⟨_, apply?_eq_of_isValid hfs' hfe' (le_iff.2 hfle)⟩
  rw [hsecond', Option.bind_some, hfin2, Option.some.injEq, ← toByteArray_inj,
    toByteArray_eq_of_apply?_eq_some hfin2, toByteArray_eq_of_apply?_eq_some hsecond',
    toByteArray_eq_of_apply?_eq_some hsecond, toByteArray_eq_of_apply?_eq_some hfirst]
  have hbsize := hb.le_utf8ByteSize
  simp only [byteIdx_offsetBy, byteIdx_unoffsetBy, byteIdx_add_string, ← size_toByteArray]
    at hbsize hlt ⊢
  exact (replaceBytes_replaceBytes_comm_of_eq hfle (by grind) (by grind) hbsize
    (by grind) (by grind)).symm

/--
When the second replacement ends before the first one starts, making it first and moving the first
one by its change gives the same text.
-/
theorem apply?_bind_apply?_of_stop_lt_start {first second : Replacement} {text mid fin : String}
    (hlt : second.stop < first.start) (hfirst : first.apply? text = some mid)
    (hsecond : second.apply? mid = some fin) :
    (second.apply? text).bind ({ first with
        start := (first.start.unoffsetBy second.stop).offsetBy (second.start + second.text),
        stop := (first.stop.unoffsetBy second.stop).offsetBy (second.start + second.text) } :
        Replacement).apply? = some fin := by
  obtain ⟨hfs, hfe, hfle, -⟩ := apply?_eq_some_iff.1 hfirst
  obtain ⟨hss, hse, hsle, -⟩ := apply?_eq_some_iff.1 hsecond
  simp only [le_iff, String.Pos.Raw.lt_iff] at hfle hsle hlt
  have hss' := isValid_of_apply?_eq_some_of_le_start' hfirst hss (by simp only [le_iff]; grind)
  have hse' := isValid_of_apply?_eq_some_of_le_start' hfirst hse (by simp only [le_iff]; grind)
  obtain ⟨mid2, hsecond'⟩ : ∃ mid2, second.apply? text = some mid2 :=
    ⟨_, apply?_eq_of_isValid hss' hse' (le_iff.2 hsle)⟩
  have ha := isValid_of_apply?_eq_some_of_stop_le hsecond' hfs (by simp only [le_iff]; grind)
  have hb := isValid_of_apply?_eq_some_of_stop_le hsecond' hfe (by simp only [le_iff]; grind)
  obtain ⟨fin2, hfin2⟩ : ∃ fin2, ({ first with
      start := (first.start.unoffsetBy second.stop).offsetBy (second.start + second.text),
      stop := (first.stop.unoffsetBy second.stop).offsetBy (second.start + second.text) } :
      Replacement).apply? mid2 = some fin2 := ⟨_, apply?_eq_of_isValid ha hb
    (by simp only [le_iff, byteIdx_offsetBy, byteIdx_unoffsetBy]; grind)⟩
  rw [hsecond', Option.bind_some, hfin2, Option.some.injEq, ← toByteArray_inj,
    toByteArray_eq_of_apply?_eq_some hfin2, toByteArray_eq_of_apply?_eq_some hsecond',
    toByteArray_eq_of_apply?_eq_some hsecond, toByteArray_eq_of_apply?_eq_some hfirst]
  have hfesize := hfe.le_utf8ByteSize
  simp only [byteIdx_offsetBy, byteIdx_unoffsetBy, byteIdx_add_string, ← size_toByteArray]
    at hfesize ⊢
  exact replaceBytes_replaceBytes_comm_of_eq hsle (by grind) hfle hfesize (by grind)
    (by grind)

end Replacement

/--
Exchanging two replacements with {name}`swap` keeps the text that they give: when {name}`first`
and then {name}`second` applied to {name}`text` give {name}`fin`, so do the exchanged replacements
in their new order.
-/
public theorem apply?_bind_apply?_of_swap_eq_some {first second second' first' : Replacement}
    {text mid fin : String} (hswap : swap first second = some (second', first'))
    (hfirst : first.apply? text = some mid) (hsecond : second.apply? mid = some fin) :
    (second'.apply? text).bind first'.apply? = some fin := by
  revert hswap
  fun_cases swap first second with
  | case1 inserted hlt =>
    rintro ⟨⟩
    exact Replacement.apply?_bind_apply?_of_start_add_lt_start hlt hfirst hsecond
  | case2 inserted hnlt hlt =>
    rintro ⟨⟩
    exact Replacement.apply?_bind_apply?_of_stop_lt_start hlt hfirst hsecond
  | case3 inserted hnlt hnlt' => rintro ⟨⟩

/-! # Reordering a Sequence -/

/--
Exchanges the replacement at index {name}`i` with the next one using {name}`swap`. The sequence is
unchanged when {name}`swap` refuses the exchange or when there is no next replacement.
-/
def swapAt : (i : Nat) → List Replacement → List Replacement
  | 0, x :: y :: rest =>
    match swap x y with
    | some (y', x') => y' :: x' :: rest
    | none => x :: y :: rest
  | 0, l => l
  | _ + 1, [] => []
  | i + 1, x :: rest => x :: swapAt i rest

/-- An exchange with {name}`swapAt` keeps the text that the replacements give. -/
theorem applyAll?_swapAt {i : Nat} {l : List Replacement} {text fin : String}
    (h : applyAll? text l = some fin) : applyAll? text (swapAt i l) = some fin := by
  fun_induction swapAt i l generalizing text with
  | case1 x y rest y' x' hswap =>
    simp only [applyAll?_cons, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨mid, hx, m2, hy, hrest⟩ := h
    obtain ⟨t1, ht1, hx'⟩ :=
      Option.bind_eq_some_iff.1 (apply?_bind_apply?_of_swap_eq_some hswap hx hy)
    exact ⟨t1, ht1, m2, hx', hrest⟩
  | case2 | case3 | case4 => exact h
  | case5 i x rest ih =>
    rw [applyAll?_cons, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨mid, hx, hrest⟩ := h
    exact ⟨mid, hx, ih hrest⟩

/--
Reorders a sequence of replacements by exchanges of consecutive replacements, so that it gives the
same text. Each element of {name}`swaps` is the index of a replacement to exchange with the next one
using {name}`swap`, and the exchanges are made in the order of {name}`swaps`. An exchange that
{name}`swap` refuses is skipped, so replacements that touch or overlap keep their relative order.
-/
public def permute (swaps : List Nat) (reps : Array Replacement) : Array Replacement :=
  (swaps.foldl (fun l i => swapAt i l) reps.toList).toArray

/--
Reordering replacements with {name}`permute` keeps the text that they give: when the replacements
applied to {name}`text` in their order give {name}`fin`, they give {name}`fin` in the new order too.
-/
public theorem applyAll?_permute {swaps : List Nat} {reps : Array Replacement} {text fin : String}
    (h : applyAll? text reps.toList = some fin) :
    applyAll? text (permute swaps reps).toList = some fin := by
  simp only [permute, List.toList_toArray]
  generalize reps.toList = l at h ⊢
  induction swaps generalizing l with
  | nil => exact h
  | cons i swaps ih => exact ih _ (applyAll?_swapAt h)
