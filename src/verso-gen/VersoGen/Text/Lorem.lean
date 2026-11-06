/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

set_option doc.verso true

/-!
The text that generated documents are made of. Generated text starts with the canonical lorem ipsum
passage and continues with words from a Latin word list. Neither contains markup characters.
-/

namespace VersoGen.Text

def canonicalPassage : String :=
  "Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt \
  ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation \
  ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in \
  reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur \
  sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id \
  est laborum."

/-- The words of {name}`canonicalPassage`, in order and with their punctuation. -/
public def canonicalWords : Array String :=
  (canonicalPassage.split ' ').fold (init := #[]) (·.push ·.copy)

/--
Latin words of the kind that lorem ipsum generators use after the standard passage, chosen for
variety and not copied from a particular source. Words that read as unfortunate English words are
left out.
-/
@[expose] public def latinWords : Array String := #[
  "a", "ac", "accumsan", "aenean", "aliquam", "aliquet", "ante", "arcu", "at", "auctor", "augue",
  "bibendum", "blandit", "condimentum", "congue", "consequat", "convallis", "cras", "dapibus",
  "diam", "dictum", "dignissim", "donec", "egestas", "eget", "eleifend", "elementum", "enim",
  "erat", "est", "etiam", "faucibus", "felis", "fermentum", "feugiat", "finibus", "fringilla",
  "fusce", "habitant", "hendrerit", "iaculis", "imperdiet", "integer", "interdum", "justo",
  "lacinia", "lacus", "laoreet", "lectus", "leo", "libero", "ligula", "lobortis", "luctus",
  "maecenas", "massa", "mattis", "mauris", "metus", "mi", "nam", "nec", "neque", "nibh", "nisl",
  "nunc", "orci", "ornare", "pellentesque", "pharetra", "phasellus", "placerat", "porta",
  "porttitor", "posuere", "praesent", "pretium", "proin", "pulvinar", "purus", "quam", "quisque",
  "rhoncus", "risus", "rutrum", "sagittis", "sapien", "scelerisque", "semper", "sodales",
  "sollicitudin", "suscipit", "suspendisse", "tellus", "tempus", "tincidunt", "tristique",
  "ullamcorper", "ultrices", "ultricies", "urna", "varius", "vehicula", "vel", "vestibulum",
  "vitae", "vivamus", "viverra", "volutpat"
]

/-- A word with its punctuation removed. -/
public def bareWord (w : String) : String :=
  w.foldl (init := "") fun out c => if c.isAlpha then out.push c else out

/--
The words with their punctuation removed, joined with spaces. Words that consist only of punctuation
are left out.
-/
public def bareWords (ws : Array String) : String :=
  ws.foldl (init := "") fun out w =>
    let w := bareWord w
    if w.isEmpty then out else if out.isEmpty then w else out ++ " " ++ w
