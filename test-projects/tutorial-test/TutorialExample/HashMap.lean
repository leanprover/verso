/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoTutorial

import TutorialExample.Data
import Std.Data.HashMap

open Verso.Genre
open Verso.Genre.Manual InlineLean

#doc (Tutorial) "Using `Std.HashMap`" =>
%%%
slug := "hashmap"
summary := inlines!"describes hash maps"
exampleStyle := .inlineLean `HashMap
%%%

This is a machine-generated tutorial used for testing the feature. Please don't attempt to learn from it. Think of it as more-realistic Lorem Ipsum.

{name}`Std.HashMap` provides an efficient hash table implementation for key-value storage with average O(1) lookup, insertion, and deletion. This guide covers practical usage of hash maps in Lean 4.

# Importing and Setup

```imports
import Std.Data.HashMap
```

```lean
-- HashMap is in the Std namespace
open Std (HashMap)
```

# Creating Hash Maps

## Empty Hash Maps

```lean
-- Create an empty hash map with type annotations
def emptyMap : HashMap String Nat :=
  HashMap.emptyWithCapacity

-- Type inference usually works
def scores :=
  HashMap.emptyWithCapacity (α := String) (β := Nat)

-- Using the empty literal
def config : HashMap String Bool := ∅
```

## From Lists

```lean
-- Build from a list of key-value pairs
def studentAges : HashMap String Nat :=
  HashMap.ofList [
    ("Alice", 20),
    ("Bob", 22),
    ("Charlie", 21)
  ]

-- From an array
def colorCodes : HashMap String String :=
  HashMap.ofList #[
    ("red", "#FF0000"),
    ("green", "#00FF00"),
    ("blue", "#0000FF")
  ].toList
```

## Builder Pattern

```lean
-- Chain insertions
def buildMap : HashMap String Nat :=
  HashMap.emptyWithCapacity 3
    |>.insert "x" 10
    |>.insert "y" 20
    |>.insert "z" 30
```

# Basic Operations

## Insertion

```lean
def map1 := emptyMap.insert "key" 42

-- Insert returns a new map (functional/immutable)
def map2 := map1.insert "another" 100

-- Inserting with an existing key replaces the value
def map3 := map2.insert "key" 99  -- "key" now maps to 99
```

## Lookup

```lean
def ages := HashMap.ofList [("Alice", 20), ("Bob", 22)]

-- get? returns Option
def aliceAge : Option Nat := ages["Alice"]?  -- some 20
def eveAge : Option Nat := ages["Eve"]?      -- none

-- getD with default value
def getAge (name : String) : Nat :=
  ages.getD name 0  -- returns 0 if not found

-- Using get? with pattern matching
def describeAge (name : String) : String :=
  match ages[name]? with
  | some age => s!"{name} is {age} years old"
  | none => s!"{name} not found"
```

## Checking Membership

```lean
def map' := HashMap.ofList [("x", 1), ("y", 2)]

def hasX : Bool := map'.contains "x"  -- true
def hasZ : Bool := map'.contains "z"  -- false

-- Check before inserting
def insertIfNew
    (map : HashMap String Nat) (key : String) (val : Nat) :
    HashMap String Nat :=
  if map.contains key then
    map
  else
    map.insert key val
```

## Deletion

```lean
def original :=
  HashMap.ofList [("a", 1), ("b", 2), ("c", 3)]

-- Erase a key
def afterErase :=
  original.erase "b"  -- only "a" and "c" remain

-- Erasing a non-existent key is a no-op
def stillSame :=
  original.erase "z"  -- same as original
```

## Size and Emptiness

```lean
def map'' := HashMap.ofList [("x", 1), ("y", 2)]

def count : Nat := map''.size  -- 2

def isEmpty1 : Bool := map''.isEmpty      -- false
def isEmpty2 : Bool :=
  ({} : HashMap String Nat).isEmpty  -- true
```

# Iteration and Transformation

## Folding

```lean
def sumValues (map : HashMap String Nat) : Nat :=
  map.fold (init := 0) fun acc _key val => acc + val

def example' :=
  HashMap.ofList [("a", 10), ("b", 20), ("c", 30)]
#eval sumValues example'  -- 60

-- Collecting keys
def getKeys (map : HashMap String Nat) : List String :=
  map.fold (init := []) fun acc key _val => key :: acc

-- Building a list of pairs
def toPairs (map : HashMap String Nat) :
    List (String × Nat) :=
  map.fold (init := []) fun acc key val => (key, val) :: acc
```

## Mapping Values

```lean
namespace Mapping
-- Transform all values
def doubleValues (map : HashMap String Nat) :
    HashMap String Nat :=
  map.fold (init := {}) fun acc key val =>
    acc.insert key (val * 2)

def original := HashMap.ofList [("x", 5), ("y", 10)]
def doubled := doubleValues original  -- x → 10, y → 20
end Mapping
```

# Working with Custom Types

## Deriving Hashable and BEq

For custom types, derive `Hashable` and `BEq`:

```lean
structure Point where
  x : Int
  y : Int
deriving Hashable, BEq

def locations : HashMap Point String :=
  HashMap.ofList [
    (⟨0, 0⟩, "origin"),
    (⟨1, 0⟩, "east"),
    (⟨0, 1⟩, "north")
  ]

def getLocation (p : Point) : Option String :=
  locations[p]?
```

## Manual Instances

For more control, implement instances manually:

```lean
inductive Color' where
  | red
  | green
  | blue

-- BEq instance
instance : BEq Color' where
  beq c1 c2 := match c1, c2 with
    | .red, .red => true
    | .green, .green => true
    | .blue, .blue => true
    | _, _ => false

-- Hashable instance
instance : Hashable Color' where
  hash c := match c with
    | .red => 0
    | .green => 1
    | .blue => 2

def colorNames : HashMap Color' String :=
  HashMap.ofList [
    (.red, "Red"),
    (.green, "Green"),
    (.blue, "Blue")
  ]
```

## Compound Keys

```lean
structure Coordinate where
  row : Nat
  col : Nat
  deriving Hashable, BEq

def grid : HashMap Coordinate String :=
  HashMap.ofList [
    (⟨0, 0⟩, "top-left"),
    (⟨0, 1⟩, "top-right"),
    (⟨1, 0⟩, "bottom-left")
  ]
```

# Practical Examples

## Word Frequency Counter

```lean
def countWords (text : List String) : HashMap String Nat :=
  text.foldl (init := {}) fun map word =>
    let count := map.getD word 0
    map.insert word (count + 1)

def text := [
  "the", "quick", "brown", "fox",
  "the", "lazy", "dog", "the"
]
def frequencies := countWords text
-- "the" → 3, "quick" → 1, etc.
```

## Caching/Memoization

```lean
structure Cache where
  store : HashMap Nat Nat
  deriving Inhabited

def fibonacci (n : Nat) (cache : Cache) : Nat × Cache :=
  match cache.store[n]?with
  | some result => (result, cache)
  | none =>
    if n ≤ 1 then
      let newCache := { store := cache.store.insert n n }
      (n, newCache)
    else
      let (fib1, cache1) := fibonacci (n - 1) cache
      let (fib2, cache2) := fibonacci (n - 2) cache1
      let result := fib1 + fib2
      let newCache := {
        store := cache2.store.insert n result
      }
      (result, newCache)

def computeFib (n : Nat) : Nat :=
  let (result, _) := fibonacci n { store := {} }
  result
```

## Grouping Data

```lean
def groupBy (f : α → β) (xs : List α) [Hashable β] [BEq β] :
    HashMap β (List α) :=
  xs.foldl (init := {}) fun map x =>
    let key := f x
    let group := map.getD key []
    map.insert key (x :: group)

-- Group numbers by their remainder mod 3
def numbers := [1, 2, 3, 4, 5, 6, 7, 8, 9]
def grouped := groupBy (· % 3) numbers
-- 0 → [9, 6, 3], 1 → [7, 4, 1], 2 → [8, 5, 2]
```

## Building an Index

```lean
structure Document where
  id : Nat
  content : List String
  deriving Repr

def buildIndex (docs : List Document) :
    HashMap String (List Nat) :=
  docs.foldl (init := {}) fun index doc =>
    doc.content.foldl (init := index) fun idx word =>
      let docIds := idx.getD word []
      idx.insert word (doc.id :: docIds)

def documents : List Document := [
  { id := 1, content := ["hello", "world"] },
  { id := 2, content := ["hello", "lean"] },
  { id := 3, content := ["world", "lean"] }
]

def index := buildIndex documents
-- "hello" → [2, 1], "world" → [3, 1], "lean" → [3, 2]
```

## Deduplication

```lean
section
variable [Hashable α] [BEq α]

def deduplicate (xs : List α)  : List α :=
  let (result, _) := xs.foldl (init := ([], {}))
    fun (acc, (seen : HashMap α Unit)) x =>
      if seen.contains x then
        (acc, seen)
      else
        (x :: acc, seen.insert x ())
  result.reverse

def withDuplicates := [1, 2, 3, 2, 4, 1, 5]
def unique := deduplicate withDuplicates  -- [1, 2, 3, 4, 5]
end
```
