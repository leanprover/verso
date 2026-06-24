/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen

Round-trip property tests for Verso's serialization. The generators and the `roundTripOk`/`isEqOk`
helpers live in `VersoTests.SerializationGenerators`; they construct Verso types whose constructors are private, so
they stay module-internal there and are reached here through `import all`.
-/
module

import Errata
import all VersoTests.SerializationGenerators

open Lean
open Verso Multi
open Errata

/-- Internal identifiers round-trip through JSON. -/
@[test]
def internalId : Test := property (∀ id : InternalId, roundTripOk id)

/-- Objects round-trip through JSON. -/
@[test]
def object : Test := property (∀ obj : Object, roundTripOk obj)

/-- Domains round-trip through JSON. -/
@[test]
def domain : Test := property (∀ dom : Domain, roundTripOk dom)

/-- Reference domains round-trip through JSON. -/
@[test]
def refDomain : Test := property (∀ dom : RefDomain, roundTripOk dom)

/-- Reference objects round-trip through JSON. -/
@[test]
def refObject : Test := property (∀ obj : RefObject, roundTripOk obj)

/-- Remote information round-trips through JSON. -/
@[test]
def remoteInfo : Test := property (∀ info : RemoteInfo, roundTripOk info)

/-- The collection of remotes round-trips through JSON. -/
@[test]
def allRemotes : Test := property (∀ remotes : AllRemotes, roundTripOk remotes)

/-- Manual traverse state round-trips through JSON. -/
@[test]
def traverseState : Test :=
  property (∀ st : Verso.Genre.Manual.TraverseState, roundTripOk st)

/-- HTML round-trips through JSON. -/
@[test]
def html : Test := property (∀ html : Verso.Output.Html, roundTripOk html)

/-- Manual data files round-trip through JSON. -/
@[test]
def dataFile : Test := property (∀ f : Verso.Genre.Manual.DataFile, roundTripOk f)

/-- Manual numbering round-trips through JSON. -/
@[test]
def numbering : Test := property (∀ n : Verso.Genre.Manual.Numbering, roundTripOk n)

/-- Cross-reference sources round-trip through JSON. -/
@[test]
def xrefSource : Test :=
  property (∀ src : XrefSource, isEqOk (XrefSource.fromJson? src.toJson) src)

/-- Remotes round-trip through JSON. -/
@[test]
def remote : Test :=
  property (∀ r : Remote, isEqOk (Remote.fromJson? "" r.toJson) r)

/-- Search domain mappers and search priorities round-trip through JSON. -/
@[test]
def searchPriorities : Test :=
  property <| ∀ (semantic fullText : Fin 100) (domains : Verso.NameMap (Fin 100)),
    let mapper : Search.DomainMapper :=
      { displayName := "d", className := "c", dataToSearchables := "x => []" }
    let priorities : Search.SearchPriorities := { semantic, fullText, domains }
    roundTripOk mapper ∧ roundTripOk priorities

/--
Every entry `Verso.Search.priorityMapJson` produces is a non-neutral integer tied to an input
doc's {name}`IndexDoc.id` and {name}`IndexDoc.priority`, and every input doc with a non-neutral
priority has its id present. Documents with no priority or the neutral value `50` are omitted.
-/
@[test]
def priorityMapJson : Test :=
  property <| ∀ docs : Array Search.IndexDoc,
    let j : Json := Search.priorityMapJson docs
    let entries : Array (String × Json) :=
      match Json.getObj? j with
      | .error _ => #[]
      | .ok obj => obj.toArray
    let forward := entries.all fun (k, v) =>
      match Json.getInt? v with
      | .error _ => false
      | .ok p => p != 50 && docs.any fun d => d.id == k && d.priority == some p
    let backward := docs.all fun d =>
      let isNeutral := d.priority.isNone || d.priority == some 50
      isNeutral || (Json.getObjVal? j d.id).toOption.isSome
    forward ∧ backward
