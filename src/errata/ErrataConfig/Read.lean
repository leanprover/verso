/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
The reading and validation of `errata.toml`: every key and value is checked, each problem is
reported at its position in the file, and the profiles' inheritance is applied.
-/
module

public import ErrataConfig.Basic
public import ErrataConfig.Duration
public import ErrataConfig.StringOffsets

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace ErrataConfig

/-- A duration-valued key's value in milliseconds. With {name}`positive`, zero is a problem. -/
def readDuration (key : String) (v : Lake.Toml.Value) (positive := false) :
    CheckM (Option Nat) := do
  match v with
  | .string ref s =>
    match durationMs? s with
    | some ms =>
      if positive && ms == 0 then
        problem ref s!"'{key}' must be longer than zero"
        return none
      return some ms
    | none =>
      problem ref s!"'{key}' must be a duration of {durationForm}, and it is {s.quote}"
      return none
  | other =>
    problem other.ref s!"'{key}' must be a duration string, and it is {kindOf other}"
    return none

/-- A string-valued key's value. -/
def readString (key : String) (v : Lake.Toml.Value) : CheckM (Option String) := do
  match v with
  | .string _ s => return some s
  | other =>
    problem other.ref s!"'{key}' must be a string, and it is {kindOf other}"
    return none

/-- A path-valued key's value: a string that is not empty. -/
def readPath (key : String) (v : Lake.Toml.Value) : CheckM (Option String) := do
  match v with
  | .string ref s =>
    if s.isEmpty then
      problem ref s!"'{key}' must be a path, and it is the empty string"
      return none
    return some s
  | other =>
    problem other.ref s!"'{key}' must be a path string, and it is {kindOf other}"
    return none

/-- A boolean-valued key's value. -/
def readBool (key : String) (v : Lake.Toml.Value) : CheckM (Option Bool) := do
  match v with
  | .boolean _ b => return some b
  | other =>
    problem other.ref s!"'{key}' must be a boolean, and it is {kindOf other}"
    return none

/--
A filter string, with the position of its opening delimiter and, when its token decodes to the text
that the TOML reader read, the position of each of its characters.
-/
def readFilter (key : String) (v : Lake.Toml.Value) : CheckM (Option FilterString) := do
  match v with
  | .string ref text =>
    let fileMap ← read
    let some start := ref.getPos? | return some { text, line := 0, col := 0 }
    let p := fileMap.toPosition start
    let positions? := do
      let stop ← ref.getTailPos?
      let token := ({ str := fileMap.source, startPos := start, stopPos := stop } : Substring.Raw)
      let (decoded, offsets) ← stringOffsets? token.toString
      guard (decoded == text)
      return offsets.map fun o =>
        let q := fileMap.toPosition ⟨start.byteIdx + o⟩
        (q.line, q.column)
    return some { text, line := p.line, col := p.column, positions? }
  | other =>
    problem other.ref s!"'{key}' must be a string, and it is {kindOf other}"
    return none

/--
The leaves of a settings table below the name {name}`namePrefix`, each with its dotted name: every
value other than a table, every table with the key {lit}`needs`, and every empty table. The other
tables hold more of a name, and their leaves are named below it.
-/
partial def settingLeaves (namePrefix : String) (t : Lake.Toml.Table) :
    Array (String × Lake.Toml.Value) :=
  t.items.foldl (init := #[]) fun out (k, v) =>
    let name := if namePrefix.isEmpty then keyName k else s!"{namePrefix}.{keyName k}"
    match v with
    | .table _ inner =>
      if inner.items.isEmpty || (inner.find? `needs).isSome then out.push (name, v)
      else out ++ settingLeaves name inner
    | _ => out.push (name, v)

/--
The settings table. Settings' names are their fully qualified declaration names, written as quoted
dotted keys ({lit}`"A.B.c" = …`), bare dotted keys, or keys in nested tables
({lit}`[….settings.A.B]` with {lit}`c = …`); {name}`settingLeaves` flattens nested tables into
dotted names. Each value is a string or {lit}`{ needs = "target" }`, with no coercion, and each name
is given once.
-/
def readSettings (v : Lake.Toml.Value) : CheckM (Array (String × SettingValue)) := do
  let .table _ t := v
    | problem v.ref s!"'settings' must be a table, and it is {kindOf v}"
      return #[]
  let shape := "a string or { needs = \"target\" }"
  let mut out := #[]
  for (name, sv) in settingLeaves "" t do
    match sv with
    | .string ref s =>
      if out.any (·.1 == name) then problem ref s!"the setting '{name}' is given twice"
      else out := out.push (name, .value s)
    | .table ref inner =>
      match inner.find? `needs with
      | some (.string r tgt) =>
        if inner.items.size != 1 then
          problem ref s!"the setting '{name}' must be {shape}, and its table has keys \
            besides 'needs'"
        else if out.any (·.1 == name) then problem ref s!"the setting '{name}' is given twice"
        else
          let (line, col) ← positionOf r
          out := out.push (name, .needs tgt line col)
      | some other =>
        problem other.ref s!"'needs' must name a Lake target as a string, and it is \
          {kindOf other}"
      | none =>
        problem ref s!"the setting '{name}' must be {shape}, and it is an empty table"
    | other =>
      problem other.ref s!"the setting '{name}' must be {shape}, and it is {kindOf other}"
  return out

/-- The keys of an override. -/
def overrideKeys : List String :=
  ["filter", "timeout", "fixture-timeout", "grace-period", "slow-after", "update-golden",
    "settings"]

/-- An override of the profile {name}`profile`. -/
def readOverride (profile : String) (v : Lake.Toml.Value) : CheckM (Option Override) := do
  let .table ref t := v
    | problem v.ref s!"each override of the profile '{profile}' must be a table, and it is \
        {kindOf v}"
      return none
  checkKeys s!"an override of the profile '{profile}'" overrideKeys t
  let some filterValue := t.find? `filter
    | problem ref s!"an override of the profile '{profile}' needs a 'filter'"
      return none
  let some filter ← readFilter "filter" filterValue | return none
  let mut o : Override := { filter }
  if let some x := t.find? `timeout then
    o := { o with timeoutMs? := ← readDuration "timeout" x true }
  if let some x := t.find? `«fixture-timeout» then
    o := { o with fixtureTimeoutMs? := ← readDuration "fixture-timeout" x true }
  if let some x := t.find? `«grace-period» then
    o := { o with gracePeriodMs? := ← readDuration "grace-period" x }
  if let some x := t.find? `«slow-after» then
    o := { o with slowAfterMs? := ← readDuration "slow-after" x }
  if let some x := t.find? `«update-golden» then
    o := { o with updateGolden? := ← readBool "update-golden" x }
  if let some x := t.find? `settings then o := { o with settings := ← readSettings x }
  return some o

/-- The keys of a profile. -/
def profileKeys : List String :=
  ["inherits", "timeout", "fixture-timeout", "grace-period", "slow-after", "jobs", "update-golden",
    "settings", "override", "default-filter", "junit", "json", "markdown"]

/-- The profile named {name}`name`, as the file gives it. -/
def readProfile (name : String) (v : Lake.Toml.Value) : CheckM (Option Profile) := do
  let .table ref t := v
    | problem v.ref s!"the profile '{name}' must be a table, and it is {kindOf v}"
      return none
  checkKeys s!"the profile '{name}'" profileKeys t
  let mut p : Profile := { name, ref }
  if let some x := t.find? `inherits then
    if let some parent ← readString "inherits" x then
      p := { p with inherits? := some (parent, x.ref) }
  if let some x := t.find? `timeout then
    p := { p with timeoutMs? := ← readDuration "timeout" x true }
  if let some x := t.find? `«fixture-timeout» then
    p := { p with fixtureTimeoutMs? := ← readDuration "fixture-timeout" x true }
  if let some x := t.find? `«grace-period» then
    p := { p with gracePeriodMs? := ← readDuration "grace-period" x }
  if let some x := t.find? `«slow-after» then
    p := { p with slowAfterMs? := ← readDuration "slow-after" x }
  if let some x := t.find? `jobs then
    match x with
    | .integer _ n =>
      if n > 0 then p := { p with jobs? := some n.toNat }
      else problem x.ref s!"'jobs' must be a positive integer, and it is {n}"
    | other => problem other.ref s!"'jobs' must be a positive integer, and it is {kindOf other}"
  if let some x := t.find? `«update-golden» then
    p := { p with updateGolden? := ← readBool "update-golden" x }
  if let some x := t.find? `settings then p := { p with settings := ← readSettings x }
  if let some x := t.find? `override then
    match x with
    | .array _ items =>
      let mut overrides := #[]
      for item in items do
        if let some o ← readOverride name item then overrides := overrides.push o
      p := { p with overrides }
    | other =>
      problem other.ref s!"'override' must be an array of tables, written \
        [[profile.{name}.override]], and it is {kindOf other}"
  if let some x := t.find? `«default-filter» then
    p := { p with defaultFilter? := ← readFilter "default-filter" x }
  if let some x := t.find? `junit then p := { p with junit? := ← readPath "junit" x }
  if let some x := t.find? `json then p := { p with json? := ← readPath "json" x }
  if let some x := t.find? `markdown then p := { p with markdown? := ← readPath "markdown" x }
  return some p

/-- A test executable that {lit}`[[executable]]` adds. -/
def readExecutable (v : Lake.Toml.Value) : CheckM (Option Executable) := do
  let .table ref t := v
    | problem v.ref s!"each [[executable]] must be a table, and it is {kindOf v}"
      return none
  checkKeys "an [[executable]]" ["name", "command", "cwd"] t
  let name? ← match t.find? `name with
    | some x => readString "name" x
    | none =>
      problem ref "an [[executable]] needs a 'name'"
      pure none
  let command? ← match t.find? `command with
    | some (.array r items) =>
      let mut words := #[]
      let mut ok := true
      for item in items do
        match item with
        | .string _ s => words := words.push s
        | other =>
          problem other.ref s!"each word of 'command' must be a string, and this one is \
            {kindOf other}"
          ok := false
      if words.isEmpty && ok then
        problem r "'command' must have at least one word"
        pure none
      else pure (if ok then some words else none)
    | some other =>
      problem other.ref s!"'command' must be an array of strings, and it is {kindOf other}"
      pure none
    | none =>
      problem ref "an [[executable]] needs a 'command'"
      pure none
  let cwd? ← match t.find? `cwd with
    | some x => readString "cwd" x
    | none => pure none
  let some name := name? | return none
  let some command := command? | return none
  let (line, col) ← positionOf ref
  return some { name, ref, line, col, command, cwd? }

/--
Applies inheritance: each profile gets its ancestors' values, the nearer ancestor winning per key,
settings merged per setting, and overrides concatenated with the ancestors' first. The profile
{lit}`default` is the root, which every other profile inherits from unless it names another. The
result always has {lit}`default`.
-/
def inherit (profiles : Array Profile) : CheckM (Array Profile) := do
  let profiles :=
    if profiles.any (·.name == "default") then profiles else #[{ name := "default" }] ++ profiles
  let find (name : String) := profiles.find? (·.name == name)
  let mut out := #[]
  for p in profiles do
    if p.name == "default" then
      if let some (_, r) := p.inherits? then
        problem r "the profile 'default' is the root, and it inherits from no other profile"
    -- The chain from the profile up to the root, nearest first.
    let mut chain := #[p]
    let mut cur := p
    let mut broken := false
    repeat
      if cur.name == "default" then break
      let parentName := (cur.inherits?.map (·.1)).getD "default"
      let some parent := find parentName
        | if let some (_, r) := cur.inherits? then
            if cur.name == p.name then
              problem r s!"the profile '{cur.name}' inherits from '{parentName}', which is not a \
                profile"
          broken := true
          break
      if chain.any (·.name == parent.name) then
        -- Each profile on the cycle reports it; a profile that only leads into it is left out.
        if parent.name == p.name then
          if let some (_, r) := p.inherits? then
            let names := (chain.map (·.name)).toList ++ [parent.name]
            problem r s!"the profiles inherit in a cycle: {" → ".intercalate names}"
        broken := true
        break
      chain := chain.push parent
      cur := parent
    if broken then continue
    -- The root first, so each nearer profile's values replace the farther ones'.
    let merged := chain.reverse.foldl (init := ({ name := p.name, ref := p.ref } : Profile))
      fun acc q => {
        acc with
        timeoutMs? := q.timeoutMs? <|> acc.timeoutMs?
        fixtureTimeoutMs? := q.fixtureTimeoutMs? <|> acc.fixtureTimeoutMs?
        gracePeriodMs? := q.gracePeriodMs? <|> acc.gracePeriodMs?
        slowAfterMs? := q.slowAfterMs? <|> acc.slowAfterMs?
        jobs? := q.jobs? <|> acc.jobs?
        updateGolden? := q.updateGolden? <|> acc.updateGolden?
        settings := q.settings.foldl (init := acc.settings) fun s (k, v) =>
          (s.filter (·.1 != k)).push (k, v)
        overrides := acc.overrides ++ q.overrides
        defaultFilter? := q.defaultFilter? <|> acc.defaultFilter?
        junit? := q.junit? <|> acc.junit?
        json? := q.json? <|> acc.json?
        markdown? := q.markdown? <|> acc.markdown?
      }
    out := out.push merged
  return out

/-- Validates the whole of the configuration file's table. -/
def readFile (t : Lake.Toml.Table) : CheckM File := do
  checkKeys "errata.toml" ["default-filter", "executable", "profile"] t
  let mut file : File := {}
  if let some x := t.find? `«default-filter» then
    file := { file with defaultFilter? := ← readFilter "default-filter" x }
  if let some x := t.find? `executable then
    match x with
    | .array _ items =>
      let mut exes : Array Executable := #[]
      for item in items do
        if let some e ← readExecutable item then
          if exes.any (·.name == e.name) then
            problem e.ref s!"the [[executable]] name '{e.name}' is used more than once"
          else exes := exes.push e
      file := { file with executables := exes }
    | other =>
      problem other.ref s!"'executable' must be an array of tables, written [[executable]], and \
        it is {kindOf other}"
  if let some x := t.find? `profile then
    match x with
    | .table _ profiles =>
      let mut ps := #[]
      for (k, v) in profiles.items do
        if let some p ← readProfile (keyName k) v then ps := ps.push p
      file := { file with profiles := ← inherit ps }
    | other =>
      problem other.ref s!"'profile' must be a table of profiles, written [profile.NAME], and it \
        is {kindOf other}"
  if file.profiles.isEmpty then file := { file with profiles := #[{ name := "default" }] }
  return file

/-- A problem as {lit}`errata.toml:LINE:COL: message`. -/
def Problem.render (fileMap : Lean.FileMap) (p : Problem) : String :=
  match p.ref.getPos? with
  | some pos =>
    let q := fileMap.toPosition pos
    s!"errata.toml:{q.line}:{q.column}: {p.msg}"
  | none => s!"errata.toml: {p.msg}"

/--
Reads and validates the text of a configuration file. The result is what the file says, or every
problem found, each at its position and in the order of the file.
-/
def parse (text : String) : IO (Except (Array String) File) := do
  -- TOML's grammar has no byte-order mark, and some editors write one.
  let text := (text.dropPrefix? "﻿").map (·.copy) |>.getD text
  let ictx := Lean.Parser.mkInputContext text "errata.toml"
  let table ← match ← (Lake.Toml.loadToml ictx).toBaseIO with
    | .ok t => pure t
    | .error log => return .error (← log.toList.toArray.mapM fun m => m.toString)
  let (file, problems) := ((readFile table).run ictx.fileMap).run #[]
  if problems.isEmpty then return .ok file
  -- Problems at the same position stay in the order they were found.
  let position (p : Problem) := (p.ref.getPos?.map (·.byteIdx)).getD 0
  let sorted := problems.zipIdx.qsort fun (a, i) (b, j) =>
    position a < position b || (position a == position b && i < j)
  return .error (sorted.map (·.1.render ictx.fileMap))

end ErrataConfig
