# Docstring elaborator fixes needed in Lean

Issues found while reviewing Verso PR #859 (literate-mode handlers for Verso docstring
extensions). Each needs a change in the `lean4` repository. File and line references are
for `v4.30.0-rc2`.

## 1. `{option}` role renders `set_option [anonymous]`

**File:** `src/Lean/Elab/DocString/Builtin.lean`, `option` role, around line 1160.

When the role is given full `set_option` syntax, as in
`` {option}`set_option maxHeartbeats 1000` ``, the stored display code reads
`set_option [anonymous]` instead of `set_option maxHeartbeats 1000`.

The role parses the code with the `set_option` command parser:

```
"set_option " >> identWithPartialTrailingDot >> ppSpace >> optionValue
```

The helper `optionNameAndVal` (line 452) reads the option name from `stx[1]` and the
value from `stx[3]`, and these indices work: the role resolves the option correctly.
But the display code a few lines below uses different, wrong indices:

```lean
let code := #[
  ("set_option", some .keyword), (" ", none),
  (toString stx[1][0].getId, some <| .option optionName decl.declName), (" ", none),
  (toString stx[2].getAtomVal, some <| .literal stx[2].getKind none)
]
```

`stx[1]` is the ident itself, so `stx[1][0]` is `Syntax.missing` and `getId` returns
`[anonymous]`. `stx[2]` is not the value, so `getAtomVal` returns the empty string.

**Fix:** build the name from `optionName` (or `stx[1]`) and the value from `stx[3]`.
Note that `stx[3]` can be a string or numeric literal node, where the atom is nested,
or a bare `true`/`false` atom, so `stx[3].getAtomVal` alone is not enough for the
literal cases. Reusing the `val : DataValue` returned by `optionNameAndVal` for the
display string is probably simplest. Test with a numeric, a string, and a Boolean
option value.

**Why it cannot be fixed downstream:** the broken strings are baked into the
`Data.SetOption` payload when the docstring is elaborated. Consumers such as Verso
receive only the corrupted `DocCode`.

## 2. `{assert}` and `{assert'}` produce no hover or highlighting information

**File:** `src/Lean/Elab/DocString/Builtin.lean`, `assert'` at line 1215, `assert` at
line 1233.

Both roles elaborate their terms but return a bare `.code s.getString`. Compare with
`leanRole` (line 1080), which wraps elaboration in `withSaveInfoContext`, collects the
info trees, and returns a `Data.LeanTerm` payload built with `highlightSyntax`. As a
result, `` {assert}`Nat.zero = Nat.zero` `` renders as plain code with no hovers for
`Nat.zero`, observed in the Verso PR #859 review.

**Fix:** capture info the same way `leanRole` does and return a `Data.LeanTerm`
payload (or a dedicated `Data.Assert`) when info trees are available. For `assert`,
the parsed term can be passed to `highlightSyntax` directly. For `assert'`, the parsed
null node with `lhs`, `=`, `rhs` works as well.

## 3. `{assert'}` is not usable once `=` notation exists

`assert'` exists for the prelude, before the equality type's notation is introduced,
and parses `a = b` itself. After the notation is defined, the role's hand-rolled
parse of `=` cannot be used in practice, so the role cannot be demonstrated or tested
outside the bootstrap. Verso's test fixture now documents it as untested
(`test-projects/literate-config/LitConfig/Builtins.lean`).

**Fix (agreed direction from the PR #859 discussion):** replace it with a role that
takes the two (or three, with the type) sides as separate code parameters, for
example `` {assert'}[`Nat.zero` `Nat.zero`] ``, so no equality notation is needed.

## 4. `Data.Atom` is not `public`

**File:** `src/Lean/Elab/DocString/Builtin/Keywords.lean`, line 26.

The file uses the module system and `structure Data.Atom` lacks `public`, so its name
is mangled with a private prefix. The `kw` and `kw?` roles put it in `Inline.other`
payloads, so external consumers must dispatch on the mangled name. Verso works around
this by matching the name's suffix (`handleKwAtom` in
`src/verso-literate/VersoLiterate/Basic.lean`, which carries a comment about this).

**Fix:** mark the structure `public`. The workaround in Verso can then be removed.

## 5. `{conv}` stores a `Data.Tactic` value in its `Data.ConvTactic` payload

**File:** `src/Lean/Elab/DocString/Builtin.lean`, `conv` role, around line 1388.

The role builds its payload as:

```lean
return .other {
    name := ``Data.ConvTactic, val := .mk { name := t : Data.Tactic}
  } #[.code s.getString]
```

The extension name says `Data.ConvTactic`, but the `Dynamic` value is a `Data.Tactic`, so
`val.get? Data.ConvTactic` fails for consumers that dispatch on the advertised type. The
two structures have the same shape, which hides the mistake. Verso works around it by
accepting both payload types in `handleConvTactic`
(`src/verso-literate/VersoLiterate/Basic.lean`); the workaround can be removed once this
is fixed.

**Fix:** construct a `Data.ConvTactic` value (`val := .mk { name := t : Data.ConvTactic }`).

## 6. `{conv}` does not resolve tactics by token, unlike `{tactic}`

**File:** `src/Lean/Elab/DocString/Builtin.lean`, `conv` role and `getConvTactic`,
around line 1351.

`{tactic}` resolves its argument against `Tactic.Doc.allTacticDocs`, matching both
internal kind names and user-facing names, so `` {tactic}`rfl` `` works. `getConvTactic`
only matches when the argument is a name suffix of a conv tactic's syntax kind, so
`` {conv}`rfl` `` does not resolve (the kind is `convRfl`). The role then silently falls
back to parsing the string as conv syntax and returns plain `.code`, with no payload and
no metadata for downstream tools. `` {conv}`lhs` `` works only because the kind happens
to be named `Lean.Parser.Tactic.Conv.lhs`.

**Fix:** resolve conv tactics by first token as well, the way `tactic` does, or at least
document the suffix requirement in the role's docstring.

## 7. Enhancement: diagnostics in `DocCode`

`DocCode` segments carry only token highlighting (`DocHighlight`). Messages produced
by commands in a docstring's `lean` code block are instead re-logged as silent info
messages positioned inside the doc comment
(`src/Lean/Elab/DocString/Builtin.lean`, `lean` code block, around line 945). A
consumer that renders the docstring has no direct way to know which part of the code
block a message belongs to.

Verso now reverse-engineers the placement: the concatenated `DocCode` text reproduces
a region of the source file verbatim, so each doc-comment message is matched to the
occurrence of that text containing the message's range
(`relocateDocMessages` in `src/verso-literate/VersoLiterateMain.lean`). This works,
but a first-class representation of message spans in `DocCode` (or in
`Data.LeanBlock`) would let all consumers place diagnostics without this
reconstruction, and would also cover messages whose positions fall outside any code
block.
