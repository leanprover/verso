/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Environment
import Lean.Meta
import Verso.Syntax
import VersoManual.Basic


namespace Verso.Genre.Manual

open Lean
open Verso.Output.Html
open Verso.Doc.Elab

/--
A progress tracker that shows how many symbols are documented.

The parameter `present` tracks which names' docs are present in the manual, sorted by namespace. The
set of names in each namespace is encoded as a string with space separation to prevent running out
of heartbeats while quoting larger data structures.
-/
def Block.progress
    (namespaces exceptions : Array Name)
    (present : List (Name × String))
    (tactics : Array Name) :
    Block where
  name := `Verso.Genre.Manual.Block.progress
  data := toJson (namespaces, exceptions, present, tactics)

private def ignore [Monad m] [MonadLiftT CoreM m] [MonadEnv m] (x : Name) : m Bool := do
  if (← Meta.Simp.isSimproc x) then return true
  let env ← getEnv
  return isPrivateName x ||
    isAuxRecursor env x ||
    isNoConfusion env x ||
    isRecCore env x ||
    env.isProjectionFn x ||
    Lean.Linter.isDeprecated env x ||
    x.hasNum ||
    x.isInternalOrNum ||
    (`noConfusionType).isSuffixOf x ||
    let str := x.getString!
    str ∈ ["sizeOf_spec", "sizeOf_eq", "brecOn", "ind", "ofNat_toCtorIdx", "inj", "injEq", "induct"] ||
    "proof_".isPrefixOf str && (str.drop 6).all (·.isDigit) ||
    "match_".isPrefixOf str && (str.drop 6).all (·.isDigit) ||
    "eq_".isPrefixOf str && (str.drop 3).all (·.isDigit)

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let mut names := #[]
  for (x, _) in (← getEnv).constants do
    if x matches .str .anonymous _ && !(← liftTermElabM <| ignore x) then
      names := names.push x
  names := names.qsort (·.toString < ·.toString)
  elabCommand <| ← `(private def $(mkIdent `allRootNames) : Array Name := #[$(names.map (quote · : Name → Term)),*])

@[directive_expander progress]
def progress : DirectiveExpander
  | args, blocks => do
    if h : args.size > 0 then
      throwErrorAt args[0].syntax  "Expected 0 arguments"
    let mut namespaces : NameSet := {}
    let mut exceptions : NameSet := {}
    for block in blocks do
      match block with
      | `(block|```$nameStx:ident $argsStx* | $contents```) =>
        let contents := contents.getString
        match nameStx.getId with
        | `namespace =>
          for str in contents.split Char.isWhitespace do
            if !str.isEmpty then
              namespaces := namespaces.insert str.toName
        | `exceptions =>
          for str in contents.split Char.isWhitespace do
            if !str.isEmpty then
              exceptions := exceptions.insert str.toName
        | _ => throwErrorAt nameStx "Expected 'namespace' or 'exceptions'"
      | _ => throwErrorAt block "Expected code block named 'namespace' or 'exceptions'"
    let mut present : NameMap NameSet := {}
    let mut rootPresent : NameSet := {}

    for ns in namespaces do
      present := present.insert ns {}
    for (x, info) in (← getEnv).constants do
      if (← ignore x) then continue
      if exceptions.contains x then continue
      match info with
      | .thmInfo _ => continue -- don't document theorems
      | .ctorInfo _ => continue -- constructors are documented as children of their types
      | _ => pure ()
      if ← Meta.isInstance x then continue
      if let .str .anonymous s := x then
        if let some v := present.find? `_root_ then
          present := present.insert `_root_ (v.insert x)
        else
          present := present.insert `_root_ (NameSet.empty.insert x)
      else
        let mut ns := x
        while !ns.isAnonymous && !(ns.getString!.get 0 |>.isUpper) do
          ns := ns.getPrefix
        if let some v := present.find? ns then
          present := present.insert ns (v.insert x)

    let present' := present.toList.map (fun x => (x.1, String.intercalate " " (x.2.toList.map Name.toString)))
    let allTactics : Array Name := (← Elab.Tactic.Doc.allTacticDocs).map (fun t => t.internalName)

    pure #[← ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.progress $(quote namespaces.toArray) $(quote exceptions.toArray) $(quote present') $(quote allTactics)) #[])]

@[block_extension Block.progress]
def progress.descr : BlockDescr where
  traverse _ _ _ := pure none
  toHtml := some fun _ _ _ info _blocks => open Output.Html in do
    let documented ← match ((← Doc.Html.HtmlT.state).get? `Verso.Genre.Manual.docstring).getD (pure <| .mkObj []) >>= Json.getObj? with
      | .error e =>
        Doc.Html.HtmlT.logError e
        pure {}
      | .ok v =>
        pure v
    let mut ok : NameSet := {}
    for ⟨name, _⟩ in documented.toArray do
      let x := name.toName
      ok := ok.insert x


    let .ok ((namespaces : Array Name), (exceptions : Array Name), (present : List (Name × String)), (allTactics : Array Name)) := fromJson? info
      | panic! "Can't deserialize progress bar state"

    let check : NameMap (List Name) := present.foldr (init := {}) fun (ns, names) z =>
      -- The filter is needed here because `"".splitOn " " = [""]`
      z.insert ns (names.splitOn " " |>.filter (!·.isEmpty) |>.map String.toName)
    let check := check.insert `_root_ allRootNames.toList

    let undocTactics ← allTactics.filterM fun tacticName => do
      let st ← Doc.Html.HtmlT.state (genre := Manual)
      pure <| (TraverseState.getDomainObject? st tacticDomain tacticName.toString).isNone && tacticName ∉ exceptions

    let tacticPercent := undocTactics.size.toFloat * 100.0 / allTactics.size.toFloat

    let namespaces := namespaces.qsort (·.toString ≤ ·.toString)

    return {{
      <dl>
        {{namespaces.map fun ns =>
          let wanted := check.getD ns []
          let notDocumented := wanted.filter (!ok.contains ·) |>.mergeSort (fun x y => x.toString < y.toString)
          let percentMissing :=
            if wanted.isEmpty then 0
            else notDocumented.length.toFloat * 100.0 / wanted.length.toFloat
          {{
            <dt><code>{{ns.toString}}</code></dt>
            <dd>
              <details>
                <summary>
                  <progress id=s!"prog-{ns}" value=s!"{100 - percentMissing.toUInt8.toNat}" min="0" max="100"></progress>
                  <label for=s!"prog-ns">s!"Missing {percentMissing}%"</label>
                </summary>
                {{notDocumented |>.map (·.toString) |> String.intercalate ", " }}
                <pre>
                  {{ notDocumented.map ("{docstring " ++ ·.toString ++ "}\n\n") |> String.join }}
                </pre>
                <pre>
                  "```exceptions\n"
                  {{ notDocumented.map (·.toString ++ "\n") |> String.join }}
                  "```\n"
                </pre>
              </details>
            </dd>
          }}
        }}
        <dt>"Tactics"</dt>
        <dd>
          <details>
            <summary>
              <progress id="progress-tactics" value=s!"{100 - tacticPercent.toUInt8.toNat}" min="0" max="100"></progress>
              <label for="progress-tactics">s!"Missing {tacticPercent}% ({undocTactics.size}/{allTactics.size})"</label>
            </summary>
            {{ undocTactics.map (·.toString) |>.toList |> String.intercalate ", " }}
            <pre>
              {{ undocTactics.map ("{docstring " ++ ·.toString ++ "}\n") |>.toList |> String.join }}
            </pre>
            <pre>
              "```exceptions\n"
              {{ undocTactics.map (·.toString ++ "\n") |>.toList |> String.join }}
              "```\n"
            </pre>
          </details>
        </dd>
      </dl>
    }}
  toTeX := some (fun _ _ _ _ _ => pure <| Output.TeX.text "Unsupported")
