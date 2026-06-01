/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import VersoManual.Theme
public import Lean.Data.Json

set_option linter.missingDocs true
set_option doc.verso true

/-!
Build helpers for the runtime theme-selection scaffolding: the inline no-flash head script, the
{lit}`window.versoThemes` data file, and the {lit}`:root[data-verso-theme="…"]`-scoped CSS
written into {lit}`verso-themes.css`.
-/

namespace Verso.Theme

open Lean (Json)

/-- The pieces of a theme that the picker / no-flash script need at runtime, JSON-encoded. -/
private def themeJson (n : Lean.Name) (t : ManualTheme) : Json :=
  let appearance := match t.appearance with | .light => "light" | .dark => "dark"
  let description : Json := t.description.map Json.str |>.getD .null
  let sourceLink : Json := match t.sourceLink with
    | none => .null
    | some s => Json.mkObj [("url", Json.str s.url), ("text", Json.str s.text)]
  Json.mkObj [
    ("id", Json.str n.toString),
    ("name", Json.str t.name),
    ("appearance", Json.str appearance),
    ("description", description),
    ("sourceLink", sourceLink)
  ]

/--
The contents of {lit}`-verso-data/verso-themes.js`. Exposes {lit}`window.versoThemes` with the
shape `{ themes: [...], defaultLight, defaultDark, codeSample }` so the picker can render the
choices and the live code preview.

{name}`codeSample` is a small fixed HTML string reusing the {lit}`.hl.lean` markup; the picker drops it
inside a {lit}`data-verso-theme`-scoped element to show what each theme will look like.
-/
public def windowVersoThemesJs
    (themes : ThemeRegistry)
    (defaultLight defaultDark defaultSingle : Lean.Name)
    (codeSample : String) : String :=
  let entries := themes.foldl (init := #[]) (fun acc n t => acc.push (themeJson n t))
  let payload := Json.mkObj [
    ("themes", Json.arr entries),
    ("defaultLight", Json.str defaultLight.toString),
    ("defaultDark", Json.str defaultDark.toString),
    ("defaultSingle", Json.str defaultSingle.toString),
    ("codeSample", Json.str codeSample)
  ]
  s!"window.versoThemes = {payload.compress};\n"

/--
The body of the synchronous head script that runs before paint and sets
{lit}`data-verso-theme` and {lit}`data-verso-appearance` on the document root so the first
painted frame matches the chosen theme. The {lit}`themes` argument is the available set; the
defaults are inlined here (not read from {lit}`window.versoThemes`) to avoid an ordering race.

Single-mode fallback is {lit}`defaultSingle` — the theme an author chose for readers who do
not follow the system appearance. First visits (no stored mode) use the same fallback so the
painted frame matches what the reader will see when they open the picker.
-/
public def themeInitScript
    (themes : ThemeRegistry)
    (defaultLight defaultDark defaultSingle : Lean.Name) : String :=
  let pairs := themes.foldl (init := ([] : List String)) fun acc n t =>
    let a := match t.appearance with | .light => "light" | .dark => "dark"
    s!"\"{n.toString}\":\"{a}\"" :: acc
  let table := "{" ++ ",".intercalate pairs.reverse ++ "}"
  s!"(function() \{
  var APPEARANCE = {table};
  var DEFAULT_LIGHT = \"{defaultLight.toString}\";
  var DEFAULT_DARK = \"{defaultDark.toString}\";
  var DEFAULT_SINGLE = \"{defaultSingle.toString}\";
  function readMode() \{ try \{ return localStorage.getItem(\"verso-theme-mode\"); } catch (e) \{ return null; } }
  function readKey(k) \{ try \{ return localStorage.getItem(k); } catch (e) \{ return null; } }
  var mode = readMode();
  var prefersDark = window.matchMedia && window.matchMedia(\"(prefers-color-scheme: dark)\").matches;
  var picked = null;
  if (mode === \"single\") \{
    picked = readKey(\"verso-theme-single\") || DEFAULT_SINGLE;
  } else if (mode === \"auto\") \{
    picked = prefersDark ? readKey(\"verso-theme-dark\") : readKey(\"verso-theme-light\");
    if (!picked) picked = prefersDark ? DEFAULT_DARK : DEFAULT_LIGHT;
  }
  if (!picked || !APPEARANCE.hasOwnProperty(picked)) \{
    // First visit (no mode set): use the single-mode default the author configured so the
    // painted frame matches what the picker would show on this device.
    picked = DEFAULT_SINGLE;
  }
  var appearance = APPEARANCE[picked] || (prefersDark ? \"dark\" : \"light\");
  document.documentElement.setAttribute(\"data-verso-theme\", picked);
  document.documentElement.setAttribute(\"data-verso-appearance\", appearance);
  function onChange(e) \{
    if ((readMode() || \"auto\") !== \"auto\") return;
    var dark = e.matches;
    var k = dark ? \"verso-theme-dark\" : \"verso-theme-light\";
    var p = readKey(k);
    if (!p || !APPEARANCE.hasOwnProperty(p)) p = dark ? DEFAULT_DARK : DEFAULT_LIGHT;
    document.documentElement.setAttribute(\"data-verso-theme\", p);
    document.documentElement.setAttribute(\"data-verso-appearance\", APPEARANCE[p]);
  }
  var mq = window.matchMedia && window.matchMedia(\"(prefers-color-scheme: dark)\");
  if (mq) \{
    if (mq.addEventListener) mq.addEventListener(\"change\", onChange);
    else if (mq.addListener) mq.addListener(onChange);
  }
})();"

/--
Produces the body of {lit}`verso-themes.css`:

- font-face rules from every available theme (one block per theme; content dedup is the caller's
  job);
- an unscoped `:root` block carrying the {name}`single`'s variables — what the server-rendered
  HTML uses before the no-flash script attaches {lit}`data-verso-theme`. {name}`single` is the
  resolved single-mode default theme;
- an {lit}`@media (prefers-color-scheme: dark)` block carrying the {name}`Verso.Theme.ManualTheme`
  named by {name}`defaultDark` (no-JS fallback only — the no-flash script always sets a concrete
  attribute);
- one `:root[data-verso-theme="…"]` block per registered theme so the picker can swap themes by
  flipping the attribute.

{name}`single` is always one of the registered themes, so its font and asset URLs resolve against
the same {lit}`-verso-data/themes/<name>` root as the attribute-scoped blocks; no separate
page-theme asset root is needed.
-/
public def «verso-themes.css»
    (single : ManualTheme)
    (themes : ThemeRegistry)
    (_defaultLight defaultDark : Lean.Name) : String := Id.run do
  let assetRoot (n : Lean.Name) : String := s!"-verso-data/themes/{n.toString}"
  let mut out := ""
  -- Font-face rules.
  for (n, t) in themes do
    let rules := t.fontFaceRules (assetRoot n)
    unless rules.isEmpty do out := out ++ rules
  -- Unscoped :root block from the single-mode default.
  out := out ++ s!":root \{\n{single.cssVariables}}\n"
  -- @media dark fallback for no-JS visitors.
  if let some t := themes.find? defaultDark then
    out := out ++ s!"@media (prefers-color-scheme: dark) \{\n  :root \{\n{t.cssVariables}  }\n}\n"
  -- Attribute-scoped blocks for every registered theme.
  for (n, t) in themes do
    out := out ++ s!":root[data-verso-theme=\"{n.toString}\"] \{\n{t.cssVariables}}\n"
    let extra := t.extraCss (assetRoot n)
    unless extra.isEmpty do
      out := out ++ s!":where(:root[data-verso-theme=\"{n.toString}\"]) \{\n{extra}}\n"
  return out
