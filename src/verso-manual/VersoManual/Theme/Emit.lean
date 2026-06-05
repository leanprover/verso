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

/--
The theme mode a manual starts new readers in, and the appearance it serves to readers without
JavaScript.
-/
public inductive ThemeMode where
  /-- Track the operating system's {lit}`prefers-color-scheme`. -/
  | followSystem
  /-- Always start with the default light theme. -/
  | light
  /-- Always start with the default dark theme. -/
  | dark
deriving DecidableEq, Repr

instance : Inhabited ThemeMode := ⟨.followSystem⟩

/-- The picker and no-flash mode string for a theme mode: {lit}`auto`, {lit}`light`, or {lit}`dark`. -/
public def ThemeMode.modeString : ThemeMode → String
  | .followSystem => "auto"
  | .light => "light"
  | .dark => "dark"

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
shape `{ themes: [...], defaultLight, defaultDark, defaultMode, codeSample }` so the picker can
render the choices and the live code preview.

{name}`defaultMode` is the {name}`ThemeMode` an author configured, encoded as the picker's mode
string, so a new reader's Appearance control starts on it.

{name}`codeSample` is a small fixed HTML string reusing the {lit}`.hl.lean` markup; the picker drops it
inside a {lit}`data-verso-theme`-scoped element to show what each theme will look like.
-/
public def windowVersoThemesJs
    (themes : ThemeRegistry)
    (defaultLight defaultDark : Lean.Name)
    (defaultMode : ThemeMode)
    (codeSample : String) : String :=
  let entries := themes.foldl (init := #[]) (fun acc n t => acc.push (themeJson n t))
  let payload := Json.mkObj [
    ("themes", Json.arr entries),
    ("defaultLight", Json.str defaultLight.toString),
    ("defaultDark", Json.str defaultDark.toString),
    ("defaultMode", Json.str defaultMode.modeString),
    ("codeSample", Json.str codeSample)
  ]
  s!"window.versoThemes = {payload.compress};\n"

/--
The body of the synchronous head script that runs before paint and sets
{lit}`data-verso-theme` and {lit}`data-verso-appearance` on the document root so the first
painted frame matches the chosen theme. The {lit}`themes` argument is the available set; the
defaults are inlined here (not read from {lit}`window.versoThemes`) to avoid an ordering race.

The stored {lit}`verso-theme-mode` is one of {lit}`light`, {lit}`dark`, or {lit}`auto`.
In {lit}`light`/{lit}`dark` mode the painted theme is the reader's chosen light or dark theme
(falling back to {lit}`defaultLight`/{lit}`defaultDark`); in {lit}`auto` mode it tracks the OS
{lit}`prefers-color-scheme`. First visits (no stored mode) use the author's configured
{name}`ThemeMode` (inlined as {lit}`DEFAULT_MODE`), which defaults to {lit}`auto` so a new reader
follows their system appearance.
-/
public def themeInitScript
    (themes : ThemeRegistry)
    (defaultLight defaultDark : Lean.Name)
    (defaultMode : ThemeMode) : String :=
  let pairs := themes.foldl (init := ([] : List String)) fun acc n t =>
    let a := match t.appearance with | .light => "light" | .dark => "dark"
    s!"\"{n.toString}\":\"{a}\"" :: acc
  let table := "{" ++ ",".intercalate pairs.reverse ++ "}"
  s!"(function() \{
  var APPEARANCE = {table};
  var DEFAULT_LIGHT = \"{defaultLight.toString}\";
  var DEFAULT_DARK = \"{defaultDark.toString}\";
  var DEFAULT_MODE = \"{defaultMode.modeString}\";
  function readMode() \{ try \{ return localStorage.getItem(\"verso-theme-mode\"); } catch (e) \{ return null; } }
  function readKey(k) \{ try \{ return localStorage.getItem(k); } catch (e) \{ return null; } }
  var prefersDark = window.matchMedia && window.matchMedia(\"(prefers-color-scheme: dark)\").matches;
  var mode = readMode() || DEFAULT_MODE;
  var picked = null;
  if (mode === \"light\") \{
    picked = readKey(\"verso-theme-light\") || DEFAULT_LIGHT;
  } else if (mode === \"dark\") \{
    picked = readKey(\"verso-theme-dark\") || DEFAULT_DARK;
  } else \{
    picked = prefersDark ? (readKey(\"verso-theme-dark\") || DEFAULT_DARK)
                         : (readKey(\"verso-theme-light\") || DEFAULT_LIGHT);
  }
  if (!picked || !APPEARANCE.hasOwnProperty(picked)) \{
    picked = prefersDark ? DEFAULT_DARK : DEFAULT_LIGHT;
  }
  var appearance = APPEARANCE[picked] || (prefersDark ? \"dark\" : \"light\");
  document.documentElement.setAttribute(\"data-verso-theme\", picked);
  document.documentElement.setAttribute(\"data-verso-appearance\", appearance);
  function onChange(e) \{
    if ((readMode() || DEFAULT_MODE) !== \"auto\") return;
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
- the no-JavaScript defaults, governed by {name}`defaultMode`. In {name (full := ThemeMode.followSystem)}`followSystem`
  mode, when both {name}`defaultLight` and {name}`defaultDark` are available, an unscoped `:root`
  block carries the light default and an {lit}`@media (prefers-color-scheme: dark)` block carries
  the dark default, so readers without JavaScript follow their system appearance. In
  {name (full := ThemeMode.light)}`light`/{name (full := ThemeMode.dark)}`dark` mode (or when only
  one appearance has a theme), a single `:root` block carries that appearance's default and there
  is no media-query swap. The no-flash script always sets a concrete {lit}`data-verso-theme`, so
  this affects only readers without JavaScript and the first pre-script frame;
- one `:root[data-verso-theme="…"]` block per registered theme so the picker can swap themes by
  flipping the attribute.

The default themes are always among the registered themes, so their font and asset URLs resolve
against the same {lit}`-verso-data/themes/<name>` root as the attribute-scoped blocks; no separate
page-theme asset root is needed.
-/
public def «verso-themes.css»
    (themes : ThemeRegistry)
    (defaultLight defaultDark : Lean.Name)
    (defaultMode : ThemeMode) : String := Id.run do
  let assetRoot (n : Lean.Name) : String := s!"-verso-data/themes/{n.toString}"
  let mut out := ""
  -- Font-face rules.
  for (n, t) in themes do
    let rules := t.fontFaceRules (assetRoot n)
    unless rules.isEmpty do out := out ++ rules
  -- No-JavaScript defaults. In follow-system mode with both defaults available, a light `:root`
  -- plus a dark media block lets no-JS readers track the system. In light/dark mode, or when only
  -- one appearance has a theme, a single `:root` block carries that appearance's default with no
  -- media swap. (The available set always contains both defaults, so the missing-default `<|>`
  -- chains are defensive.)
  let light? := themes.find? defaultLight
  let dark? := themes.find? defaultDark
  let any? := themes.toList.head?.map (·.2)
  let rootOf (t : ManualTheme) : String := s!":root \{\n{t.cssVariables}}\n"
  match defaultMode with
  | .followSystem =>
    match light?, dark? with
    | some l, some d =>
      out := out ++ rootOf l
      out := out ++ s!"@media (prefers-color-scheme: dark) \{\n  :root \{\n{d.cssVariables}  }\n}\n"
    | _, _ =>
      if let some t := light? <|> dark? <|> any? then out := out ++ rootOf t
  | .light =>
    if let some t := light? <|> dark? <|> any? then out := out ++ rootOf t
  | .dark =>
    if let some t := dark? <|> light? <|> any? then out := out ++ rootOf t
  -- Attribute-scoped blocks for every registered theme.
  for (n, t) in themes do
    out := out ++ s!":root[data-verso-theme=\"{n.toString}\"] \{\n{t.cssVariables}}\n"
    let extra := t.extraCss (assetRoot n)
    unless extra.isEmpty do
      out := out ++ s!":where(:root[data-verso-theme=\"{n.toString}\"]) \{\n{extra}}\n"
  return out
