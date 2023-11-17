import Lean.Data.RBMap

import LeanDoc.Doc
import LeanDoc.Html
import LeanDoc.Doc.Html

namespace LeanDoc.Genre

namespace Blog

open LeanDoc.Doc (Part)
open LeanDoc.Html
open LeanDoc.Doc.Html
open Lean (RBMap)

structure Date where
  year : Int
  month : Nat
  day : Nat

structure Post where
  date : Date
  authors : List String
  content : Part
  draft : Bool
deriving TypeName

private def filterString (p : Char → Bool) (str : String) : String := Id.run <| do
  let mut out := ""
  for c in str.toList do
    if p c then out := out.push c
  pure out

def defaultPostName (date : Date) (title : String) : String :=
  s!"{date.year}-{date.month}-{date.day}-{slugify title}"
where
  slugify str := Id.run do
    let mut slug := ""
    for c in str.toList do
      if c == ' ' then slug := slug.push '-'
      else if c.isAlpha || c.isDigit then slug := slug.push c.toLower
      else continue
    pure slug

structure Config where
  destination : System.FilePath := "./_site"
  showDrafts : Bool := false
  postName : Date → String → String := defaultPostName
deriving Inhabited


structure Template.Params.Val where
  value : Dynamic
  fallback : Array Dynamic

namespace Template.Params.Val

def get? [TypeName α] (value : Val) : Option α :=
  value.value.get? α <|> do
    for v in value.fallback do
      if let some x := v.get? α then return x
    none

def getD [TypeName α] (value : Val) (default : α) : α :=
  value.get? |>.getD default

end Template.Params.Val

deriving instance TypeName for String



instance : Coe String Template.Params.Val where
  coe str := ⟨.mk str, #[.mk <| Html.text str]⟩

instance : Coe Html Template.Params.Val where
  coe
   | .text str => ↑str
   | other => ⟨.mk other, #[]⟩

def Template.Params := RBMap String Params.Val compare

namespace Template.Params

def ofList (params : List (String × Val)) : Params :=
  Lean.RBMap.ofList params

def toList (params : Params) : List (String × Val) :=
  Lean.RBMap.toList params

def insert (params : Params) (key : String) (val : Val) : Params :=
  Lean.RBMap.insert params key val



def forPart (txt : Part) : Params := ofList [
  ("title", ⟨.mk txt.titleString, #[.mk {{ <h1> {{ txt.title.map (ToHtml.toHtml {}) }} </h1>}}]⟩),
  ("content", txt.content.map (ToHtml.toHtml {}) ++ txt.subParts.map (ToHtml.toHtml {}))
]

end Template.Params

inductive Template.Error where
  | missingParam (param : String)
  | wrongParamType (param : String) (type : Lean.Name)

abbrev TemplateM (α : Type) : Type := ReaderT Template.Params (Except Template.Error) α

abbrev Template := TemplateM Html

structure Theme where
  primaryTemplate : Template
  pageTemplate : Template
  postTemplate : Template
  archiveEntryTemplate : Template
  adHocTemplates : Array String → Option Template := fun _ => none

namespace Template

def param [TypeName α] (key : String) : TemplateM α := do
  match (← read).find? key with
  | none => throw <| .missingParam key
  | some val =>
    if let some v := val.get? (α := α) then return v
    else throw <| .wrongParamType key (TypeName.typeName α)

namespace Params

end Params

namespace Default

def primary : Template := do return #[{{
  <html>
    <head>
      <title>{{ (← param (α := String) "title") }}</title>
    </head>
    <body>
      <h1>{{ (← param "title") }}</h1>
      {{ (← param "content") }}
    </body>
  </html>
}}]

def page : Template := param "content"

def post : Template := param "content"

def archiveEntry : Template := do
  let post : Post ← param "post"
  return #[{{
  <li>
    {{
    match post.date with
    | Date.mk y m d => {{<span class="date"> s!"{y}-{m}-{d}" </span>}}
    }}
    <span class="name">{{post.content.title.map (ToHtml.toHtml {})}}</span>
  </li>
}}]

end Default

end Template

open Template.Default in
def Theme.default : Theme where
  primaryTemplate := primary
  pageTemplate := page
  postTemplate := post
  archiveEntryTemplate := archiveEntry

inductive Dir α where
  | pages (subPages : Array α)
  | blog (posts : Array Post)

inductive Nav where
  | page (name : String) (text : Part) (contents : Dir Nav)


structure Site where
  frontPage : Part
  contents : Dir Nav

namespace Generate

structure Context where
  dir : System.FilePath
  path : List String := []
  config : Config

end Generate

abbrev GenerateM := ReaderT Generate.Context IO

namespace Template

def render (template : Template) (params : Template.Params) : GenerateM Html := do
  match template params with
  | .error err =>
    let message := match err with
    | .missingParam p => ↑ s!"Missing parameter: '{p}'"
    | .wrongParamType p t => ↑ s!"Parameter '{p}' doesn't have a {t} fallback"
    throw message
  | .ok v => pure v

def renderMany (templates : List Template) (params : Template.Params) : GenerateM Html := do
    let mut params := params
    let mut output := Html.empty
    for template in templates do
      output ← template.render params
      params := params.insert "content" ↑output
    pure output

end Template



def currentDir : GenerateM System.FilePath := do
  let base := (← read).dir
  let steps := (← read).path
  pure (steps.foldl (·.join ⟨·⟩) base)

def showDrafts : GenerateM Bool := (·.config.showDrafts) <$> read
def postName (post : Post) : GenerateM String := do
  pure <| (← read).config.postName post.date post.content.titleString

def inDir (dir : String) (act : GenerateM α) : GenerateM α :=
  withReader (fun ctxt => {ctxt with path := ctxt.path ++ [dir]}) act

def ensureDir (dir : System.FilePath) : IO Unit := do
  if !(← dir.pathExists) then
    IO.FS.createDirAll dir
  if !(← dir.isDir) then
    throw (↑ s!"Not a directory: {dir}")

mutual
  partial def Dir.generate (theme : Theme) : Dir Nav → GenerateM Unit
    | .pages content => do
      for p in content do
        Nav.generate theme p
    | .blog posts =>
      for post in posts do
        if post.draft && !(← showDrafts) then continue
        let filename := (← currentDir).join (← postName post)

        let output ← Template.renderMany [theme.postTemplate, theme.primaryTemplate] <| .forPart post.content
        ensureDir filename
        IO.FS.withFile (filename.join "index.html") .write fun h => do
          h.putStrLn output.asString


  partial def Nav.generate (theme : Theme) : Nav → GenerateM Unit
    | .page name txt subPages => do
      ensureDir <| (← currentDir).join name
      inDir name do
        -- TODO more configurable template context
        let output ← Template.renderMany [theme.pageTemplate, theme.primaryTemplate] <| .forPart txt

        IO.FS.withFile ((← currentDir).join "index.html") .write fun h =>
          h.putStrLn output.asString
        subPages.generate theme
end

def Site.generate (theme : Theme) (site : Site): GenerateM Unit := do
  let root ← currentDir
  ensureDir root
  let output ← Template.renderMany [theme.pageTemplate, theme.primaryTemplate] <| .forPart site.frontPage
  let filename := root.join "index.html"
  IO.FS.withFile filename .write fun h => do
    h.putStrLn output.asString

  site.contents.generate theme

def blogMain (theme : Theme) (site : Site) (options : List String) : IO UInt32 := do
  let cfg ← opts {} options
  site.generate theme {dir := cfg.destination, config := cfg}
  pure 0

where
  opts (cfg : Config)
    | ("--output"::dir::more) => opts {cfg with destination := dir} more
    | ("--drafts"::more) => opts {cfg with showDrafts := true} more
    | (other :: _) => throw (↑ s!"Unknown option {other}")
    | [] => pure cfg

end Blog
namespace Manual

end Manual
