import Lean

import LeanDoc.Doc
import LeanDoc.Doc.Html
import LeanDoc.Genre.Blog.Basic
import LeanDoc.Genre.Blog.Site
import LeanDoc.Output.Html

open Lean (RBMap)

open LeanDoc Doc Output Html
open LeanDoc.Genre Blog

private def next (xs : Array α) : Option (α × Array α) :=
  if _ : 0 < xs.size then
    some (xs[0], xs.extract 1 xs.size)
  else
    none

instance [Monad m] : MonadPath (HtmlT Blog m) where
  currentPath := do
    let (_, ctxt, _) ← read
    pure ctxt.path

instance [Monad m] : MonadConfig (HtmlT Blog m) where
  currentConfig := do
    let (_, ctxt, _) ← read
    pure ctxt.config

open HtmlT

defmethod Highlighted.Token.Kind.«class» : Highlighted.Token.Kind → String
  | .var _ => "var"
  | .sort  => "sort"
  | .const _ _ => "const"
  | .keyword _ _ => "keyword"
  | .unknown => "unknown"

defmethod Highlighted.Token.Kind.data : Highlighted.Token.Kind → String
  | .const n _ => "const-" ++ toString n
  | .var ⟨v⟩ => "var-" ++ toString v
  | _ => ""


def hover (content : Html) : Html := {{
  <div class="hover-container"><div class="hover-info"> {{ content }} </div></div>
}}

defmethod Highlighted.Token.Kind.hover? : (tok : Highlighted.Token.Kind) → Option Html
  | .const n doc | .keyword (some n) doc =>
    let docs := match doc with
      | none => .empty
      | some txt => {{<hr/><p>{{txt}}</p>}}
    some <| hover {{ {{toString n}} {{docs}} }}
  | _ => none


defmethod Highlighted.Token.toHtml (tok : Highlighted.Token) : Html := {{
  <span class={{tok.kind.«class» ++ " token"}} "data-binding"={{tok.kind.data}}>{{tok.content}}{{tok.kind.hover?.getD .empty}}</span>
}}


defmethod Highlighted.Span.Kind.«class» : Highlighted.Span.Kind → String
  | .info => "info"
  | .warning => "warning"
  | .error => "error"

partial defmethod Highlighted.toHtml : Highlighted → Html
  | .token t => t.toHtml
  | .text str => str
  | .span s info hl => {{<span class={{"has-info " ++ s.«class»}}><span class="hover-container"><span class={{"hover-info message " ++ s.«class»}}>{{info}}</span></span>{{toHtml hl}}</span>}}
  | .point s info => {{<span class={{"message " ++ s.«class»}}>{{info}}</span>}}
  | .seq hls => hls.map toHtml

partial instance : GenreHtml Blog IO where
  part _ m := nomatch m
  block go
    | .highlightedCode contextName hls, _contents => do
      pure {{ <pre class="hl lean" "data-lean-context"={{toString contextName}}> {{ hls.toHtml }} </pre> }}
    | .htmlDiv classes, contents => do
      pure {{ <div class={{classes}}> {{← contents.mapM go}} </div> }}
    | .blob html, _ => pure html
  inline go
    | .label x, contents => do
      let contentHtml ← contents.mapM go
      let some tgt := (← state).targets.find? x
        | panic! "No label for {x}"
      pure {{ <span id={{tgt.htmlId}}> {{ contentHtml }} </span>}}
    | .ref x, contents => do
      match (← state).targets.find? x with
      | none =>
        HtmlT.logError "Can't find target {x}"
        pure {{<strong class="internal-error">s!"Can't find target {x}"</strong>}}
      | some tgt =>
        let addr := s!"{String.join ((← relative tgt.path).intersperse "/")}#{tgt.htmlId}"
        go <| .link contents addr
    | .pageref x, contents => do
      match (← state).pageIds.find? x with
      | none =>
        HtmlT.logError "Can't find target {x}"
        pure {{<strong class="internal-error">s!"Can't find target {x}"</strong>}}
      | some path =>
        let addr := String.join ((← relative path).intersperse "/")
        go <| .link contents addr
    | .htmlSpan classes, contents => do
      pure {{ <span class={{classes}}> {{← contents.mapM go}} </span> }}
    | .blob html, _ => pure html

namespace LeanDoc.Genre.Blog.Template

structure Params.Val where
  value : Dynamic
  fallback : Array Dynamic

namespace Params.Val

def get? [TypeName α] (value : Val) : Option α :=
  value.value.get? α <|> do
    for v in value.fallback do
      if let some x := v.get? α then return x
    none

def getD [TypeName α] (value : Val) (default : α) : α :=
  value.get? |>.getD default

end Params.Val

deriving instance TypeName for String


instance : Coe String Template.Params.Val where
  coe str := ⟨.mk str, #[.mk <| Html.text str]⟩

instance : Coe Html Template.Params.Val where
  coe
   | .text str => ↑str
   | other => ⟨.mk other, #[]⟩


def Params := RBMap String Params.Val compare

instance : EmptyCollection Params := inferInstanceAs <| EmptyCollection (RBMap _ _ _)

namespace Params

def ofList (params : List (String × Val)) : Params :=
  Lean.RBMap.ofList params

def toList (params : Params) : List (String × Val) :=
  Lean.RBMap.toList params

def insert (params : Params) (key : String) (val : Val) : Params :=
  Lean.RBMap.insert params key val

def erase (params : Params) (key : String) : Params :=
  Lean.RBMap.erase params key


end Params

inductive Error where
  | missingParam (param : String)
  | wrongParamType (param : String) (type : Lean.Name)

structure Context where
  site : Site
  config : Config
  path : List String
  params : Params
  builtInStyles : Lean.HashSet String
  builtInScripts : Lean.HashSet String

end Template

abbrev TemplateM (α : Type) : Type := ReaderT Template.Context (Except Template.Error) α

abbrev Template := TemplateM Html

instance : MonadPath TemplateM where
  currentPath := Template.Context.path <$> read

instance : MonadConfig TemplateM where
  currentConfig := Template.Context.config <$> read

namespace Template

def param? [TypeName α] (key : String) : TemplateM (Option α) := do
  match (← read).params.find? key with
  | none => return none
  | some val =>
    if let some v := val.get? (α := α) then return (some v)
    else throw <| .wrongParamType key (TypeName.typeName α)


def param [TypeName α] (key : String) : TemplateM α := do
  match (← read).params.find? key with
  | none => throw <| .missingParam key
  | some val =>
    if let some v := val.get? (α := α) then return v
    else throw <| .wrongParamType key (TypeName.typeName α)

def builtinHeader : TemplateM Html := do
  let mut out := .empty
  for style in (← read).builtInStyles do
    out := out ++ {{<style>"\n"{{style}}"\n"</style>"\n"}}
  for script in (← read).builtInScripts do
    out := out ++ {{<script>"\n"{{script}}"\n"</script>"\n"}}
  pure out

namespace Params

end Params
