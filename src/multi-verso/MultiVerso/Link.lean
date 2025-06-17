import Lean.Data.Json
import MultiVerso.Path
import MultiVerso.Slug

open Lean
namespace Verso.Multi

/-- A link to a given piece of content -/
structure Link where
  path : Path
  htmlId : Slug
deriving ToJson, FromJson, BEq, Ord

/-- Constructs a link URL suitable for an `<a>` tag. -/
def Link.link (link : Link) : String :=
  link.path.link (htmlId := some link.htmlId.toString)
