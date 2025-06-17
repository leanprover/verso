import Std.Data.HashMap
import Std.Time.DateTime

open Std
open Std.Time

namespace Verso.Multi

inductive XrefSource where
  | localOverride (path : System.FilePath)
  | remoteOverride (URL : String)
  | default
deriving BEq


/--
A remote collection of documentation.
-/
structure Remote where
  /-- The root URL for the documentation. -/
  root : String
  /-- Sources to be attempted in order. -/
  source : List XrefSource
deriving BEq

structure RemoteMeta where
  lastUpdated : Timestamp

structure Manifest where
  /-- A mapping from external source names to their root URLs. -/
  sources : HashMap String Remote
  /-- A relative directory that governs where to store Verso cross-reference data -/
  outputDir : System.FilePath
