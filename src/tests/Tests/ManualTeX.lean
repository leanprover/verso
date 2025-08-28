import Verso
import VersoManual

namespace Verso.ManualTexTest

open Verso Genre Manual

def testTexMain : IO Unit := open Verso Genre Manual in do
 let logError (msg : String) := IO.eprintln msg
 let cfg : Config := {
   destination := "/tmp/_out",
   emitTeX := true,
   emitHtmlMulti := false,
   }
 let part : Doc.Part Manual := Doc.Part.mk #[] "title" none #[] #[]
 let exts : ExtensionImpls := (ExtensionImpls.fromLists [] [])
 let z := ReaderT.run (emitTeX logError cfg part) exts
 _ ← z
 return

def run (input : String) : IO String := do
  testTexMain
  pure s!"{input}"

end Verso.ManualTexTest
