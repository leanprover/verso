import Lake
open Lake DSL

require std from git "https://github.com/leanprover/std4" @ "main"

package «leandoc» where
  -- add package configuration options here

lean_lib LeanDoc where
  srcDir := "src/leandoc"
  roots := #[`LeanDoc.Doc, `LeanDoc.Output, `LeanDoc.Parser, `LeanDoc.Examples, `LeanDoc.Method, `LeanDoc.Syntax, `LeanDoc.SyntaxUtils]
  -- add library configuration options here

lean_lib LeanBlog where
  srcDir := "src/leanblog"
  roots := #[`LeanDoc.Genre.Blog]

@[default_target]
lean_exe «leandoc» where
  root := `Main
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true

lean_lib BlogContents where

@[default_target]
lean_exe «demoblog» where
  root := `DemoBlog
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true
