import Lake
open Lake DSL

require subverso from git "https://github.com/leanprover/subverso.git"@"main"
require MD4Lean from git "https://github.com/david-christiansen/md4lean"@"parser"

package verso where
  precompileModules := true
  -- add package configuration options here

lean_lib Verso where
  srcDir := "src/verso"
  roots := #[`Verso]
  -- add library configuration options here

lean_lib VersoCodeHighlighting where
  srcDir := "src/code-highlighting"
  roots := #[`Verso.Code]

lean_lib VersoBlog where
  srcDir := "src/verso-blog"
  roots := #[`Verso.Genre.Blog]

@[default_target]
lean_exe «verso» where
  root := `Main
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true
