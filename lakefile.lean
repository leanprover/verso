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

lean_lib VersoManual where
  srcDir := "src/verso-manual"
  roots := #[`Verso.Genre.Manual]



@[default_target]
lean_exe «verso» where
  root := `Main
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true

lean_lib UsersGuide where
  srcDir := "doc"

@[default_target]
lean_exe usersguide where
  root := `UsersGuideMain
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true

-- A demo site that shows how to generate websites with Verso
lean_lib DemoSite where
  srcDir := "examples/website"
  roots := #[`DemoSite]

@[default_target]
lean_exe demosite where
  srcDir := "examples/website"
  root := `DemoSiteMain
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true


-- An example of a textbook project built in Verso
lean_lib DemoTextbook where
  srcDir := "examples/textbook"
  roots := #[`DemoTextbook]

@[default_target]
lean_exe demotextbook where
  srcDir := "examples/textbook"
  root := `DemoTextbookMain
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true

-- An example of a minimal nontrivial custom genre
lean_lib SimplePage where
  srcDir := "examples/custom-genre"
  roots := #[`SimplePage]

lean_exe simplepage where
  srcDir := "examples/custom-genre"
  root := `SimplePageMain
