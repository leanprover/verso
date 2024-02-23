import Lake
open Lake DSL

require std from git "https://github.com/leanprover/std4" @ "nightly-testing-2024-02-22"

package verso where
  -- add package configuration options here

lean_lib Verso where
  srcDir := "src/verso"
  roots := #[`Verso]
  -- add library configuration options here

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
