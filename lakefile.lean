import Lake
open Lake DSL

require subverso from git "https://github.com/leanprover/subverso"@"structured-output"
require MD4Lean from git "https://github.com/acmepjz/md4lean"@"main"

package verso where
  precompileModules := false -- temporarily disabled to work around an issue with nightly-2025-03-30

@[default_target]
lean_lib VersoUtil where
  srcDir := "src/verso-util"
  roots := #[`VersoUtil]

@[default_target]
lean_lib Verso where
  srcDir := "src/verso"
  roots := #[`Verso]

@[default_target]
lean_lib MultiVerso where
  srcDir := "src/multi-verso"
  roots := #[`MultiVerso]

input_dir searchJs where
  path := "static-web/search"

@[default_target]
lean_lib VersoSearch where
  srcDir := "src/verso-search"
  -- Rebuild search when JS on disk changes
  needs := #[searchJs]

@[default_target]
lean_lib VersoBlog where
  srcDir := "src/verso-blog"
  roots := #[`VersoBlog]

@[default_target]
lean_lib VersoManual where
  srcDir := "src/verso-manual"
  roots := #[`VersoManual]

@[default_target]
lean_exe «verso» where
  root := `Main
  srcDir := "src/cli"

@[test_driver]
lean_exe «verso-tests» where
  root := `Tests
  srcDir := "src/tests"

@[default_target]
lean_exe «verso-demo» where
  root := `Main
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true

lean_lib UsersGuide where
  srcDir := "doc"
  leanOptions := #[⟨`weak.linter.verso.manual.headerTags, true⟩]

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
  supportInterpreter := true

-- An example of a package documentation project built in Verso
lean_lib PackageManual where
  srcDir := "examples/package-manual"
  roots := #[`PackageManual]

@[default_target]
lean_exe packagedocs where
  srcDir := "examples/package-manual"
  root := `PackageManualMain
  supportInterpreter := true

-- An example of a minimal nontrivial custom genre
@[default_target]
lean_lib SimplePage where
  srcDir := "examples/custom-genre"
  roots := #[`SimplePage]

@[default_target]
lean_exe simplepage where
  srcDir := "examples/custom-genre"
  root := `SimplePageMain
