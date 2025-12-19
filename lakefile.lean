import Lake
open Lake DSL

require subverso from git "https://github.com/leanprover/subverso"@"main"
require MD4Lean from git "https://github.com/acmepjz/md4lean"@"main"
require plausible from git "https://github.com/leanprover-community/plausible"@"main"

package verso where
  precompileModules := false -- temporarily disabled to work around an issue with nightly-2025-03-30
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target]
lean_lib VersoUtil where
  srcDir := "src/verso-util"
  roots := #[`VersoUtil]

input_dir staticWeb where
  text := true
  path := "static-web"

input_dir vendorJs where
  text := true
  path := "vendored-js"

@[default_target]
lean_lib Verso where
  srcDir := "src/verso"
  roots := #[`Verso]
  needs := #[staticWeb, vendorJs]

@[default_target]
lean_lib MultiVerso where
  srcDir := "src/multi-verso"
  roots := #[`MultiVerso]

@[default_target]
lean_lib VersoSearch where
  srcDir := "src/verso-search"
  -- Rebuild search when JS on disk changes
  needs := #[staticWeb]

@[default_target]
lean_lib VersoBlog where
  srcDir := "src/verso-blog"
  roots := #[`VersoBlog]

@[default_target]
lean_lib VersoManual where
  srcDir := "src/verso-manual"
  roots := #[`VersoManual]
  needs := #[staticWeb]

@[default_target]
lean_exe «verso» where
  root := `Main
  srcDir := "src/cli"
  supportInterpreter := true

@[default_target]
lean_lib VersoLiterate where
  roots := #[`VersoLiterate]
  srcDir := "src/verso-literate"

@[default_target]
lean_exe «verso-literate» where
  root := `Main
  srcDir := "src/verso-literate"
  supportInterpreter := true

input_file «verso-html-css» where
  text := true
  path := "src/verso-html/code.css"

@[default_target]
lean_exe «verso-html» where
  root := `Main
  srcDir := "src/verso-html"
  needs := #[«verso-html-css»]
  supportInterpreter := true

@[default_target]
lean_lib Tests where
  srcDir := "src/tests"

@[test_driver]
lean_exe «verso-tests» where
  root := `TestMain
  srcDir := "src/tests"
  supportInterpreter := true

@[default_target]
lean_exe «verso-demo» where
  root := `Main
  supportInterpreter := true

lean_lib UsersGuide where
  srcDir := "doc"
  leanOptions := #[⟨`weak.linter.verso.manual.headerTags, true⟩]

@[default_target]
lean_exe usersguide where
  root := `UsersGuideMain
  supportInterpreter := true

-- A demo site that shows how to generate websites with Verso
lean_lib DemoSite where
  srcDir := "test-projects/website"
  roots := #[`DemoSite]

@[default_target]
lean_exe demosite where
  srcDir := "test-projects/website"
  root := `DemoSiteMain
  supportInterpreter := true

-- An example of a textbook project built in Verso
lean_lib DemoTextbook where
  srcDir := "test-projects/textbook"
  roots := #[`DemoTextbook]

@[default_target]
lean_exe demotextbook where
  srcDir := "test-projects/textbook"
  root := `DemoTextbookMain
  supportInterpreter := true

-- An example of a package documentation project built in Verso
lean_lib PackageManual where
  srcDir := "test-projects/package-manual"
  roots := #[`PackageManual]

@[default_target]
lean_exe packagedocs where
  srcDir := "test-projects/package-manual"
  root := `PackageManualMain
  supportInterpreter := true

-- An example of a minimal nontrivial custom genre
@[default_target]
lean_lib SimplePage where
  srcDir := "test-projects/custom-genre"
  roots := #[`SimplePage]

@[default_target]
lean_exe simplepage where
  srcDir := "test-projects/custom-genre"
  root := `SimplePageMain
  supportInterpreter := true


module_facet literate mod : System.FilePath := do
  let ws ← getWorkspace

  let exeJob ← «verso-literate».fetch
  let modJob ← mod.olean.fetch

  let buildDir := ws.root.buildDir
  let litFile := mod.filePath (buildDir / "literate") "json"

  exeJob.bindM fun exeFile =>
    modJob.mapM fun _oleanPath => do
      addLeanTrace
      buildFileUnlessUpToDate' (text := true) litFile <|
        proc {
          cmd := exeFile.toString
          args := #[mod.name.toString, litFile.toString]
          env := ← getAugmentedEnv
        }
      pure litFile

library_facet literate lib : Array System.FilePath := do
  let mods ← (← lib.modules.fetch).await
  let lits ← mods.mapM fun x =>
    x.facet `literate |>.fetch
  pure <| Job.collectArray lits


package_facet literate pkg : Array System.FilePath := do
  let libs := Job.collectArray (← pkg.leanLibs.mapM (·.facet `literate |>.fetch))
  let exes := Job.collectArray (← pkg.leanExes.mapM (·.toLeanLib.facet `literate |>.fetch))
  return libs.zipWith (·.flatten ++ ·.flatten) exes
