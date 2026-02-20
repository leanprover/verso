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

input_file tutorialDefaultCss where
  text := true
  path := "src/verso-tutorial/default.css"

@[default_target]
lean_lib VersoTutorial where
  srcDir := "src/verso-tutorial"
  roots := #[`VersoTutorial]
  needs := #[tutorialDefaultCss]

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

@[default_target]
lean_lib VersoLiterateCode where
  srcDir := "src/verso-literate-code"
  roots := #[`VersoLiterateCode]

input_file «verso-html-css» where
  text := true
  path := "src/verso-html/code.css"

@[default_target]
lean_exe «verso-html» where
  root := `Main
  srcDir := "src/verso-html"
  needs := #[«verso-html-css»]
  supportInterpreter := true

input_file «verso-literate-html-css» where
  text := true
  path := "src/verso-literate-html/literate.css"

input_dir literateStaticWeb where
  text := true
  path := "static-web/literate"

@[default_target]
lean_exe «verso-literate-html» where
  root := `Main
  srcDir := "src/verso-literate-html"
  needs := #[«verso-literate-html-css», literateStaticWeb]
  supportInterpreter := true

@[default_target]
lean_exe «verso-literate-plan» where
  root := `Main
  srcDir := "src/verso-literate-plan"
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

@[default_target]
lean_lib TutorialExample where
  srcDir := "test-projects/tutorial-test"

@[default_target]
lean_exe «tutorial-example» where
  srcDir := "test-projects/tutorial-test"
  root := `Main
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

package_facet «literate-html» pkg : System.FilePath := do
  let ws ← getWorkspace
  let buildDir := ws.root.buildDir
  let litDir := buildDir / "literate"
  let htmlDir := buildDir / "literate-html"
  let planFile := buildDir / "literate-plan"
  let moduleListFile := buildDir / "literate-modules"
  let tomlFile := ws.root.dir / "literate.toml"

  -- Build literate JSON for all libraries
  let litJobs := Job.collectArray (← pkg.leanLibs.mapM (·.facet `literate |>.fetch))

  -- Fetch the plan executable
  let planExeJob ← «verso-literate-plan».fetch

  -- Fetch the HTML generator executable
  let htmlExeJob ← «verso-literate-html».fetch

  -- Collect module names from all default-target libraries
  let moduleNames ← pkg.leanLibs.foldlM (init := #[]) fun acc lib => do
    let mods ← (← lib.modules.fetch).await
    return acc ++ mods.map (·.name.toString)

  htmlExeJob.bindM fun htmlExeFile =>
    planExeJob.bindM fun planExeFile =>
      litJobs.mapM fun _litFiles => do

        if ← tomlFile.pathExists then
          addTrace (← computeTrace tomlFile)
        else
          addPureTrace "No literate TOML config file"

        -- Write module list and create plan
        let moduleList := ("\n".intercalate moduleNames.toList ++ "\n")
        addPureTrace moduleList
        buildFileUnlessUpToDate' moduleListFile do
          IO.FS.writeFile moduleListFile moduleList

        buildFileUnlessUpToDate' planFile do
          let planArgs := #[moduleListFile.toString, planFile.toString] ++
            (if ← tomlFile.pathExists then #[tomlFile.toString] else #[])
          proc {
            cmd := planExeFile.toString
            args := planArgs
            env := ← getAugmentedEnv
          }

        -- Run HTML generator with --plan and optionally --config
        buildUnlessUpToDate htmlDir (← getTrace) (htmlDir.addExtension "trace")  do
          let mut htmlArgs := #[litDir.toString, htmlDir.toString, "--plan", planFile.toString]
          IO.FS.createDirAll htmlDir
          if ← tomlFile.pathExists then
            htmlArgs := htmlArgs ++ #["--config", tomlFile.toString]
          proc {
            cmd := htmlExeFile.toString
            args := htmlArgs
            env := ← getAugmentedEnv
          }
        pure htmlDir
