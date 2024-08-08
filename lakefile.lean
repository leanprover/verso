import Lake
open Lake DSL

require subverso from git "https://github.com/leanprover/subverso.git"@"main"
require MD4Lean from git "https://github.com/david-christiansen/md4lean"@"parser"

package verso where
  precompileModules := true
  -- add package configuration options here

@[default_target]
lean_lib Verso where
  srcDir := "src/verso"
  roots := #[`Verso]
  -- add library configuration options here

@[default_target]
lean_lib VersoBlog where
  srcDir := "src/verso-blog"
  roots := #[`Verso.Genre.Blog]
