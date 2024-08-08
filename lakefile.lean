import Lake
open Lake DSL

require subverso from git "https://github.com/leanprover/subverso.git"@"main"
require MD4Lean from git "https://github.com/david-christiansen/md4lean"@"parser"

package verso where

  -- add package configuration options here

@[default_target]
lean_lib VersoA where
  srcDir := "src/verso"
  roots := #[`Verso.A]

@[default_target]
lean_lib VersoBlog where
  srcDir := "src/verso-blog"
  roots := #[`Verso.Genre.Blog]
