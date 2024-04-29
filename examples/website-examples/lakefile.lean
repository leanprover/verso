import Lake
open Lake DSL

require subverso from git "https://github.com/leanprover/subverso.git"@"issue/17"

package «examples» where
  -- add package configuration options here

@[default_target]
lean_lib «Examples» where
  -- add library configuration options here
