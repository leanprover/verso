import Lake
open Lake DSL

package verso where

  -- add package configuration options here

@[default_target]
lean_lib Verso where
  srcDir := "src/verso"
  roots := #[`Verso]

@[default_target]
lean_lib VersoBlog where
  srcDir := "src/verso-blog"
  roots := #[`Verso.Genre.Blog]
