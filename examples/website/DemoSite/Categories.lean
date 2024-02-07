import Verso.Genre.Blog

open Verso.Genre.Blog.Post

namespace DemoSite

def examples : Category where
  name := "Examples of Verso usage"
  slug := "examples"

def other : Category where
  name := "Other content"
  slug := "other"
