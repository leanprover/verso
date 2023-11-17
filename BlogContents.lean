import LeanDoc
import LeanDoc.Genre

import BlogContents.Pages.Front
import BlogContents.Posts.AnExcellentPost
import BlogContents.Posts.AnotherPost

open LeanDoc.Genre
open LeanDoc.Genre.Blog



def blog : Site where
  frontPage := %doc BlogContents.Pages.Front
  contents := .pages #[
    .page "archives" (%doc BlogContents.Pages.Front) <|
      .blog #[
        { date := ⟨2023, 10, 2⟩,
          authors := ["Some Author", "Co Author"],
          content := %doc BlogContents.Posts.AnExcellentPost,
          draft := false
        },
        { date := ⟨2023, 10, 15⟩,
          authors := ["Some Author"],
          content := %doc BlogContents.Posts.AnotherPost,
          draft := false
        }
      ]
  ]
