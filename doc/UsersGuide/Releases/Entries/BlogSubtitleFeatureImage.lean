module

public import UsersGuide.Releases.Entry

open Verso.Genre Manual InlineLean UsersGuide.Releases

release_note
  version := ⟨4, 36, 0⟩
  breaking := false
  tag := "feat-blog-subtitle-feature-image"
  prs := [1047]

#doc (Manual) "Subtitle and Feature Image Metadata Fields in Blog" =>

Added optional subtitle and feature image fields in a blog post's metadata.
A feature image is a large image that's given prominent placement for a post.
Blog themes can now showcase these images on the post list in addition to in the post itself.
