module

public import UsersGuide.Releases.Entry

open Verso.Genre Manual InlineLean UsersGuide.Releases

release_note
  version := ⟨4, 36, 0⟩
  breaking := false
  tag := "feat-blog-subtitle-feature-image"
  prs := [1047]

#doc (Manual) "Blog new Subtitle and Feature Image metadata fields" =>

Added an optional subtitle and feature image field in a blog's metadata.
This allows users to create a blog theme that show cases feature images and subtitles in their posts list.
