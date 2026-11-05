module

public import UsersGuide.Releases.Entry

open Verso.Genre Manual InlineLean UsersGuide.Releases

release_note
  version := ⟨4, 36, 0⟩
  breaking := false
  tag := "feat-blog-subtitle-feature-image"
  prs := [1047]

#doc (Manual) "Subtitle and Feature Image Metadata Fields in Blog" =>

Added optional subtitle and featured image fields in a blog post's metadata.
A featured image is a large image that's given prominent placement for a post.
Blog themes can now showcase these images on the post list in addition to in the post itself.

:::paragraph
These fields are both optional, which means migration of old posts is optional.
The unset fields will simply not be displayed.
If you would like your old posts to be migrated to include a featured image and subtitle, then:

* Add a field `subtitle` to your post's metadata, for example: `subtitle := "an explanation using Lean"`.
* Add a field `featuredImage` with a path to an image to your post's metadata, for example: `featuredImage := "static/post-images/mypicture.png"`.
:::
