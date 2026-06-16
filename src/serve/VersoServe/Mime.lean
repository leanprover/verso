/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace VersoServe

/--
A MIME type, split into its top-level type and subtype, as in {lit}`text` and {lit}`html` for
{lit}`text/html`.
-/
structure MimeType where
  /-- The top-level type, such as {lit}`text` or {lit}`image`. -/
  type : String
  /-- The subtype, such as {lit}`html` or {lit}`png`. -/
  subtype : String
deriving Repr, BEq, Inhabited

namespace MimeType

/-- Whether the type names textual content that should carry `; charset=utf-8`. -/
def isTextual (mime : MimeType) : Bool :=
  mime.type == "text" ||
    mime == ⟨"application", "json"⟩ ||
    mime == ⟨"application", "xml"⟩ ||
    mime == ⟨"image", "svg+xml"⟩

/--
The {lit}`Content-Type` header value, including `; charset=utf-8` for textual types.
-/
def contentType (mime : MimeType) : String :=
  let base := s!"{mime.type}/{mime.subtype}"
  if mime.isTextual then base ++ "; charset=utf-8" else base

end MimeType

/--
The MIME type for a file extension {name}`ext`, or {name}`none` when the extension is unknown.

The extension is given without a leading dot and matched case-insensitively.
-/
def mimeType? (ext : String) : Option MimeType :=
  match ext.toLower with
  | "html" | "htm" => some ⟨"text", "html"⟩
  | "css" => some ⟨"text", "css"⟩
  | "js" | "mjs" => some ⟨"text", "javascript"⟩
  | "json" | "map" => some ⟨"application", "json"⟩
  | "svg" => some ⟨"image", "svg+xml"⟩
  | "xml" => some ⟨"application", "xml"⟩
  | "txt" => some ⟨"text", "plain"⟩
  | "md" => some ⟨"text", "markdown"⟩
  | "csv" => some ⟨"text", "csv"⟩
  | "png" => some ⟨"image", "png"⟩
  | "jpg" | "jpeg" => some ⟨"image", "jpeg"⟩
  | "gif" => some ⟨"image", "gif"⟩
  | "webp" => some ⟨"image", "webp"⟩
  | "avif" => some ⟨"image", "avif"⟩
  | "ico" => some ⟨"image", "x-icon"⟩
  | "woff" => some ⟨"font", "woff"⟩
  | "woff2" => some ⟨"font", "woff2"⟩
  | "ttf" => some ⟨"font", "ttf"⟩
  | "otf" => some ⟨"font", "otf"⟩
  | "eot" => some ⟨"application", "vnd.ms-fontobject"⟩
  | "wasm" => some ⟨"application", "wasm"⟩
  | "pdf" => some ⟨"application", "pdf"⟩
  | "zip" => some ⟨"application", "zip"⟩
  | "gz" | "tgz" => some ⟨"application", "gzip"⟩
  | "bz2" | "tbz2" => some ⟨"application", "x-bzip2"⟩
  | "bz" => some ⟨"application", "x-bzip"⟩
  | "xz" | "txz" => some ⟨"application", "x-xz"⟩
  | "zst" => some ⟨"application", "zstd"⟩
  | "br" => some ⟨"application", "x-brotli"⟩
  | "lz" => some ⟨"application", "x-lzip"⟩
  | "lzma" => some ⟨"application", "x-lzma"⟩
  | "z" => some ⟨"application", "x-compress"⟩
  | "tar" => some ⟨"application", "x-tar"⟩
  | "7z" => some ⟨"application", "x-7z-compressed"⟩
  | "rar" => some ⟨"application", "vnd.rar"⟩
  | "mp4" => some ⟨"video", "mp4"⟩
  | "webm" => some ⟨"video", "webm"⟩
  | "mp3" => some ⟨"audio", "mpeg"⟩
  | "ogg" => some ⟨"audio", "ogg"⟩
  | "wav" => some ⟨"audio", "wav"⟩
  | _ => none

/--
The {lit}`Content-Type` header value for a file, including `; charset=utf-8` for textual types.

Files whose extension is unknown are served as {lit}`application/octet-stream`.
-/
def contentTypeForPath (path : System.FilePath) : String :=
  path.extension.bind mimeType?
    |>.map MimeType.contentType
    |>.getD "application/octet-stream"
