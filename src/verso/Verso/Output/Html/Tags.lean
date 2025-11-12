/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

namespace Verso.Output.Html

/-- Void tags are those that cannot have child nodes - they must not have closing tags.

See https://developer.mozilla.org/en-US/docs/Glossary/Void_element
 -/
public def voidTags : List String :=
  ["area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "param", "source", "track", "wbr"]

/--
Tags for which tag omission rules do not permit omitting the
closing tag (the XHTML-style `<selfclosing/>` syntax is also invalid
here). This list includes all SVG tags, since SVG is XML based and XML requires
that every tag be explicitly closed.

This was manually constructed by grepping through
- https://html.spec.whatwg.org/
- https://www.w3.org/TR/SVG11/eltindex.html
- https://www.w3.org/TR/SVGTiny12/elementTable.html
- https://www.w3.org/TR/SVG2/eltindex.html
-/
public def mustClose : List String :=
  ["b", "u", "mark", "bdi", "bdo", "span", "ins", "del", "picture", "iframe",
   "object", "video", "audio", "map", "table", "form", "label", "button", "select",
   "datalist", "textarea", "output", "progress", "meter", "fieldset", "legend",
   "details", "summary", "dialog", "script", "noscript", "template", "slot",
   "canvas", "title", "style", "article", "section", "nav", "aside", "h1",
   "h2", "h3", "h4", "h5", "h6", "hgroup", "header", "footer", "address", "pre",
   "blockquote", "ol", "ul", "menu", "dl", "figure", "figcaption", "main", "search",
   "div", "a", "em", "strong", "small", "s", "cite", "q", "dfn", "abbr", "ruby",
   "data", "time", "code", "var", "samp", "kbd", "sub", "sup", "i"] ++
  -- SVG tags begin here
  ["altGlyph", "a", "altGlyphDef", "altGlyphItem", "animate", "animateColor",
   "animateMotion", "animateTransform", "circle", "clipPath", "color-profile",
   "cursor", "defs", "desc", "ellipse", "feBlend", "feColorMatrix",
   "feComponentTransfer", "feComposite", "feConvolveMatrix", "feDiffuseLighting",
   "feDisplacementMap", "feDistantLight", "feFlood", "feFuncA", "feFuncB",
   "feFuncG", "feFuncR", "feGaussianBlur", "feImage", "feMerge", "feMergeNode",
   "feMorphology", "feOffset", "fePointLight", "feSpecularLighting", "feSpotLight",
   "feTile", "feTurbulence", "filter", "font", "font-face", "font-face-format",
   "font-face-name", "font-face-src", "font-face-uri", "foreignObject", "g",
   "glyph", "glyphRef", "hkern", "image", "line", "linearGradient", "marker",
   "mask", "metadata", "missing-glyph", "mpath", "path", "pattern", "polygon",
   "polyline", "radialGradient", "rect", "script", "set", "stop", "style", "svg",
   "switch", "symbol", "text", "textPath", "title", "tref", "tspan", "use", "view",
   "vkern", "audio", "canvas", "discard", "feDropShadow", "iframe", "unknown",
   "video"]

/--
  Tags to break the line after without risking weird results
-/
public def newlineAfter : List String := [
  "p", "div", "li", "ul", "ol", "section", "header", "nav", "head", "body",
  "script", "link", "meta", "html"] ++ [1,2,3,4,5,6].map (s!"h{·}")
