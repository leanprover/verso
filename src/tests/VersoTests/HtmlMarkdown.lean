/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Errata
import Verso.Output.Html.Markdown

open Verso.Output.Html

/-- info: "<p>Some <em>text</em> and <code>code</code></p>" -/
#test_msgs in
#eval (Markdown.toHtml "Some *text* and `code`").render

/-- info: "<p>a &lt;b&gt; &amp; c</p>" -/
#test_msgs in
#eval (Markdown.toHtml "a &lt;b&gt; &amp; c").render

/-- info: "<p>The sum is <code class=\"math inline\">x_1 + x_2</code>.</p>" -/
#test_msgs in
#eval (Markdown.toHtml (math := true) "The sum is $x_1 + x_2$.").render

/-- info: "<p><code class=\"math display\">\\sum_i x_i</code></p>" -/
#test_msgs in
#eval (Markdown.toHtml (math := true) "$$\\sum_i x_i$$").render

/-- info: "<ul><li>one</li><li>two</li></ul>" -/
#test_msgs in
#eval (Markdown.toHtml "* one\n* two").render

/-- info: "<ul><li><p>one</p></li><li><p>two</p></li></ul>" -/
#test_msgs in
#eval (Markdown.toHtml "* one\n\n* two").render

/-- info: "<ul><li>[x] done</li><li>[ ] todo</li></ul>" -/
#test_msgs in
#eval (Markdown.toHtml "* [x] done\n* [ ] todo").render

/-- info: "<p>~~struck~~</p>" -/
#test_msgs in
#eval (Markdown.toHtml "~~struck~~").render

/-- info: "<p>See <a href=\"https://example.com/a\">https://example.com/a</a>.</p>" -/
#test_msgs in
#eval (Markdown.toHtml "See https://example.com/a.").render

/-- info: "<table><thead><tr><th>a</th><th>b</th></tr></thead><tbody><tr><td>1</td><td>2</td></tr></tbody></table>" -/
#test_msgs in
#eval (Markdown.toHtml "| a | b |\n|---|---|\n| 1 | 2 |").render

/-- info: "<pre><code>def x := 5\n</code></pre>" -/
#test_msgs in
#eval (Markdown.toHtml "```lean\ndef x := 5\n```").render

/-- info: "<p><a href=\"https://example.com\">link</a></p>" -/
#test_msgs in
#eval (Markdown.toHtml "[link](https://example.com)").render

/-- info: "<p><a href=\"../Foo#bar\">link</a></p>" -/
#test_msgs in
#eval (Markdown.toHtml "[link](../Foo#bar)").render

/-- info: "<p><a href=\"https://example.com\" title=\"T\">link</a></p>" -/
#test_msgs in
#eval (Markdown.toHtml "[link](https://example.com \"T\")").render

/-- info: "<p><img src=\"data:image/png;base64,iVBORw0KGgo=\" alt=\"dot\"/></p>" -/
#test_msgs in
#eval (Markdown.toHtml "![dot](data:image/png;base64,iVBORw0KGgo=)").render

/-- info: "<h1>A</h1><h2>B</h2><h2>C</h2>" -/
#test_msgs in
#eval (Markdown.toHtml "# A\n\n#### B\n\n## C").render

/-- info: "<h1>A</h1><h1>B</h1>" -/
#test_msgs in
#eval (Markdown.toHtml "### A\n\n# B").render

/-- info: "<h1>1</h1><h2>2</h2><h3>3</h3><h4>4</h4><h5>5</h5><h6>6</h6>" -/
#test_msgs in
#eval (Markdown.toHtml "# 1\n## 2\n### 3\n#### 4\n##### 5\n###### 6").render

/-- info: "<h1>A</h1><h2>B</h2>" -/
#test_msgs in
#eval (Markdown.toHtml "# A\n\n## B" (topLevel := 0)).render

/-- info: "<h2>1</h2><h3>2</h3><h4>3</h4><h5>4</h5><h6>5</h6><p><strong>6</strong></p>" -/
#test_msgs in
#eval (Markdown.toHtml "# 1\n## 2\n### 3\n#### 4\n##### 5\n###### 6" (topLevel := 2)).render

/-- info: "<h5>A</h5><h6>B</h6><p><strong>C</strong></p>" -/
#test_msgs in
#eval (Markdown.toHtml "# A\n\n## B\n\n### C" (topLevel := 5)).render
