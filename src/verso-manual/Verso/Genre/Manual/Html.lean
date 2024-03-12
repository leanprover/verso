import Verso.Output.Html

namespace Verso.Genre.Manual.Html
open Verso.Output Html

def titlePage (title : Html) (authors : List String) (intro : Html) : Html := {{
  <div class="titlepage">
    <h1>{{title}}</h1>
    <div class="authors">
      {{authors.toArray.map ({{ <span class="author">{{Coe.coe ·}}</span> }})}}
    </div>
    {{intro}}
  </div>
}}

def page (textTitle : String) (contents : Html) : Html := {{
<html>
  <head>
    <title>{{textTitle}}</title>
    <link rel="stylesheet" href="book.css" />
  </head>
  <body>
    <div class="with-toc">
      <header>
        <h1>{{textTitle}}</h1>
        <div id="controls">
          <label for="toggle-toc" id="toggle-toc-click">"TOC"</label>
        </div>
        <div id="print">
          <span>"🖨"</span>
        </div>
      </header>
      <nav id="toc">
        <input type="checkbox" id="toggle-toc"/>
        <ol>
          <li class="unnumbered">"Title page"</li>
          <li>
            <a href="#introduction">"Introduction"</a>
            <ol>
              <li>"About this Document"</li>
            </ol>
          </li>
          <li>
            "Basic Concepts"
            <ol>
              <li>"One Concept"</li>
              <li>"Another Concept"</li>
            </ol>
          </li>
          <li class="unnumbered">"Conclusion"</li>
        </ol>
      </nav>
      <main>
        {{contents}}
      </main>
    </div>
  </body>
</html>
}}
