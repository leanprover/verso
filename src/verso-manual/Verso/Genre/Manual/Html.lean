import Verso.Output.Html



namespace Verso.Genre.Manual.Html
open Verso.Output Html

def titlePage (title : Html) (authors : List String) : Html := {{
  <h1>{{title}}</h1>
  <div class="authors">
    {{authors.toArray.map ({{ <span class="author">{{Coe.coe ·}}</span> }})}}
  </div>
}}

def page (textTitle : String) (contents : Html) : Html := {{
<html>
  <head>
    <title>{{textTitle}}</title>
  </head>
  <body>
    {{contents}}
  </body>
</html>
}}
