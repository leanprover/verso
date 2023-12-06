import LeanDoc.Genre.Blog

open LeanDoc.Genre (Blog)
open LeanDoc.Genre.Blog (page_link htmlSpan htmlDiv blob)
open LeanDoc Output Html

set_option pp.rawOnError true

def teamData : Array (String × Html × String × String):= #[
  ("/static/team/leo.jpg",
   {{ <a href="https://leodemoura.github.io/about">"Leo de Moura"</a>" (AWS)" }},
   "Leo de Moura",
   "Chief Architect, Co-Founder"),
  ("/static/team/sebastian.jpg",
   "Sebastian Ullrich",
   "Sebastian Ullrich",
   "Head of Engineering, Co-Founder"),
  ("/static/team/joachim.jpg",
   "Joachim Breitner",
   "Joachim Breitner",
   "Senior Research Software Engineer"),
  ("/static/team/david.jpg",
   "David Thrane Christiansen",
   "David Thrane Christiansen",
   "Senior Research Software Engineer"),
  ("/static/team/joe.jpg",
   "Joe Hendrix",
   "Joe Hendrix",
   "Principal Research Software Engineer"),
  ("/static/team/marc.jpg",
   "Marc Huisinga",
   "Marc Huisinga",
   "Research Software Engineer"),
  ("/static/team/mac.jpg",
   "Mac Malone",
   "Mac Malone",
   "Research Software Engineer"),
  ("/static/team/kyle.jpg",
   "Kyle Miller",
   "Kyle Miller",
   "Research Software Engineer (Part-Time)"),
  ("/static/team/scott.jpg",
   "Scott Morrison",
   "Scott Morrison",
   "Senior Research Software Engineer")
]

def team : Html := {{
  <div>
  {{ teamData.map fun (pic, name, alt, role) =>
    {{<div class="person">
        <img src={{pic}} alt={{alt}}/>
        <div class="name">{{name}}</div>
        <div class="role">{{role}}</div>
      </div>
    }}
  }}
  </div>
}}

#doc (Blog) "Team" =>

# People

::: blob team
:::

# Board of Directors


* [Adam Marblestone](https://www.convergentresearch.org/adam-marblestone) (Convergent Research)
* [Leo de Moura](https://leodemoura.github.io/about) (Amazon Web Services)
* [Jeremy Avigad](http://www.andrew.cmu.edu/user/avigad) (Carnegie Mellon University)
