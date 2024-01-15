import Verso.Genre.Blog
open Verso Genre Blog

#doc (Post) "Conditional Expressions in Lean" =>

%%%
authors := ["Fictional Author"]
date := {year := 2024, month := 1, day := 15}
%%%

Finally started blogging!
This post describes the syntax and semantics of conditional expressions in Lean.
Here are some examples:

```leanInit demo
-- This block initializes a Lean context
```


```lean demo
example := if true then 1 else 2
example := if True then 1 else 2
example : Int := if True then 1 else 2
```
