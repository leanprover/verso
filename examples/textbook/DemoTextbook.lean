import Verso.Genre.Manual
import DemoTextbook.Exts.Index

open Verso.Genre Manual
open DemoTextbook.Exts (index theIndex)

set_option pp.rawOnError true

#doc (Manual) "A Textbook" =>

%%%
authors := ["David Thrane Christiansen"]
%%%

{index}[example]
Here's an example project showing how to build a certain kind of textbook with Verso.

# Using an Index

The index should contain an entry for “lorem ipsum”.
{index}[lorem ipsum] foo
{index subterm:="of lorem"}[ipsum]
{index subterm:="per se"}[ipsum]
{index}[ipsum]
Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum.

This is done using the `{index}[entry]` syntax.

# Index
%%%
number := false
%%%

{theIndex}
