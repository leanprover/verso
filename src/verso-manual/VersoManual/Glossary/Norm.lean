module
namespace Verso.Genre.Manual

-- Implements the normalization procedure used in Scribble
public partial def normString (term : String) : String := Id.run do
  let mut str := term.toLower
  if str.endsWith "ies" then
    str := (str.dropEnd 3).copy ++ "y"
  if str.endsWith "s" then
    str := str.dropEnd 1 |>.copy
  str := str.replace "‑" "-"
  String.intercalate " " (str.splitToList (fun c => c.isWhitespace || c == '-') |>.filter (!·.isEmpty))
