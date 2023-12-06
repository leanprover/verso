import BlogContents

open LeanDoc.Genre.Blog

def main (args : List String) : IO UInt32 :=
  blogMain theme blog args
