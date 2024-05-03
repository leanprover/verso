import Verso.Genre.Manual

import DemoTextbook

open Verso.Genre.Manual

-- TODO: metaprogram this away
def impls := ExtensionImpls.fromLists
  [(``DemoTextbook.Exts.index, DemoTextbook.Exts.index.descr)]
  [(``Block.paragraph, paragraph.descr), (``Block.docstring, docstring.descr), (``DemoTextbook.Exts.theIndex, DemoTextbook.Exts.theIndex.descr)]

def main := manualMain impls (%doc DemoTextbook)
