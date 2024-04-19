import Verso.Genre.Manual

import UsersGuide

open Verso.Genre.Manual

-- TODO: metaprogram this away
def impls := ExtensionImpls.fromLists [] [(``Block.paragraph, paragraph.descr), (``Block.docstring, docstring.descr)]

def main := manualMain impls (%doc UsersGuide.Basic)
