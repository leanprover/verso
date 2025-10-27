import Verso
import VersoManual
import SubVerso.Highlighting

namespace Verso.RobTest
open Genre Manual InlineLean

set_option trace.compiler.ir.result true

def code := 4
def blocks := 6

#doc (Manual) "My title here" =>

Use {lean}`code` {lean}`blocks`
Use {lean}`code` {lean}`blocks`
Use {lean}`code` {lean}`blocks`

Use {lean}`code` {lean}`blocks`
Use {lean}`code` {lean}`blocks`
Use {lean}`code` {lean}`blocks`
