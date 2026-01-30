import Verso
import VersoManual

open Verso.Genre Manual

#doc (Manual) "Test for Infoview over Inline Math" =>

$`\sum_i x_i \cdot y_i = \sum_i y_i \cdot x_i`
    --^ $/lean/plainGoal

$$`\sum_i x_i + y_i = \sum_i y_i + x_i`
    --^ $/lean/plainGoal
