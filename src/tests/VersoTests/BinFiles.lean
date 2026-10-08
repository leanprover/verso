/-
Copyright (c) 2026 Jiayi Fan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jiayi Fan
-/

import Errata
import VersoUtil.BinFiles

/-! Tests for `include_bin_dir` -/

-- The names are the given path followed by `/`-separated names, whatever the build host's separator
/--
info: #["../integration/extra-files-doc/test-data/TeX-only/TeX-specific.sty",
  "../integration/extra-files-doc/test-data/html-only/html-specific.css",
  "../integration/extra-files-doc/test-data/shared/shared-file.txt"]
-/
#test_msgs in
#eval (include_bin_dir "../integration/extra-files-doc/test-data").map (·.1) |>.qsort (· < ·)
