/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Errata
import VersoManual.LicenseInfo.Include

/-! Tests for `include_license` -/

/--
info: { header? := some "Example License", text := "Permission is granted.\nSecond line.\n" }
-/
#test_msgs in
#eval include_license "IncludeLicense/ok.txt"

/--
error: invalid license file 'IncludeLicense/no-blank.txt': expected a header line, a blank line, and the license text
-/
#test_msgs in
#eval include_license "IncludeLicense/no-blank.txt"

/--
info: { header? := some "Example License", text := "Permission is granted.\n" }
-/
#test_msgs in
#eval include_license "IncludeLicense/leading-blank.txt"

/--
error: invalid license file 'IncludeLicense/only-blank.txt': expected a header line, a blank line, and the license text
-/
#test_msgs in
#eval include_license "IncludeLicense/only-blank.txt"

/--
error: invalid license file 'IncludeLicense/no-body.txt': the license text is empty
-/
#test_msgs in
#eval include_license "IncludeLicense/no-body.txt"
