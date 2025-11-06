/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

module
public import VersoManual.LicenseInfo

/-!
This module contains information about all the open-source licenses that are used as part of the
HTML versions of Lean documentation.
-/


namespace Verso.Genre.Manual.Licenses

public def popper.js : LicenseInfo where
  identifier := "MIT"
  dependency := "Popper.js"
  howUsed := some "Popper.js is used (as a dependency of Tippy.js) to show information (primarily in Lean code) when hovering the mouse over an item of interest."
  link := some "https://popper.js.org/docs/v2/"
  text := #[
  (some "The MIT License",
r#"
Copyright (c) 2019 Federico Zivolo

Permission is hereby granted, free of charge, to any person obtaining a copy of
this software and associated documentation files (the "Software"), to deal in
the Software without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Software, and to permit persons to whom the Software is furnished to do so,
subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
"#)]

public def tippy.js : LicenseInfo where
  identifier := "MIT"
  dependency := "Tippy.js"
  howUsed := some "Tippy.js is used together with Popper.js to show information (primarily in Lean code) when hovering the mouse over an item of interest."
  link := some "https://atomiks.github.io/tippyjs/"
  text := #[
  (some "The MIT License",
r#"
Copyright (c) 2017-present atomiks

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

"#)]

public def KaTeX : LicenseInfo where
  identifier := "MIT"
  dependency := "KaTeX"
  howUsed := "KaTeX is used to render mathematical notation."
  link := "https://katex.org/"
  text := #[(some "The MIT License", text)]
where
  text := r#"
Copyright (c) 2013-2020 Khan Academy and other contributors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
"#

public def elasticlunr.js : LicenseInfo where
  identifier := "MIT"
  dependency := "elasticlunr.js"
  howUsed := "Elasticlunr.js is used for full-text search"
  link := "http://elasticlunr.com/"
  text := #[(some "The MIT License", text)]
where
  text := r#"
Copyright (C) 2017 by Wei Song

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
"#

public def fuzzysort : LicenseInfo where
  identifier := "MIT"
  dependency := "fuzzysort v3.1.0"
  howUsed := "The fuzzysort library is used in the search box to quickly filter results."
  link := "https://github.com/farzher/fuzzysort"
  text := #[(some "The MIT License", text)]
where
  text := r#"
Copyright (c) 2018 Stephen Kamenar

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
"#

public def w3Combobox : LicenseInfo where
  identifier := "W3C-20150513"
  dependency := "Editable Combobox With Both List and Inline Autocomplete Example, from the W3C's ARIA Authoring Practices Guide (APG)"
  howUsed := "The search box component includes code derived from the example code in the linked article from the W3C's ARIA Authoring Practices Guide (APG)."
  link := "https://www.w3.org/WAI/ARIA/apg/patterns/combobox/examples/combobox-autocomplete-both/"
  text := #[(some "Software and Document License - 2023 Version", text)]
where
  text := r#"Permission to copy, modify, and distribute this work, with or without
modification, for any purpose and without fee or royalty is hereby granted,
provided that you include the following on ALL copies of the work or portions
thereof, including modifications:

 * The full text of this NOTICE in a location viewable to users of the redistributed or derivative work.

 * Any pre-existing intellectual property disclaimers, notices, or terms and conditions. If none exist, the W3C software and document short notice should be included.

 * Notice of any changes or modifications, through a copyright statement on the new code or document such as "This software or document includes material copied from or derived from "Editable Combobox With Both List and Inline Autocomplete Example" at https://www.w3.org/WAI/ARIA/apg/patterns/combobox/examples/combobox-autocomplete-both/. Copyright © 2024 World Wide Web Consortium. https://www.w3.org/copyright/software-license-2023/"

"#
