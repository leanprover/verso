# URL parser test cases from web-platform-tests

`urltestdata.json` is a subset of `url/resources/urltestdata.json`
from the
[web-platform-tests](https://github.com/web-platform-tests/wpt)
project at commit `128807aaf4ab2c1d63897214f173bf771ed4c990`:
https://github.com/web-platform-tests/wpt/blob/128807aaf4ab2c1d63897214f173bf771ed4c990/url/resources/urltestdata.json

The file is distributed under the 3-Clause BSD License in
`LICENSE.md`.

The subset keeps every test case (the JSON objects, without the
comment strings) that satisfies at least one of these conditions:

- The expected result has the protocol `http:` or `https:`.
- The case is an expected failure (`"failure": true`).
- The input starts with `//`, `\\`, or a scheme followed by `:`.

The entries are otherwise unchanged. To regenerate the subset from a
downloaded `urltestdata.json`, run this command in this directory:

```
python3 -I -c 'import json,re,sys; d=json.load(open(sys.argv[1],encoding="utf-8")); json.dump([c for c in d if isinstance(c,dict) and (c.get("failure") or c.get("protocol") in ("http:","https:") or re.match(r"(//|\\\\|[A-Za-z][A-Za-z0-9+.-]*:)",c["input"]))],open("urltestdata.json","w",encoding="utf-8"),ensure_ascii=False,indent=2)' PATH/TO/urltestdata.json
```
