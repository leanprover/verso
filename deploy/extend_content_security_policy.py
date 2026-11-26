import argparse
import base64
import hashlib
import re
from pathlib import Path

# Verso's HTML printer emits the policy in exactly this form.
POLICY_META = re.compile(
    r'(<meta http-equiv="Content-Security-Policy" content=")([^"]*)("/>)'
)
FORBIDDEN_IN_ORIGIN = re.compile(r"[\s;,'\"]")


def origin(text):
    if not text or FORBIDDEN_IN_ORIGIN.search(text):
        raise ValueError(f"invalid origin: {text!r}")
    return text


def script_hash(body):
    body = body.replace("\r\n", "\n").replace("\r", "\n").replace("\0", "\ufffd")
    digest = hashlib.sha256(body.encode("utf-8")).digest()
    return f"'sha256-{base64.b64encode(digest).decode('ascii')}'"


def is_hash(token):
    return token.startswith(("'sha256-", "'sha384-", "'sha512-"))


def extend_script_source(tokens, hashes, origins):
    new_origins = [o for o in dict.fromkeys(origins) if o not in tokens]
    new_hashes = [h for h in dict.fromkeys(hashes) if h not in tokens]
    last_source = max(i for i, token in enumerate(tokens) if not is_hash(token))
    position = last_source + 1
    return tokens[:position] + new_origins + tokens[position:] + new_hashes


def extend_policy(html, scripts=(), origins=()):
    origins = [origin(o) for o in origins]
    hashes = [script_hash(body) for body in scripts]
    match = POLICY_META.search(html)
    if match is None:
        return html
    directives = match.group(2).split(";")
    for index, directive in enumerate(directives):
        tokens = directive.split()
        if tokens[:1] != ["script-src"]:
            continue
        extended = extend_script_source(tokens, hashes, origins)
        if extended == tokens:
            return html
        stripped = directive.strip()
        start = directive.index(stripped)
        directives[index] = (
            directive[:start] + " ".join(extended) + directive[start + len(stripped) :]
        )
        content = ";".join(directives)
        return html[: match.start(2)] + content + html[match.end(2) :]
    raise ValueError("the Content Security Policy has no script-src directive")


def html_files(paths):
    for path in paths:
        if path.is_dir():
            yield from sorted(path.rglob("*.html"))
        else:
            yield path


def main(argv=None):
    parser = argparse.ArgumentParser(
        description="Allow trusted scripts and origins in the script-src directive "
        "of the Content Security Policy of Verso-generated HTML pages."
    )
    parser.add_argument(
        "--script",
        action="append",
        default=[],
        type=Path,
        help="a file whose exact contents are an inline script body to allow",
    )
    parser.add_argument(
        "--origin", action="append", default=[], type=origin, help="an origin to allow"
    )
    parser.add_argument("paths", nargs="+", type=Path, metavar="PATH")
    args = parser.parse_args(argv)
    scripts = [path.read_bytes().decode("utf-8") for path in args.script]
    for path in html_files(args.paths):
        html = path.read_bytes().decode("utf-8")
        extended = extend_policy(html, scripts, args.origin)
        if extended != html:
            path.write_bytes(extended.encode("utf-8"))
            print(f"extended {path}")


# Run from deploy/ with:
#   python3 -c "import extend_content_security_policy as m; m.test()"
def test():
    def expected(text):
        digest = hashlib.sha256(text.encode("utf-8")).digest()
        return f"'sha256-{base64.b64encode(digest).decode('ascii')}'"

    old = "'self' https://cdn.example 'sha256-zagrBsqmUpNTNqf2zXEe6chvc+8vg1v2GKWMvG30r34='"
    meta = '<meta http-equiv="Content-Security-Policy" content="script-src {}; base-uri \'self\'"/>'
    page = f"<html>\r\n<head>{meta.format(old)}</head><body></body></html>\n"
    new = old.replace(" '", " https://a.example '") + " " + expected("x()")
    once = extend_policy(page, ["x()"], ["https://a.example"])
    assert once == page.replace(meta.format(old), meta.format(new)), once
    assert extend_policy(once, ["x()"], ["https://a.example"]) == once
    assert extend_policy(page, [], ["https://cdn.example"]) == page
    plain = "<html><head></head><body></body></html>"
    assert extend_policy(plain, ["x()"], ["https://a.example"]) == plain
    for body, normalized in [("a\r\nb\rc", "a\nb\nc"), ("a\0b", "a\ufffdb")]:
        assert script_hash(body) == expected(normalized), body
    for bad in ["a b", "a;", "a,b", "'self'", '"a"', ""]:
        try:
            extend_policy(page, origins=[bad])
        except ValueError:
            continue
        raise AssertionError(f"accepted invalid origin {bad!r}")
    try:
        extend_policy(page.replace("script-src", "style-src"), ["x()"])
    except ValueError:
        return
    raise AssertionError("accepted a policy without script-src")


if __name__ == "__main__":
    main()
