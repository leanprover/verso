#!/usr/bin/env bash
#
# Copies a generated site under a URL prefix, rejects the URLs that break there, and link-checks the
# copy.
#
# A site is served from wherever its root is mounted, so every URL that Verso emits is relative to
# the document rather than to the origin. A URL that begins with a single slash addresses the origin
# instead, so it breaks as soon as the site is served under a prefix. Content may hold one on
# purpose, which is what `--allow` is for.
#
# usage: scripts/check-url-prefix.sh <site-directory> [--allow <regex>]

set -euo pipefail

usage() {
    echo "usage: $0 <site-directory> [--allow <regex>]" >&2
    exit 2
}

site=""
allow=""
while [ $# -gt 0 ]; do
    case "$1" in
        --allow)
            [ $# -ge 2 ] || usage
            allow="$2"
            shift 2
            ;;
        -*) usage ;;
        *)
            [ -z "$site" ] || usage
            site="$1"
            shift
            ;;
    esac
done

[ -n "$site" ] || usage
[ -d "$site" ] || {
    echo "No such directory: $site" >&2
    exit 2
}

prefix="a/url/prefix"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/$prefix"
cp -R "$site/." "$work/$prefix/"

# The attributes are the ones that `Verso.Output.Html.rewriteUrls` rewrites. An attribute name is
# taken whole, so `metadata` is not read as `data`. A candidate list is checked at its first URL,
# which is where a root-relative one in emitted content appears.
#
# A protocol-relative URL begins with two slashes and is left alone.
attrs='href|src|data|poster|action|formaction|cite|ping|srcset|imagesrcset'
pattern="(^|[[:space:]])($attrs)=\"/([^/\"]|\")|url\\([\"']?/[^/]"

rc=0
hits="$(grep -REon --include='*.html' --include='*.css' "$pattern" "$work/$prefix")" || rc=$?
if [ "$rc" -gt 1 ]; then
    echo "Failed to scan '$site' for root-relative URLs." >&2
    exit 2
fi
if [ -n "$allow" ] && [ -n "$hits" ]; then
    rc=0
    hits="$(printf '%s\n' "$hits" | grep -Ev "$allow")" || rc=$?
    if [ "$rc" -gt 1 ]; then
        echo "Failed to apply --allow to the scan of '$site'." >&2
        exit 2
    fi
fi

if [ -n "$hits" ]; then
    echo "Root-relative URLs in '$site' break when the site is served under a URL prefix:" >&2
    printf '%s\n' "$hits" | sed "s|^$work/$prefix/||" >&2
    exit 1
fi

if command -v linkchecker >/dev/null 2>&1; then
    linkchecker --config=.linkchecker/linkcheckerrc --no-status "$work/$prefix/"
else
    echo "linkchecker is not installed, so only the URL check ran." >&2
fi

echo "'$site' works under a URL prefix."
