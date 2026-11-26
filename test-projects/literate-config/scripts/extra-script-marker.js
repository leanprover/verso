// An extra script file from `extra_js` in `literate.toml`. It is served from the site's own origin,
// so it runs under the content security policy's 'self' source. The browser tests read this marker
// to check that the script ran.
window.literateExtraScriptMarker = true;
