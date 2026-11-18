(function () {
    const {
        protocol: proto,
        host: hostName,
        pathname: path,
        search: srch,
        hash: hsh,
    } = window.location;
    if (!(path.endsWith("/") || path.endsWith(".html"))) {
        window.location.replace(`${proto}//${hostName}${path}/${srch}${hsh}`);
    }
})();
