let params = new URLSearchParams(document.location.search);
let domains = params.getAll("domain");
let target = params.get("target");
console.log("Domains: " + domains);
console.log("target: " + target);
if(target) {
    let options = [];
    if (domains && domains.length > 0) {
        for (const i in domains) {
            let domain = domains[i];
            console.log('Considering domain ' + domain);
            if (xref.hasOwnProperty(domain)) {
                console.log('Found domain ' + domain);
                let opts = xref[domain];
                if (opts['contents'].hasOwnProperty(target)) {
                    options = opts['contents'][target].map(x => Object.assign(x, {'domain': domain}));
                }
            }
        }
    } else {
        for (const [dom, opts] of Object.entries(xref)) {
            if (opts['contents'].hasOwnProperty(target)) {
                for (const i of opts['contents'][target]) {
                    options.push(Object.assign(i, {'domain': dom}));
                }
            }
        }
    }

    if (options.length == 0) {
        addEventListener('DOMContentLoaded', event => {
            document.title = "Not found: '" + target + "'";
            document.querySelector("#title").innerHTML = "Not found: target '" + target + "'";
            let allDomains = [];
            for (const d in xref) {
                allDomains.push(d);
            }
            if (domains.length < 1) {
                domains = allDomains;
            }
            document.querySelector("#message").innerHTML = "<p>Searched domains:</p>" + "<ul>" + domains.map(x => "<li><code>" + x + "</code>: " + xref[x]['title'] + "</li>\n").join('') + "</ul>";
        });
    } else if (options.length == 1) {
        let addr = options[0]['address'] + "#" + options[0]['id'];
        window.location.replace(addr);
    } else {
        addEventListener('DOMContentLoaded', event => {
            document.title = "Ambiguous: '" + target + "'";
            document.querySelector("#title").innerHTML = "Ambiguous: target '" + target + "'";
            document.querySelector("#message").innerHTML = "<p>Options:</p><ul>" +
                options.map((x, idx) => '<li><p><a href="' + x['address'] + '#' + x['id'] + '">From ' + xref[x['domain']]['title'] + '</a></p></li>').join('\n') +
                "</ul>";
        });
    }
} else {
    addEventListener('DOMContentLoaded', event => {
        document.title = "No target provided";
        document.querySelector("#title").innerHTML = "No target provided";
        document.querySelector("#message").innerHTML = "<p>This script expects a 'target' query parameter, along with documentation domains.</p>";
    });
}
