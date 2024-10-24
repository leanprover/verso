let params = new URLSearchParams(document.location.search);
let domains = params.getAll("domain");
let name = params.get("name");
console.log("Domains: " + domains);
console.log("name: " + name);
if(name) {
    let options = [];
    if (domains && domains.length > 0) {
        for (const i in domains) {
            let domain = domains[i];
            console.log('Considering domain ' + domain);
            if (xref.hasOwnProperty(domain)) {
                console.log('Found domain ' + domain);
                let opts = xref[domain];
                if (opts['contents'].hasOwnProperty(name)) {
                    options = opts['contents'][name].map(x => Object.assign(x, {'domain': domain}));
                }
            }
        }
    } else {
        for (const [dom, opts] of Object.entries(xref)) {
            if (opts['contents'].hasOwnProperty(name)) {
                for (const i of opts['contents'][name]) {
                    options.push(Object.assign(i, {'domain': dom}));
                }
            }
        }
    }

    if (options.length == 0) {
        addEventListener('DOMContentLoaded', event => {
            document.title = "Not found: '" + name + "'";
            document.querySelector("#title").innerHTML = "Not found: name '" + name + "'";
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
            document.title = "Ambiguous: '" + name + "'";
            document.querySelector("#title").innerHTML = "Ambiguous: name '" + name + "'";
            document.querySelector("#message").innerHTML = "<p>Options:</p><ul>" +
                options.map((x, idx) => '<li><p><a href="' + x['address'] + '#' + x['id'] + '">From ' + xref[x['domain']]['title'] + '</a></p></li>').join('\n') +
                "</ul>";
        });
    }
} else {
    addEventListener('DOMContentLoaded', event => {
        document.title = "No name provided";
        document.querySelector("#title").innerHTML = "No name provided";
        document.querySelector("#message").innerHTML = "<p>This page expects a 'name' query parameter, along with documentation domains.</p>";
    });
}
