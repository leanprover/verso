// Confines its work to the wrappers that belong to this content, so that several releases of a
// script can share one document without reaching each other's markup.
for (const wrapper of document.querySelectorAll(".verso-fixture")) {
    if (wrapper.dataset.versoFixtureReady) continue;
    wrapper.dataset.versoFixtureReady = "true";
    for (const p of wrapper.querySelectorAll(".fixture-intro")) {
        p.dataset.versoFixtureSeen = "true";
    }
}
