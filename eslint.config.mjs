import globals from "globals";
import shared from "./eslint.shared.mjs";

export default [
    {
        ignores: ["**/*.min.js", "vendored-js/", "node_modules/", ".lake/", "_out/", "**/.lake/"],
    },
    {
        files: ["static-web/**/*.js"],
        languageOptions: {
            ecmaVersion: 2024,
            sourceType: "script",
            globals: { ...globals.browser },
        },
    },
    {
        files: ["static-web/highlighted-code.js"],
        languageOptions: {
            globals: { tippy: "readonly", versoRenderMath: "readonly" },
        },
    },
    {
        files: ["static-web/search/search-*.js"],
        ignores: ["static-web/search/search-highlight.js"],
        languageOptions: { sourceType: "module" },
    },
    ...shared,
];
