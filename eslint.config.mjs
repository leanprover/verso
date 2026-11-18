import js from "@eslint/js";
import prettier from "eslint-config-prettier";
import compat from "eslint-plugin-compat";
import jsdoc from "eslint-plugin-jsdoc";
import noUnsanitized from "eslint-plugin-no-unsanitized";
import promise from "eslint-plugin-promise";
import * as regexp from "eslint-plugin-regexp";
import globals from "globals";

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
    js.configs.recommended,
    noUnsanitized.configs.recommended,
    promise.configs["flat/recommended"],
    regexp.configs["flat/recommended"],
    jsdoc.configs["flat/recommended-typescript-flavor"],
    compat.configs["flat/recommended"],
    {
        rules: {
            "no-unused-vars": [
                "error",
                {
                    argsIgnorePattern: "^_",
                    caughtErrorsIgnorePattern: "^_",
                },
            ],
            "promise/always-return": ["error", { ignoreLastCallback: true }],
            eqeqeq: ["error", "smart"],
            "prefer-const": "error",
            "no-var": "error",
            "no-shadow": "error",
            "no-implied-eval": "error",
            "no-new-func": "error",
            "no-script-url": "error",
            // TypeScript checks the types, so the JSDoc only needs to be well-formed where it
            // exists.
            "jsdoc/require-jsdoc": "off",
            "jsdoc/require-param-description": "off",
            "jsdoc/require-returns": "off",
            "jsdoc/require-returns-description": "off",
            "jsdoc/reject-any-type": "off",
            "jsdoc/multiline-blocks": "off",
            "jsdoc/tag-lines": "off",
        },
    },
    prettier,
];
