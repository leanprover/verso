import js from "@eslint/js";
import prettier from "eslint-config-prettier";
import compat from "eslint-plugin-compat";
import jsdoc from "eslint-plugin-jsdoc";
import noUnsanitized from "eslint-plugin-no-unsanitized";
import promise from "eslint-plugin-promise";
import * as regexp from "eslint-plugin-regexp";

/**
 * Standard presets and rules for Verso-related repositories to be included in
 * repository-specific files.
 */
export default [
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
            "array-callback-return": "error",
            "no-self-compare": "error",
            "no-template-curly-in-string": "error",
            "no-unmodified-loop-condition": "error",
            "no-unreachable-loop": "error",
            "no-constructor-return": "error",
            "no-throw-literal": "error",
            "prefer-promise-reject-errors": "error",
            "no-return-assign": "error",
            "no-sequences": "error",
            "no-extend-native": "error",
            "no-proto": "error",
            "no-caller": "error",
            "no-new-wrappers": "error",
            "prefer-template": "error",
            "prefer-arrow-callback": "error",
            "no-else-return": "error",
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
