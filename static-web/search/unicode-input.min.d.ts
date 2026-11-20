// Declarations for the part of the vendored `unicode-input.min.js` that the search bar uses. The
// types follow those of the `@leanprover/unicode-input` package.

/** An offset-based range of characters in a text. */
export declare class Range {
    readonly offset: number;
    readonly length: number;
    constructor(offset: number, length: number);
}
