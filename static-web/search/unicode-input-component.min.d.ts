// Declarations for the part of the vendored `unicode-input-component.min.js` that the search bar
// uses. The types follow those of the `@leanprover/unicode-input-component` package.

import { Range } from "./unicode-input.min.js";

/** The settings of the abbreviation input. */
export interface AbbreviationConfig {
    abbreviationCharacter: string;
    customTranslations: Record<string, string>;
    eagerReplacementEnabled: boolean;
}

/** Replaces abbreviations such as `\alpha` with Unicode characters as the user types. */
export declare class InputAbbreviationRewriter {
    constructor(config: AbbreviationConfig, textInput: HTMLElement);
    resetAbbreviations(): void;
    setSelections(selections: Range[]): void;
}
