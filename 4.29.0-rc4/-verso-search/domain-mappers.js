

/**
 * @type {DomainMapper}
 */
const Verso_DOT_Genre_DOT_Manual_DOT_doc_DOT_suggestion = {
    dataToSearchables:
      (domainData) =>
          Object.entries(domainData.contents).map(([key, value]) => ({
            searchKey: value[0].data.searchTerm,
            address: `${value[0].address}#${value[0].id}`,
            domainId: 'Verso.Genre.Manual.doc.suggestion',
            ref: value[0].data.suggestedRedirect,
          })),
    className: "suggestion-domain",
    displayName: "Suggestion",
    customRender:
      (searchable, matchedParts, document) => {
          const searchTerm = document.createElement('p');
          for (const { t, v } of matchedParts) {
            if (t === 'text') {
              searchTerm.append(v);
            } else {
              const emEl = document.createElement('em');
              searchTerm.append(emEl);
              emEl.textContent = v;
            }
          }
          searchTerm.append(document.createElement('br'));
          searchTerm.append(`↪ ${searchable.ref}`);
          return searchTerm
        },
    };

/**
 * @type {DomainMapper}
 */
const Verso_DOT_Genre_DOT_Manual_DOT_doc = {
    dataToSearchables:
      (domainData) =>
        Object.entries(domainData.contents).map(([key, value]) => ({
          searchKey: key,
          address: `${value[0].address}#${value[0].id}`,
          domainId: 'Verso.Genre.Manual.doc',
          ref: value,
        })),
    className: "doc-domain",
    displayName: "Documentation",
    };

/**
 * @type {DomainMapper}
 */
const Verso_DOT_Genre_DOT_Manual_DOT_doc_DOT_option = {
    dataToSearchables:
      (domainData) =>
        Object.entries(domainData.contents).map(([key, value]) => ({
          searchKey: key,
          address: `${value[0].address}#${value[0].id}`,
          domainId: 'Verso.Genre.Manual.doc.option',
          ref: value,
        })),
    className: "doc-option-domain",
    displayName: "Compiler Option",
    };

/**
 * @type {DomainMapper}
 */
const Verso_DOT_Genre_DOT_Manual_DOT_doc_DOT_tactic_DOT_conv = {
    dataToSearchables:
      (domainData) =>
        Object.entries(domainData.contents).map(([key, value]) => ({
          searchKey: value[0].data.userName,
          address: `${value[0].address}#${value[0].id}`,
          domainId: 'Verso.Genre.Manual.doc.tactic.conv',
          ref: value,
        })),
    className: "conv-tactic-domain",
    displayName: "Conv Tactic",
    };

/**
 * @type {DomainMapper}
 */
const Verso_DOT_Genre_DOT_Manual_DOT_doc_DOT_tech = {
    dataToSearchables:
      (domainData) =>
        Object.entries(domainData.contents).map(([key, value]) => ({
          searchKey: value[0].data.term,
          address: `${value[0].address}#${value[0].id}`,
          domainId: 'Verso.Genre.Manual.doc.tech',
          ref: value,
        })),
    className: "tech-term-domain",
    displayName: "Terminology",
    };

/**
 * @type {DomainMapper}
 */
const Verso_DOT_Genre_DOT_Manual_DOT_section = {
    dataToSearchables:
      (domainData) =>
          Object.entries(domainData.contents).map(([key, value]) => ({
            searchKey: `${value[0].data.sectionNum} ${value[0].data.title}`,
            address: `${value[0].address}#${value[0].id}`,
            domainId: 'Verso.Genre.Manual.section',
            ref: value,
          })),
    className: "section-domain",
    displayName: "Section",
    };

/**
 * @type {DomainMapper}
 */
const Verso_DOT_Genre_DOT_Manual_DOT_example = {
    dataToSearchables:
      (domainData) => {
        const byName = Object.entries(domainData.contents).flatMap(([key, value]) =>
          value.map(v => ({
            context: v.data[`${v.address}#${v.id}`].context,
            name: v.data[`${v.address}#${v.id}`].display,
            address: `${v.address}#${v.id}`
          }))).reduce((acc, obj) => {
            const key = obj.name;
            if (!acc.hasOwnProperty(key)) acc[key] = [];
            acc[key].push(obj);
            return acc;
          }, {})
        return Object.entries(byName).flatMap(([key, value]) => {
          if (value.length === 0) { return []; }
          const firstCtxt = value[0].context;
          let prefixLength = 0;
          for (let i = 0; i < firstCtxt.length; i++) {
            if (value.every(v => i < v.context.length && v.context[i] === firstCtxt[i])) {
              prefixLength++;
            } else break;
          }
          return value.map((v) => ({
            searchKey: v.context.slice(prefixLength).concat(v.name).join(' › '),
            address: v.address,
            domainId: 'Verso.Genre.Manual.example',
            ref: value
          }));
        });
      },
    className: "example-def",
    displayName: "Example Definition",
    };

/**
 * @type {DomainMapper}
 */
const Verso_DOT_Genre_DOT_Manual_DOT_doc_DOT_tactic = {
    dataToSearchables:
      (domainData) =>
        Object.entries(domainData.contents).map(([key, value]) => ({
          searchKey: value[0].data.userName,
          address: `${value[0].address}#${value[0].id}`,
          domainId: 'Verso.Genre.Manual.doc.tactic',
          ref: value,
        })),
    className: "tactic-domain",
    displayName: "Tactic",
    };

export const domainMappers = {"Verso.Genre.Manual.doc.suggestion":
    Verso_DOT_Genre_DOT_Manual_DOT_doc_DOT_suggestion,
  "Verso.Genre.Manual.doc": Verso_DOT_Genre_DOT_Manual_DOT_doc,
  "Verso.Genre.Manual.doc.option":
    Verso_DOT_Genre_DOT_Manual_DOT_doc_DOT_option,
  "Verso.Genre.Manual.doc.tactic.conv":
    Verso_DOT_Genre_DOT_Manual_DOT_doc_DOT_tactic_DOT_conv,
  "Verso.Genre.Manual.doc.tech":
    Verso_DOT_Genre_DOT_Manual_DOT_doc_DOT_tech,
  "Verso.Genre.Manual.section":
    Verso_DOT_Genre_DOT_Manual_DOT_section,
  "Verso.Genre.Manual.example":
    Verso_DOT_Genre_DOT_Manual_DOT_example,
  "Verso.Genre.Manual.doc.tactic":
    Verso_DOT_Genre_DOT_Manual_DOT_doc_DOT_tactic
};