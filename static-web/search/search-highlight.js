
/**
 * @typedef {{ref: string, score: number, doc: {id: string, header: string, context: string, contents: string}}} TextMatch
 * @typedef {{run: (tokens: string[]) => string[]}} ElasticLunrPipeline
 * @typedef {{bool?: "AND"|"OR", fields?:Record<string, {boost?: number}>}} SearchConfig
 * @typedef {{search: ((term: string, config: SearchConfig) => TextMatch[]), pipeline: ElasticLunrPipeline}|undefined|null} TextSearchIndex
 * @typedef {{original: string, stem: string, start: number, end: number}} TextToken
 */

/** Whether to search word prefixes or whole words in full-text searches. Should match the setting in search-box.js.
 * @type {boolean}
 */
const expandHlMatches = true;


const searchIndex = /** @type {{searchIndex: TextSearchIndex}} */ (
  /** @type {unknown} */ (window)
).searchIndex;


/** Tokenizes the given string, computing stems.
 * @param {string} text
 * @return {TextToken[]}
 */
const tokenizeText = (text) => {
  const toks = [];
  const regex = /[^\s(),."“”—:]+/g;
  let match;
  while ((match = regex.exec(text)) !== null) {
    let stems = searchIndex.pipeline.run([match[0]]);
    for (const stem of stems) {
      toks.push({
        original: match[0],
        start: match.index,
        end: match.index + match[0].length,
        stem: stem.toLowerCase()
      });
    }
  }
  return toks;
}

function highlightSearchTerms() {
  // Get search terms from URL query string
  const urlParams = new URLSearchParams(window.location.search);
  const searchQuery = urlParams.get('terms');
  
  if (!searchQuery) {
    return; // No search terms found
  }
  
  // Stem the terms
  const searchTerms = {};
  const regex = /\S+/g;
  let match;
  while ((match = regex.exec(searchQuery)) !== null) {
    let stems = searchIndex.pipeline.run([match[0]]);
    for (const stem of stems) {
      searchTerms[stem.toLowerCase()] = match[0];
    }
  }

  // Function to highlight text in a text node
  function highlightTextNode(textNode) {
    let text = textNode.textContent;

    const toks = tokenizeText(text);
    for (const t of toks.reverse()) {
      if (expandHlMatches) {
        // We're doing full-text search with matching prefixes. Find the longest matching stem in the results and use it.
        let bestStem = "";
        for (termStem in searchTerms) {
          if (termStem.length <= bestStem.length) continue;
          if (t.stem.startsWith(termStem)) bestStem = termStem;
        }
        if (bestStem.length > 0) {
          text = text.slice(0, t.start) + `<span class="text-search-results" title="Result for “${searchTerms[bestStem]}”">${text.slice(t.start, t.end)}</span>` + text.slice(t.end);
        }
      } else {
        // We're doing full-text search with whole words only. Look the stem up directly.
        if (searchTerms.hasOwnProperty(t.stem)) {
          text = text.slice(0, t.start) + `<span class="text-search-results" title="Result for “${searchTerms[t.stem]}”">${text.slice(t.start, t.end)}</span>` + text.slice(t.end);
        }
      }
    }
        
    // Create a temporary container
    const tempDiv = document.createElement('div');
    tempDiv.innerHTML = text;
    
    // Replace the text node with highlighted content
    const fragment = document.createDocumentFragment();
    while (tempDiv.firstChild) {
      fragment.appendChild(tempDiv.firstChild);

    }
    const parent = textNode.parentNode;
    parent.replaceChild(fragment, textNode);
    parent.querySelectorAll('.text-search-results').forEach((e) => {
      e.addEventListener('click', () => {
        const i = allHighlights.indexOf(e);
        if (i >= 0) {
          currentHighlightIndex = i;
          updateNavigationState();
        }
      });
    });
  }
  
  /** Function to traverse DOM and find text nodes
   * @param {any} node
   */
  function traverseNodes(node) {
    if (node.nodeType === Node.TEXT_NODE) {
      highlightTextNode(node);
    } else if (node.nodeType === Node.ELEMENT_NODE) {
      // Skip script, style, and already highlighted elements
      if (node.tagName &&
          !['SCRIPT', 'STYLE', 'NOSCRIPT'].includes(node.tagName.toUpperCase()) &&
          !node.classList.contains('text-search-results') &&
          // Don't highlight search terms in invisible hovers
          !node.classList.contains('hover-info') &&
          // Don't highlight search terms in doc box labels
          !(node.classList.contains('label') && node.parentNode && node.parentNode.classList.contains('namedocs'))) {
        
        // Process child nodes (in reverse order to handle DOM changes)
        const children = Array.from(node.childNodes);
        for (let i = children.length - 1; i >= 0; i--) {
          traverseNodes(children[i]);
        }
      }
    }
  }
  
  // Start traversal from <main>
  document.querySelectorAll('main section').forEach(traverseNodes);
  
  // Update highlights array after highlighting
  updateHighlightsArray();
}

// Function to remove all highlights
function removeHighlights() {
  const highlightedElements = document.querySelectorAll('span.text-search-results');
  highlightedElements.forEach(span => {
    const parent = span.parentNode;
    parent.replaceChild(document.createTextNode(span.textContent), span);
    parent.normalize(); // Merge adjacent text nodes
  });
  updateHighlightsArray();
}

/** The index of the current highlight
 * @type {number}
 */
let currentHighlightIndex = -1;
/** All highlight elements.
 * @type {HTMLElement[]}
 */
let allHighlights = [];

/** Update highlights array and reset navigation
 */
function updateHighlightsArray() {
  allHighlights = Array.from(document.querySelectorAll('span.text-search-results'));
  currentHighlightIndex = -1;
  updateNavigationState();
}

/** Navigate to next highlight
 */
function nextHighlight() {
  if (allHighlights.length === 0) return;
  
  currentHighlightIndex = (currentHighlightIndex + 1) % allHighlights.length;
  scrollToHighlight(currentHighlightIndex);
}

/** Navigate to previous highlight
 */
function prevHighlight() {
  if (allHighlights.length === 0) return;
  
  currentHighlightIndex = currentHighlightIndex <= 0 ?
    allHighlights.length - 1 : currentHighlightIndex - 1;
  scrollToHighlight(currentHighlightIndex);
}

/** Scroll to a specific highlight
 * @param {number} index The index of the highlight element in allHighlights
 */
function scrollToHighlight(index) {
  if (index >= 0 && index < allHighlights.length) {
    // Ensure visibility by opening collapsed examples
    let here = allHighlights[index];
    if (here) {
      while (here = here.parentElement) {
        if (here.nodeName.toLowerCase() == "details") {
          here.setAttribute('open', 'open');
          break;
        }
      }
    }

    // Scroll to it
    allHighlights[index].scrollIntoView({
      behavior: 'smooth',
      block: 'center'
    });
    
    updateNavigationState();
  }
}

/** Update navigation button states based on the contents of the document.
 */
function updateNavigationState() {
  const prevBtn = document.getElementById('highlight-prev');
  const nextBtn = document.getElementById('highlight-next');
  const countSpan = document.getElementById('highlight-count');
  const currentSpan = document.getElementById('highlight-current');
  const currentCount = document.getElementById('highlight-current-count');
  
  if (prevBtn && nextBtn && countSpan) {
    const hasHighlights = allHighlights.length > 0;
    prevBtn.disabled = !hasHighlights;
    nextBtn.disabled = !hasHighlights;
    
    if (hasHighlights && currentHighlightIndex >= 0) {
      countSpan.textContent = `${currentHighlightIndex + 1}/${allHighlights.length}`;
      currentSpan.textContent = allHighlights[currentHighlightIndex].textContent;
      let resName = allHighlights[currentHighlightIndex].title;
      resName = resName.charAt(0).toLowerCase() + resName.slice(1);
      currentCount.title = 'Go to ' + resName;
      document.querySelectorAll('.text-search-results').forEach((e) => e.classList.remove('focused'));
      let here = allHighlights[currentHighlightIndex];
      here.classList.add('focused');
      while (here = here.parentElement) {
        if (here.nodeName.toLowerCase() == "details") {
            here.setAttribute('open', 'open');
            break;
        }
      }
    } else {
      countSpan.textContent = hasHighlights ? `0/${allHighlights.length}` : '0/0';
      currentSpan.textContent = '';
      currentCount.title = '';
    }
  }
}

/** Toggle highlights
 */
function toggleHighlights() {
  const existingHighlights = document.querySelectorAll('span.text-search-results');
  if (existingHighlights.length > 0) {
    removeHighlights();
  } else {
    highlightSearchTerms();
  }
}

/** Scroll to first highlight after a specific element
 * @param {string} elementId
 */
function scrollToFirstHighlightAfter(elementId) {
  let targetElement = document.getElementById(elementId);
  if (!targetElement) {
    targetElement = document.body;
  }
  
  const highlights = document.querySelectorAll('span.text-search-results');
  if (highlights.length === 0) {
    return false;
  }
  
  // Find the first highlight that comes after the target element in document order
  const targetPosition = targetElement.compareDocumentPosition ?
    targetElement : null;
  
  if (!targetPosition) {
    return false;
  }
  
  for (let highlight of highlights) {
    const position = targetElement.compareDocumentPosition(highlight);
    // Check if highlight comes after target element
    if (position & Node.DOCUMENT_POSITION_FOLLOWING) {
      highlight.scrollIntoView({
        behavior: 'smooth',
        block: 'center'
      });
      currentHighlightIndex = allHighlights.indexOf(highlight);
      updateNavigationState();
      return true;
    }
  }
  
  return false;
}

/** Checks whether there's a search query in the URL */
function hasSearchQuery() {
  const urlParams = new URLSearchParams(window.location.search);
  const searchQuery = urlParams.get('terms');
  return searchQuery && searchQuery.trim().length > 0;
}

/** Creates control buttons (only if search query exists)
 */
function createControlButtons() {
  if (!hasSearchQuery()) {
    return;
  }
  
  const container = document.createElement('div');
  container.id = 'highlight-controls';
  
  // Previous button
  const prevBtn = document.createElement('button');
  prevBtn.id = 'highlight-prev';
  prevBtn.textContent = '◀';
  prevBtn.title = 'Previous match';
  prevBtn.addEventListener('click', prevHighlight);
  
  const currentSpan = document.createElement('span');
  currentSpan.id = 'highlight-current';

  // Count display
  const countSpan = document.createElement('span');
  countSpan.id = 'highlight-count';
  countSpan.textContent = '0/0';

  const currentCount = document.createElement('span');
  currentCount.id = 'highlight-current-count';
  currentCount.appendChild(currentSpan);
  currentCount.appendChild(countSpan);
  currentCount.addEventListener('click', () => scrollToHighlight(currentHighlightIndex));
  
  // Next button
  const nextBtn = document.createElement('button');
  nextBtn.id = 'highlight-next';
  nextBtn.textContent = '▶';
  nextBtn.title = 'Next match';
  nextBtn.addEventListener('click', nextHighlight);
  
  // Toggle button
  const toggleBtn = document.createElement('button');
  toggleBtn.id = 'highlight-close';
  toggleBtn.textContent = '✖';
  toggleBtn.title = 'Close search';
  toggleBtn.addEventListener('click', toggleHighlights);
  toggleBtn.addEventListener('click', () => container.remove());
  
  container.appendChild(prevBtn);
  container.appendChild(currentCount);
  container.appendChild(nextBtn);
  container.appendChild(toggleBtn);
  
  document.body.appendChild(container);
}

// Run the highlighter when DOM is ready
if (document.readyState === 'loading') {
  document.addEventListener('DOMContentLoaded', function() {
    highlightSearchTerms();
    createControlButtons();
    updateHighlightsArray();
    
    // Check for hash in URL and scroll to first highlight after it
    if (window.location.hash) {
      const elementId = window.location.hash.substring(1);
      setTimeout(() => {
        scrollToFirstHighlightAfter(elementId);
      }, 100); // Small delay to ensure highlighting is complete
    }
  });
} else {
  highlightSearchTerms();
  createControlButtons();
  updateHighlightsArray();
  
  // Check for hash in URL and scroll to first highlight after it
  if (window.location.hash) {
    const elementId = window.location.hash.substring(1);
    setTimeout(() => {
      scrollToFirstHighlightAfter(elementId);
    }, 100); // Small delay to ensure highlighting is complete
  }
}
