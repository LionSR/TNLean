#!/usr/bin/env python3
"""Reader-facing regression for the generated web blueprint.

A web build that exits zero can still hand the reader an unusable page: an
identifier that is the repr of a renderer object, a display that opens and
closes before its own entries, a bracketed commutator read as a line spacing,
a cross-reference printed as ``??``, an empty link where a file path belongs.
Every one of those was produced by a build that reported success.

The checks below therefore read the built pages rather than the build log.
They come in two passes.  The first reads the generated source before a
browser can repair it, because a browser silently closes a paragraph that the
renderer left open and hides the evidence.  The second opens every page and
measures what a reader would meet: mathematics that failed to typeset,
LaTeX left visible in the prose, and, at a narrow width, a page the reader
must scroll sideways as a whole rather than one wide display at a time.

The local server and browser session are the ones used by
``test_tenkz_equation_web.py``.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

_SCRIPTS = Path(__file__).resolve().parent
sys.path.insert(0, str(_SCRIPTS))
# The rule deciding what a bracket after a row break means belongs to the
# renderer. It is read from there rather than restated, so the two cannot
# come to disagree; the module it lives in imports no renderer of its own.
sys.path.insert(0, str(_SCRIPTS.parent / "blueprint/src/Packages"))

from playwright.sync_api import Page, sync_playwright

from _tnlean_utils import ROW_BREAK_LENGTH
from test_tenkz_equation_web import serve


# A width at which a phone reads the blueprint, and a width at which a desktop
# does.  At both, the page itself must not scroll sideways.
MOBILE_WIDTH = 360
DESKTOP_WIDTH = 1440

# Commands that carry blueprint bookkeeping.  They address the dependency
# graph and the Lean library, never the reader, so none of them may reach a
# page as text.
METADATA_COMMANDS = (
    "lean",
    "leanok",
    "mathlibok",
    "notready",
    "uses",
    "alsoIn",
    "proves",
    "discussion",
    "tenkzkernel",
    "path",
)

ROW_BREAK_BRACKET = re.compile(r"\\\\\s*\[([^\]\n]*)\]")
ENVIRONMENT_OPEN = re.compile(r"\\begin\{([A-Za-z*]+)\}")
ENVIRONMENT_CLOSE = re.compile(r"\\end\{([A-Za-z*]+)\}")
RENDERER_REPR = re.compile(r'="[^"]*<plasTeX[^"]*"|="[^"]*object at 0x[0-9a-f]+[^"]*"')
EMPTY_LINK = re.compile(r"<a\b[^>]*\shref=\"\"[^>]*>\s*</a>")


def _generated_pages(root: Path) -> list[Path]:
    pages = sorted(root.glob("*.html"))
    if not pages:
        raise SystemExit(f"no generated blueprint pages under {root}")
    return pages


def _assert_no_renderer_internals(page: Path, source: str) -> None:
    """No attribute may carry a renderer object where a name belongs.

    A cross-reference key written inside a display used to reach the page as
    the repr of a parse fragment, which is both unreadable and different on
    every build.
    """
    found = RENDERER_REPR.search(source)
    assert found is None, f"{page.name}: renderer object in an attribute: {found.group(0)}"


def _assert_environments_balanced(page: Path, source: str) -> None:
    """Every display environment closes exactly as often as it opens.

    An environment the renderer does not know is closed before its entries and
    its real closing marker is left adrift, which reaches the reader as an
    empty display followed by the unset entries as raw text.
    """
    opened = ENVIRONMENT_OPEN.findall(source)
    closed = ENVIRONMENT_CLOSE.findall(source)
    for name in sorted(set(opened) | set(closed)):
        assert opened.count(name) == closed.count(name), (
            f"{page.name}: {name} opens {opened.count(name)} times and closes "
            f"{closed.count(name)} times"
        )
    assert "bgroup" not in opened, (
        f"{page.name}: a brace group reached the mathematics as an environment; "
        "a command with an argument is undeclared"
    )


def _assert_row_breaks_carry_lengths(page: Path, source: str) -> None:
    """A bracket after a row break holds a length or is guarded as content."""
    for match in ROW_BREAK_BRACKET.finditer(source):
        assert ROW_BREAK_LENGTH.match(match.group(1)), (
            f"{page.name}: a row break is followed by {match.group(0)!r}, which "
            "is mathematics read as a line spacing"
        )


def _assert_no_empty_links(page: Path, source: str) -> None:
    """No link may be both empty and unaddressed."""
    found = EMPTY_LINK.search(source)
    assert found is None, (
        f"{page.name}: empty link {found.group(0)!r}; a command is rendered "
        "through a template that belongs to another one"
    )


def _assert_generated_source(pages: list[Path]) -> None:
    for page in pages:
        source = page.read_text(encoding="utf-8", errors="replace")
        _assert_no_renderer_internals(page, source)
        _assert_environments_balanced(page, source)
        _assert_row_breaks_carry_lengths(page, source)
        _assert_no_empty_links(page, source)


READER_TEXT = """(commands) => {
  const walker = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT);
  const parts = [];
  while (walker.nextNode()) {
    const node = walker.currentNode;
    if (node.parentElement.closest('script, style, mjx-container, .MathJax')) continue;
    parts.push(node.nodeValue);
  }
  const text = parts.join(' ');
  const excerpt = index => text.slice(Math.max(0, index - 70), index + 70);
  // Once MathJax has run, no delimiter and no environment marker is left in
  // the reader's text. One that survives is a formula the reader is being
  // shown as source, which is the failure this file exists to reject; it must
  // be reported rather than skipped over.
  const source = [];
  for (const found of text.matchAll(/\\\\\\(|\\\\\\[|\\\\begin\\{/g)) {
    source.push(excerpt(found.index));
    if (source.length > 3) break;
  }
  const leaks = [];
  for (const command of commands) {
    const found = new RegExp('\\\\\\\\' + command + '\\\\b').exec(text);
    if (found) leaks.push(excerpt(found.index));
  }
  // A reference the renderer could not resolve prints two question marks,
  // bare in prose and parenthesised after \\eqref. Neither spelling depends on
  // what surrounds it, so neither is required to.
  const unresolved = /\\?\\?/.exec(text);
  return {
    source,
    leaks,
    unresolved: unresolved ? excerpt(unresolved.index) : null,
    errors: [...document.querySelectorAll('mjx-merror')]
      .map(node => node.getAttribute('title') || node.textContent).slice(0, 8),
    typeset: document.querySelectorAll('mjx-container').length,
  };
}"""

# An element may reach past the viewport only from inside something that
# scrolls, which is how one wide display stays readable without the page
# itself scrolling sideways.
OVERFLOW = """() => {
  const root = document.documentElement;
  const escaped = [];
  for (const element of document.querySelectorAll('body *')) {
    const box = element.getBoundingClientRect();
    if (box.width <= 0) continue;
    if (box.right <= root.clientWidth + 1 && box.left >= -1) continue;
    let scroller = element.parentElement, scoped = false;
    while (scroller && scroller !== root) {
      const overflow = getComputedStyle(scroller).overflowX;
      if (overflow === 'auto' || overflow === 'scroll') { scoped = true; break; }
      scroller = scroller.parentElement;
    }
    if (!scoped) escaped.push(element.tagName + '.' + (element.className || ''));
    if (escaped.length > 4) break;
  }
  return {scrollWidth: root.scrollWidth, clientWidth: root.clientWidth, escaped};
}"""


def _settle(page: Page) -> None:
    """Wait until MathJax has finished its first pass over this page.

    The bundle is fetched asynchronously, so at the moment the document is
    parsed it may not have installed itself yet.  Waiting for the promise to
    exist, and only then for it to resolve, is what keeps a page from being
    read before its mathematics is set.
    """
    page.wait_for_function(
        "() => window.MathJax && window.MathJax.startup"
        " && window.MathJax.startup.promise",
        timeout=120_000,
    )
    page.evaluate("() => window.MathJax.startup.promise")


def _assert_reader_text(name: str, facts: dict[str, object]) -> None:
    assert not facts["source"], (name, facts["source"])
    assert not facts["leaks"], (name, facts["leaks"])
    assert facts["unresolved"] is None, (name, facts["unresolved"])
    assert not facts["errors"], (name, facts["errors"])


def _assert_page_owns_no_sideways_scroll(name: str, width: int, facts: dict) -> None:
    assert facts["scrollWidth"] <= facts["clientWidth"] + 1, (name, width, facts)
    assert not facts["escaped"], (name, width, facts["escaped"])


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--web-root", type=Path, default=Path("blueprint/web"))
    args = parser.parse_args()

    root = args.web_root.resolve()
    pages = _generated_pages(root)
    _assert_generated_source(pages)

    typeset = 0
    with serve(root) as base_url, sync_playwright() as playwright:
        browser = playwright.chromium.launch()
        page = browser.new_page(viewport={"width": MOBILE_WIDTH, "height": 900})
        page.set_default_timeout(120_000)
        for generated in pages:
            page.goto(f"{base_url}/{generated.name}",
                      wait_until="domcontentloaded", timeout=120_000)
            # Proofs are folded away by default; a folded proof has no width,
            # so its displays would escape measurement.
            page.add_style_tag(content=".proof_content { display: block !important; }")
            _settle(page)
            facts = page.evaluate(READER_TEXT, list(METADATA_COMMANDS))
            _assert_reader_text(generated.name, facts)
            typeset += int(facts["typeset"])
            for width in (MOBILE_WIDTH, DESKTOP_WIDTH):
                page.set_viewport_size({"width": width, "height": 900})
                page.wait_for_timeout(200)
                _assert_page_owns_no_sideways_scroll(
                    generated.name, width, page.evaluate(OVERFLOW))
            page.set_viewport_size({"width": MOBILE_WIDTH, "height": 900})
        browser.close()

    assert typeset > 0, (
        "no mathematics was typeset on any page; MathJax never ran, so the "
        "reader-facing checks proved nothing"
    )
    print(json.dumps({"pages": len(pages), "typeset": typeset}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
