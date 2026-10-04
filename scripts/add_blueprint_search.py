#!/usr/bin/env python3
"""Add client-side full-text search to the generated web blueprint.

The plasTeX web build ships no search box: a reader can jump only to entries
that appear in the table of contents, not to an arbitrary phrase in the prose.
This step layers Pagefind (https://pagefind.app) onto the already-built pages
so that any word in the blueprint can be found from any page.

Run it against the generated tree after ``leanblueprint web`` (and after the
reader-facing render regression):

    python3 scripts/add_blueprint_search.py --web-root blueprint/web

The step is offline once Pagefind is installed; it

1. tags each chapter's prose (``div.main-text``) as the Pagefind search body,
   so the per-page navigation and table of contents -- which repeat on every
   page -- are not indexed;
2. runs Pagefind to build the static index under ``<web-root>/pagefind/``;
3. injects the Pagefind search box into every page's header, plus the small
   stylesheet/script links that drive it.

The injected markup is bracketed by HTML comment markers, so re-running the
script on an already-processed tree is a no-op.

Pagefind is located automatically: the ``pagefind`` Python module
(``pip install 'pagefind[extended]'``), a ``pagefind`` executable on ``PATH``,
or ``npx pagefind`` are tried in that order.
"""

from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path

MARKER = "blueprint-search"

HEAD_SNIPPET = (
    f"<!-- {MARKER}:begin -->"
    '<link rel="stylesheet" href="pagefind/pagefind-ui.css" />'
    f"<!-- {MARKER}:end -->"
)

BOX_SNIPPET = (
    f"<!-- {MARKER}:begin -->"
    '<div id="blueprint-search" class="blueprint-search"></div>'
    f"<!-- {MARKER}:end -->"
)

# Pagefind records page URLs relative to the site root it indexes (a leading
# ``/``). The blueprint is published under a sub-path, not the domain root, so
# the leading slash is stripped and the link resolved relative to the current
# page instead; every page lives flat in one directory, so this is correct
# wherever the site is deployed.
SCRIPT_SNIPPET = (
    f"<!-- {MARKER}:begin -->"
    '<script src="pagefind/pagefind-ui.js"></script>'
    "<script>"
    'window.addEventListener("DOMContentLoaded", function () {'
    "  if (!window.PagefindUI) return;"
    "  new PagefindUI({"
    '    element: "#blueprint-search",'
    "    showSubResults: true,"
    "    showImages: false,"
    "    processResult: function (result) {"
    '      if (result && typeof result.url === "string") {'
    '        result.url = result.url.replace(/^\\//, "");'
    "      }"
    "      if (result && result.sub_results) {"
    "        result.sub_results.forEach(function (sub) {"
    '          if (typeof sub.url === "string") sub.url = sub.url.replace(/^\\//, "");'
    "        });"
    "      }"
    "      return result;"
    "    }"
    "  });"
    "});"
    "</script>"
    f"<!-- {MARKER}:end -->"
)


def _pagefind_command() -> list[str]:
    """Return a runnable Pagefind command, preferring the Python module."""
    candidates = [
        [sys.executable, "-m", "pagefind"],
        ["pagefind"],
        ["npx", "-y", "pagefind@1"],
    ]
    for cmd in candidates:
        try:
            result = subprocess.run(
                cmd + ["--help"],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
            )
        except OSError:
            continue
        if result.returncode == 0:
            return cmd
    raise SystemExit(
        "Pagefind not found. Install it with "
        "`pip install 'pagefind[extended]'` or make `npx` available."
    )


def _tag_search_body(html: str) -> str:
    """Mark the chapter prose as the only indexed region of the page.

    With a search body present on the content pages, Pagefind excludes the
    pages that have none (the title and dependency-graph pages) and ignores the
    repeated table of contents on the pages that do.
    """
    needle = '<div class="main-text">'
    if needle in html and "data-pagefind-body" not in html:
        html = html.replace(
            needle, '<div class="main-text" data-pagefind-body>', 1)
    return html


def _process(html: str) -> tuple[str, bool]:
    """Return the processed page and whether the search UI was injected."""
    html = _tag_search_body(html)
    if f"{MARKER}:begin" in html:
        return html, False
    if "</head>" not in html or "</body>" not in html:
        return html, False
    new = html.replace("</head>", HEAD_SNIPPET + "</head>", 1)
    if "</header>" in new:
        new = new.replace("</header>", BOX_SNIPPET + "</header>", 1)
    elif "<body>" in new:
        new = new.replace("<body>", "<body>" + BOX_SNIPPET, 1)
    else:
        return html, False
    new = new.replace("</body>", SCRIPT_SNIPPET + "</body>", 1)
    return new, True


def _run_pagefind(root: Path) -> None:
    cmd = _pagefind_command() + ["--site", str(root)]
    print("==> Indexing:", " ".join(cmd))
    subprocess.run(cmd, check=True)
    if not (root / "pagefind" / "pagefind-ui.js").is_file():
        raise SystemExit(
            f"Pagefind ran but produced no UI bundle under {root / 'pagefind'}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--web-root", type=Path, default=Path("blueprint/web"))
    args = parser.parse_args()

    root = args.web_root.resolve()
    pages = sorted(root.glob("*.html"))
    if not pages:
        raise SystemExit(f"no generated blueprint pages under {root}")

    injected = 0
    for page in pages:
        original = page.read_text(encoding="utf-8")
        new, did = _process(original)
        if new != original:
            page.write_text(new, encoding="utf-8")
        injected += did
    print(f"==> Prepared {injected} of {len(pages)} pages for search")

    _run_pagefind(root)
    print("==> Search index and UI added")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
