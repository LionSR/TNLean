#!/usr/bin/env python3
"""Check that verbatim picture capture preserves TeX's inline row boundaries.

Use the real parser, templates and styles, with deterministic SVG boxes instead
of invoking a TeX engine: picture compilation is covered by test_tenkz_pic.py.
The layout check runs before MathJax, so it requires no CDN connection.
"""

from __future__ import annotations

import contextlib
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch

from plasTeX.Renderers.HTML5 import Renderer, addConfig
from plasTeX.TeX import TeX
from playwright.sync_api import sync_playwright

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "blueprint/src/Packages"))
import tenkz_pic  # noqa: E402


SOURCE = r"""\documentclass{article}
\begin{document}
Before.
\par\noindent\hfil
\begin{tenkz}A\end{tenkz}\quad$=$\quad\begin{tenkz}B\end{tenkz}
\hfil\par
After.
\begin{center}
\begin{tenkz}A\end{tenkz}$=$\begin{tenkz}B\end{tenkz}
\end{center}
\begin{center}
\begin{tenkz}A\end{tenkz}$=$\begin{tenkz}B\end{tenkz}

\begin{tikzcd}C\end{tikzcd}$=$\begin{tikzcd}D\end{tikzcd}
\end{center}
\begin{center}
\begin{tenkz}A\end{tenkz}\\
\begin{tenkz}B\end{tenkz}
\end{center}
Inline \begin{tenkz}A\end{tenkz} continues here.
\begin{tenkzequation}
\begin{tenkz}A\end{tenkz}$=$\begin{tenkz}B\end{tenkz}
\end{tenkzequation}
\begin{center}
\begin{tenkz}A\end{tenkz}$=\sum_i$
\begin{tabular}{c}
\begin{tenkz}B\end{tenkz}\\
\begin{tenkz}C\end{tenkz}
\end{tabular}
\end{center}
\end{document}
"""


def _svg_box(source: str, output: Path) -> tuple[Path, bool]:
    output.mkdir(parents=True, exist_ok=True)
    path = output / "box.svg"
    path.write_text(
        '<svg xmlns="http://www.w3.org/2000/svg" width="80" height="60">'
        '<rect x="1" y="1" width="78" height="58" '
        'fill="none" stroke="black"/></svg>',
        encoding="utf-8",
    )
    return path, True


def check_inline_layout() -> None:
    with tempfile.TemporaryDirectory(prefix="tenkz-inline-") as directory:
        root = Path(directory)
        tex = TeX()
        document = tex.ownerDocument
        # Load the shipped stylesheet with the document, as the web build does.
        # Injecting it after navigation first lays out center as a flex column,
        # then changes the formatting context underneath its line-break nodes.
        addConfig(document.config)
        document.config["html5"]["extra-css"] = ["extra_styles.css"]
        document.userdata["working-dir"] = str(ROOT / "blueprint/src")
        document.config["general"]["extra-templates"] = [
            str(ROOT / "blueprint/src/plastex_templates")
        ]
        document.config["files"]["filename"] = "index.html"
        document.config["files"]["directory"] = str(root)
        document.config["files"]["split-level"] = -100
        document.context.importMacros(
            {
                name: getattr(tenkz_pic, name)
                for name in ("tenkz", "tikzcd", "tenkzequation")
            }
        )
        tex.input(SOURCE)
        with contextlib.chdir(root), patch.object(tenkz_pic, "render_unit", _svg_box):
            Renderer().render(tex.parse())
        with sync_playwright() as playwright:
            browser = playwright.chromium.launch()
            page = browser.new_page()
            page.route("https://**", lambda route: route.abort())
            page.goto((root / "index.html").as_uri())
            page.wait_for_function(
                "() => [...document.images].every(i => i.complete && i.naturalWidth > 0)"
            )
            for width in (1440, 360):
                page.set_viewport_size({"width": width, "height": 1000})
                facts = page.evaluate(
                    """() => {
                    const main = document.querySelector('.main-text');
                    const centered = main.querySelectorAll('.centered');
                    const glue = main.querySelector('p:has(> .tex-hfil)');
                    const rows = [glue, centered[0], ...centered[1].querySelectorAll('p'),
                        main.querySelector('.tenkz-equation-row')];
                    const sameRow = row => {
                        const r = [...row.querySelectorAll('img')]
                            .map(i => i.getBoundingClientRect());
                        return r.length === 2 && r[1].left > r[0].right
                            && Math.abs(r[0].top - r[1].top) < 1;
                    };
                    const broken = centered[2].querySelectorAll('img');
                    const inline = [...main.querySelectorAll('p')]
                        .find(p => p.textContent.trim().startsWith('Inline'));
                    const table = main.querySelector('table.tabular');
                    const box = table.getBoundingClientRect();
                    const lhs = table.parentElement.querySelector(':scope > img')
                        .getBoundingClientRect();
                    const stacked = [...table.querySelectorAll('img')]
                        .map(i => i.getBoundingClientRect());
                    return {
                        rows: rows.length,
                        sameRow: rows.every(sameRow),
                        operators: rows.every(row => row.textContent.includes('=')),
                        glueCentered: getComputedStyle(glue).textAlign === 'center',
                        proseSeparate: glue.previousElementSibling.textContent.trim() === 'Before.'
                            && glue.nextElementSibling.textContent.trim() === 'After.',
                        paragraphs: centered[1].querySelectorAll('p').length === 2,
                        explicitBreak: broken[1].getBoundingClientRect().top
                            >= broken[0].getBoundingClientRect().bottom,
                        inlineProse: inline.querySelectorAll('img').length === 1
                            && inline.textContent.includes('continues here.'),
                        inlineTable: getComputedStyle(table).display === 'inline-table'
                            && box.left > lhs.right
                            && Math.abs(box.top + box.height / 2
                                - lhs.top - lhs.height / 2) < 1,
                        stackedTableRows: stacked.length === 2
                            && stacked[1].top >= stacked[0].bottom,
                        contained: main.scrollWidth <= main.clientWidth + 1,
                    };
                }"""
                )
                assert facts.pop("rows") == 5, facts
                assert all(facts.values()), (
                    width,
                    facts,
                    page.locator(".main-text .centered")
                    .nth(2)
                    .evaluate(
                        """element => ({
                            html: element.innerHTML,
                            display: getComputedStyle(element).display,
                            breaks: [...element.querySelectorAll('br')].map(br => ({
                                rect: br.getBoundingClientRect().toJSON(),
                                display: getComputedStyle(br).display,
                            })),
                            images: [...element.querySelectorAll('img')].map(image => ({
                                rect: image.getBoundingClientRect().toJSON(),
                                display: getComputedStyle(image).display,
                            })),
                        })"""
                    ),
                )
            browser.close()
    print(
        "Inline tenkz/tikzcd layout: paragraphs, glue, explicit breaks and equation rows pass."
    )


if __name__ == "__main__":
    check_inline_layout()
