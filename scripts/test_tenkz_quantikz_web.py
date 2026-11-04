#!/usr/bin/env python3
"""Check that the blueprint's quantikz circuit diagrams render on web pages.

Circuit diagrams are written with the quantikz TikZ library and travel the
same picture path as the tenkz diagrams: the web bridge
(``blueprint/src/Packages/tenkz_pic.py``) captures each ``quantikz`` body
verbatim, compiles it standalone against ``macros/diagrams.tex`` and emits one
``<img class="tenkz-pic tenkz-pic-circuit">``.  This test finds every circuit
in the blueprint by its source, not by page name, and checks:

* sources: the expanded content tree holds at least ``MIN_CIRCUITS``
  circuits, each inside a ``center`` environment whose comment names its
  source and its ink-to-symbol map;
* compile: every circuit compiles through the bridge to an SVG with ink that
  fits the standalone line width, so no part of it is cropped;
* web page: a document holding every circuit, parsed by plasTeX with the
  real bridge, templates and styles, emits exactly one circuit picture per
  circuit, with the circuit source as alternative text and an SVG file
  behind it; in Chromium every picture loads and stays inside the reading
  column at desktop and phone widths, without horizontal page scroll;
* built site (``--web-root``): the generated pages together carry exactly
  the blueprint's circuits, each picture's SVG present and inked.
  ``scripts/test_tenkz_equation_web.py`` runs the same site check after the
  CI web build.

Missing plasTeX or TeX tools skip their stages outside CI and fail in CI;
a missing Chromium skips the browser stage unless ``--require-browser``.
"""

from __future__ import annotations

import argparse
import html
import os
import re
import sys
import tempfile
from dataclasses import dataclass
from html.parser import HTMLParser
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "blueprint" / "src"
sys.path.insert(0, str(ROOT / "scripts"))
sys.path.insert(0, str(SRC / "Packages"))

from blueprint_tex_tree import in_comment, read_tex_tree  # noqa: E402

MIN_CIRCUITS = 5
CIRCUIT_RE = re.compile(r"\\begin\{quantikz\}.*?\\end\{quantikz\}", re.S)
CENTER_RE = re.compile(r"\\(begin|end)\{center\}")
CIRCUIT_CLASS = "tenkz-pic-circuit"
# standalone's varwidth box is the article line width (345pt); a wider
# picture loses its right edge in the web SVG.
MAX_WIDTH_PT = 340.0
SVG_SIZE_RE = re.compile(r'<svg\b[^>]*\bwidth="([\d.]+)pt"[^>]*\bheight="([\d.]+)pt"')


def normalize(source: str) -> str:
    return " ".join(source.split())


@dataclass(frozen=True)
class Circuit:
    source: str
    center: str


def blueprint_circuits(src_root: Path = SRC) -> list[Circuit]:
    """Every live quantikz circuit of the content tree, with its center body."""
    text = read_tex_tree(src_root / "content.tex", src_root)
    circuits: list[Circuit] = []
    for match in CIRCUIT_RE.finditer(text):
        if in_comment(text, match.start()):
            continue
        opened = [
            token for token in CENTER_RE.finditer(text, 0, match.start())
            if not in_comment(text, token.start())
        ]
        assert opened and opened[-1].group(1) == "begin", (
            "a quantikz circuit must sit in a center environment",
            match.group(0)[:200],
        )
        start = opened[-1].end()
        end = text.find(r"\end{center}", match.end())
        assert end >= 0, match.group(0)[:200]
        circuits.append(Circuit(match.group(0), text[start:end]))
    return circuits


def check_sources(circuits: list[Circuit]) -> None:
    assert len(circuits) >= MIN_CIRCUITS, (len(circuits), MIN_CIRCUITS)
    sources = [normalize(circuit.source) for circuit in circuits]
    assert len(set(sources)) == len(sources), "two circuits share one source"
    for circuit in circuits:
        comments = "\n".join(
            line.strip() for line in circuit.center.splitlines()
            if line.strip().startswith("%")
        )
        assert "Source:" in comments, circuit.source[:200]
        assert re.search(r"Ink-to-(?:symbol|index) map", comments), circuit.source[:200]


def svg_size(path: Path) -> tuple[float, float]:
    match = SVG_SIZE_RE.search(path.read_text(encoding="utf-8", errors="replace")[:2000])
    assert match, path
    return float(match.group(1)), float(match.group(2))


def check_compile(circuits: list[Circuit], svg_dir: Path, require: bool) -> bool:
    import tenkz_pic

    if tenkz_pic.toolchain() is None:
        assert not require, "quantikz circuits need xelatex and dvisvgm or pdftocairo"
        print("SKIP compile: no SVG toolchain")
        return False
    for circuit in circuits:
        svg, _ = tenkz_pic.render_unit(circuit.source, svg_dir)
        assert svg is not None and tenkz_pic._svg_has_ink(svg), circuit.source[:200]
        width, height = svg_size(svg)
        assert 0 < width <= MAX_WIDTH_PT and height > 0, (width, height, circuit.source[:200])
    print(f"compile: {len(circuits)} circuits render with ink within {MAX_WIDTH_PT}pt")
    return True


class _PictureParser(HTMLParser):
    """Collect the circuit pictures of one generated page."""

    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.pictures: list[tuple[str, str]] = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        values = dict(attrs)
        if tag == "img" and CIRCUIT_CLASS in (values.get("class") or "").split():
            self.pictures.append((values.get("src") or "", values.get("alt") or ""))


def page_pictures(page: Path) -> list[tuple[str, str]]:
    parser = _PictureParser()
    parser.feed(page.read_text(encoding="utf-8"))
    parser.close()
    return parser.pictures


def check_pages(pages: list[Path], circuits: list[Circuit]) -> dict[str, int]:
    """Every circuit is pictured, once per page that shows it, with an inked SVG.

    A page that repeats a statement (such as a dependency-graph view) may
    show a circuit again, so the pages are compared with the sources as sets.
    """
    import tenkz_pic

    expected = {normalize(circuit.source) for circuit in circuits}
    found: set[str] = set()
    per_page: dict[str, int] = {}
    for page in pages:
        pictures = page_pictures(page)
        if pictures:
            per_page[page.name] = len(pictures)
        alts = [normalize(alt) for _, alt in pictures]
        assert len(set(alts)) == len(alts), (page.name, "a circuit is pictured twice")
        for src, _ in pictures:
            svg = (page.parent / html.unescape(src)).resolve()
            assert svg.is_file() and tenkz_pic._svg_has_ink(svg), (page.name, src)
        found.update(alts)
    assert found == expected, (
        "circuit pictures on the pages differ from the circuit sources",
        sorted(expected - found)[:3],
        sorted(found - expected)[:3],
    )
    return per_page


def check_site(web_root: Path, src_root: Path = SRC) -> dict[str, int]:
    """Site check for a built blueprint, robust to page names."""
    circuits = blueprint_circuits(src_root)
    pages = sorted(web_root.glob("*.html"))
    assert pages, f"no generated pages under {web_root}"
    per_page = check_pages(pages, circuits)
    print(f"site: {len(circuits)} circuit pictures on {per_page}")
    return per_page


def build_page(circuits: list[Circuit], out: Path) -> Path:
    """Render a document holding every circuit through the real web bridge."""
    from plasTeX.Renderers.HTML5 import Renderer, addConfig
    from plasTeX.TeX import TeX

    import tenkz_pic

    body = "\n".join(
        "\\begin{center}\n" + circuit.source + "\n\\end{center}\nText.\n"
        for circuit in circuits
    )
    source = "\\documentclass{article}\n\\begin{document}\n" + body + "\\end{document}\n"
    tex = TeX()
    document = tex.ownerDocument
    addConfig(document.config)
    document.config["html5"]["extra-css"] = ["extra_styles.css"]
    document.userdata["working-dir"] = str(SRC)
    document.config["general"]["extra-templates"] = [str(SRC / "plastex_templates")]
    document.config["files"]["filename"] = "index.html"
    document.config["files"]["directory"] = str(out)
    document.config["files"]["split-level"] = -100
    document.context.importMacros({"quantikz": tenkz_pic.quantikz})
    tex.input(source)
    previous = Path.cwd()
    os.chdir(out)
    try:
        Renderer().render(tex.parse())
    finally:
        os.chdir(previous)
    return out / "index.html"


def check_browser(page: Path, count: int, require: bool) -> None:
    try:
        from playwright.sync_api import sync_playwright
    except ImportError:
        assert not require, "playwright is not installed"
        print("SKIP browser: playwright is not installed")
        return
    with sync_playwright() as playwright:
        try:
            browser = playwright.chromium.launch()
        except Exception as error:  # noqa: BLE001 - a missing browser binary
            assert not require, error
            print(f"SKIP browser: {str(error).splitlines()[0]}")
            return
        tab = browser.new_page()
        tab.route("https://**", lambda route: route.abort())
        tab.goto(page.as_uri())
        tab.wait_for_function(
            "() => [...document.images].every(image => image.complete)"
        )
        for width in (1440, 360):
            tab.set_viewport_size({"width": width, "height": 1000})
            facts = tab.evaluate(
                """selector => {
                const main = document.querySelector('.main-text') || document.body;
                const bounds = main.getBoundingClientRect();
                const pictures = [...document.querySelectorAll(selector)];
                return {
                  count: pictures.length,
                  problems: pictures.filter(picture => {
                    const rect = picture.getBoundingClientRect();
                    return !picture.naturalWidth || !rect.width || !rect.height
                      || rect.left < bounds.left - 1 || rect.right > bounds.right + 1;
                  }).map(picture => picture.getAttribute('src')),
                  pageScroll: document.documentElement.scrollWidth
                    > document.documentElement.clientWidth + 1,
                };
            }""",
                f"img.{CIRCUIT_CLASS}",
            )
            assert facts["count"] == count, (width, facts)
            assert not facts["problems"], (width, facts)
            assert not facts["pageScroll"], (width, facts)
        browser.close()
    print(f"browser: {count} circuit pictures load and fit at 1440px and 360px")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--web-root", type=Path,
                        help="also check a built blueprint site")
    parser.add_argument("--output-dir", type=Path,
                        help="keep the rendered page and SVGs here")
    parser.add_argument("--require-browser", action="store_true")
    args = parser.parse_args()
    in_ci = os.environ.get("CI") == "true"

    circuits = blueprint_circuits()
    check_sources(circuits)
    print(f"sources: {len(circuits)} quantikz circuits in center environments")

    with tempfile.TemporaryDirectory(prefix="quantikz-web-") as scratch:
        out = args.output_dir.resolve() if args.output_dir else Path(scratch)
        out.mkdir(parents=True, exist_ok=True)
        compiled = check_compile(circuits, out / "tenkz_svg", require=in_ci)
        try:
            import plasTeX  # noqa: F401
        except ImportError:
            assert not in_ci, "plasTeX is not installed"
            print("SKIP web page: plasTeX is not installed")
        else:
            if compiled:
                page = build_page(circuits, out)
                per_page = check_pages([page], circuits)
                print(f"web page: {per_page}")
                check_browser(page, len(circuits), require=args.require_browser)
    if args.web_root is not None:
        check_site(args.web_root.resolve())
    print("quantikz circuit diagrams render on web pages.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
