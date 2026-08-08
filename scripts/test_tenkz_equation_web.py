#!/usr/bin/env python3
"""Browser regression for top-level tenkz equation rows in the blueprint."""

from __future__ import annotations

import argparse
import contextlib
import functools
import http.server
import json
import re
import socketserver
import threading
from html.parser import HTMLParser
from pathlib import Path

from playwright.sync_api import Page, sync_playwright


EXPECTED_PICTURE_COUNTS = [2] * 8 + [2, 3] + [2, 3, 2, 5, 1, 3, 3]
PAGES = ("ch-symmetry.html", "ch-mpdo.html", "ch-mpdo_rfp.html")
EXPECTED_WRAPPER_COUNTS = {
    "ch-symmetry.html": 8,
    "ch-mpdo.html": 2,
    "ch-mpdo_rfp.html": 7,
}


def _tenkzequation_bodies(source: str) -> list[str]:
    """Return top-level tenkzequation bodies in source order."""
    token = re.compile(r"\\(?:begin|end)\{tenkzequation\}")
    start: int | None = None
    bodies: list[str] = []
    for match in token.finditer(source):
        if match.group(0).startswith(r"\begin"):
            assert start is None, "tenkzequation environments must not nest"
            start = match.end()
        else:
            assert start is not None, "tenkzequation closes without opening"
            bodies.append(source[start:match.start()])
            start = None
    assert start is None, "tenkzequation remains unclosed"
    return bodies


def _read_tex_tree(path: Path, source_root: Path) -> str:
    """Read a TeX source after recursively expanding its input wrappers."""
    source = path.read_text(encoding="utf-8")

    def expand(match: re.Match[str]) -> str:
        target = match.group(1)
        if not target.endswith(".tex"):
            target += ".tex"
        return _read_tex_tree(source_root / target, source_root)

    return re.sub(r"\\input\{([^}]+)\}", expand, source)


def _assert_source_linked_groups(repo_root: Path) -> None:
    """Pin every migrated sibling-picture row to its TeX source wrapper."""
    symmetry = (
        repo_root / "blueprint/src/chapter/ch12_symmetry_virtual_and_cohomology.tex"
    ).read_text(encoding="utf-8")
    symmetry += (
        repo_root / "blueprint/src/chapter/ch12_symmetry_string_order.tex"
    ).read_text(encoding="utf-8")
    symmetry_bodies = _tenkzequation_bodies(symmetry)
    symmetry_anchors = (
        r"\tn[species=operator, label pos=w, ports={90:physical:$i$}]{U(g)}",
        r"\tn[skin=ring]{X_1(g^{-1})}",
        "Condition C1, lines 328--334, states",
        "Condition C2, lines 335--340, states",
        "Conditions C2--C3, lines 335--347",
        "Condition C1, lines 328--334, is",
        "Condition C2, lines 335--340, is",
        r"$\;=\;\mu\,$",
    )
    assert len(symmetry_bodies) == len(symmetry_anchors), len(symmetry_bodies)
    for body, anchor in zip(symmetry_bodies, symmetry_anchors, strict=True):
        assert anchor in body, anchor
        assert body.count(r"\begin{tenkz}") == 2, anchor

    source_root = repo_root / "blueprint/src"
    blocked = _read_tex_tree(
        source_root / "chapter/ch21_mpdo_rfp_blocked_rfp.tex", source_root
    )
    blocked_bodies = _tenkzequation_bodies(blocked)
    assert len(blocked_bodies) == 1, len(blocked_bodies)
    assert blocked_bodies[0].count(r"\begin{tenkz}") == 2
    assert r"\qquad$=$\qquad" in blocked_bodies[0]

    channels = _read_tex_tree(
        source_root
        / "chapter/ch21_mpdo_rfp_simple_local_refinement_channels.tex",
        source_root,
    )
    channel_bodies = _tenkzequation_bodies(channels)
    assert len(channel_bodies) == 2, len(channel_bodies)
    for body, anchor in zip(
        channel_bodies,
        (r"$\widehat{\mathcal T}^{\,2}:\quad$", r"$\widehat{\mathcal S}^{\,2}:\quad$"),
        strict=True,
    ):
        assert anchor in body, anchor
        assert body.count(r"\begin{tenkz}") == 3, anchor
        assert body.count(r"\xrightarrow") == 2, anchor


class QuietHandler(http.server.SimpleHTTPRequestHandler):
    """Serve the generated blueprint without writing request logs."""

    def log_message(self, format: str, *args: object) -> None:
        pass


class ReusableTCPServer(socketserver.TCPServer):
    allow_reuse_address = True


@contextlib.contextmanager
def serve(directory: Path):
    handler = functools.partial(QuietHandler, directory=str(directory))
    with ReusableTCPServer(("127.0.0.1", 0), handler) as server:
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        try:
            yield f"http://127.0.0.1:{server.server_address[1]}"
        finally:
            server.shutdown()
            thread.join()


class _GeneratedStructureParser(HTMLParser):
    """Record raw paragraph and equation-block structure without HTML5 repair."""

    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.in_paragraph = False
        self.paragraph_parts: list[str] = []
        self.events: list[tuple[str, str]] = []
        self.wrapper_count = 0

    def handle_starttag(
        self, tag: str, attrs: list[tuple[str, str | None]]
    ) -> None:
        if tag == "p":
            assert not self.in_paragraph, "generated source contains nested paragraphs"
            self.in_paragraph = True
            self.paragraph_parts = []
        if tag == "div":
            classes = dict(attrs).get("class", "") or ""
            if "tenkz-equation" in classes.split():
                assert not self.in_paragraph, (
                    "generated source places a tenkz equation inside a paragraph"
                )
                self.wrapper_count += 1
                self.events.append(("wrapper", ""))

    def handle_endtag(self, tag: str) -> None:
        if tag == "p":
            assert self.in_paragraph, "generated source closes an unopened paragraph"
            text = " ".join("".join(self.paragraph_parts).split())
            self.events.append(("paragraph", text))
            self.in_paragraph = False
            self.paragraph_parts = []

    def handle_data(self, data: str) -> None:
        if self.in_paragraph:
            self.paragraph_parts.append(data)


def _assert_generated_blocks(root: Path) -> None:
    """Check raw renderer output before a browser can repair invalid HTML."""
    parsers: dict[str, _GeneratedStructureParser] = {}
    for filename in PAGES:
        parser = _GeneratedStructureParser()
        parser.feed((root / filename).read_text(encoding="utf-8"))
        parser.close()
        assert not parser.in_paragraph, f"{filename} leaves a paragraph open"
        assert parser.wrapper_count == EXPECTED_WRAPPER_COUNTS[filename], (
            filename,
            parser.wrapper_count,
        )
        parsers[filename] = parser

    events = parsers["ch-mpdo_rfp.html"].events
    prose_boundaries = (
        (
            "Its two Kronecker factors are the two bare cups:",
            "This is the identity in",
        ),
        (
            "Applying this inverse map to the doubled physical index",
            "This is the single-block identity in",
        ),
    )
    for preceding, following in prose_boundaries:
        preceding_index = next(
            index
            for index, event in enumerate(events)
            if event[0] == "paragraph" and preceding in event[1]
        )
        following_index = next(
            index
            for index, event in enumerate(events)
            if event[0] == "paragraph" and following in event[1]
        )
        assert any(
            event[0] == "wrapper"
            for event in events[preceding_index + 1:following_index]
        ), (preceding, following)


def _equation_facts(page: Page) -> list[dict[str, object]]:
    return page.locator(".tenkz-equation").evaluate_all(
        """wrappers => wrappers.map(wrapper => {
          const pictures = [...wrapper.querySelectorAll(':scope .tenkz-pic')];
          const row = wrapper.querySelector(':scope > .tenkz-equation-row');
          return {
            pictureCount: pictures.length,
            directChildren: pictures.every(picture => picture.parentElement === row),
            insideMathJax: pictures.some(picture =>
              picture.closest('mjx-container, .MathJax, script[type^="math/tex"]')),
            visibleRawSource: /\\\\begin\\{tenkz(?:cd|lattice|planes|free)?\\}|\\\\tnpic/
              .test(wrapper.innerText),
          };
        })"""
    )


def _assert_desktop_rows(page: Page) -> None:
    facts = page.locator(".tenkz-equation").evaluate_all(
        """wrappers => wrappers.map(wrapper => {
          const row = wrapper.querySelector(':scope > .tenkz-equation-row');
          const rects = [...row.querySelectorAll(':scope > .tenkz-pic')]
            .map(picture => picture.getBoundingClientRect());
          const centers = rects.map(rect => rect.top + rect.height / 2);
          return {
            increasingX: rects.every((rect, i) => i === 0 || rect.left > rects[i - 1].left),
            sameRow: centers.every(center => Math.abs(center - centers[0]) <= 1),
            flexNowrap: getComputedStyle(row).display === 'flex'
              && getComputedStyle(row).flexWrap === 'nowrap',
          };
        })"""
    )
    assert all(fact["increasingX"] for fact in facts), facts
    assert all(fact["sameRow"] for fact in facts), facts
    assert all(fact["flexNowrap"] for fact in facts), facts


def _assert_mobile_scroll(page: Page) -> list[dict[str, object]]:
    facts = page.locator(".tenkz-equation").evaluate_all(
        """wrappers => wrappers.map(wrapper => {
          const row = wrapper.querySelector(':scope > .tenkz-equation-row');
          const pictures = [...wrapper.querySelectorAll('.tenkz-pic')];
          const rowElements = [...row.children];
          const first = row.firstElementChild;
          const last = row.lastElementChild;
          const parent = wrapper.parentElement;
          const figure = wrapper.closest('figure');
          const documentWidth = document.documentElement.clientWidth;
          wrapper.scrollLeft = 0;
          const wrapperAtStart = wrapper.getBoundingClientRect();
          const parentAtStart = parent === null ? null : parent.getBoundingClientRect();
          const firstAtStart = first.getBoundingClientRect();
          const allVisibleAtStart = rowElements.every(element => {
            const rect = element.getBoundingClientRect();
            return rect.left >= wrapperAtStart.left - 1
              && rect.right <= wrapperAtStart.right + 1;
          });
          const firstReachable = firstAtStart.left >= wrapperAtStart.left - 1
            && firstAtStart.right <= wrapperAtStart.right + 1;
          wrapper.scrollLeft = wrapper.scrollWidth;
          const wrapperAtEnd = wrapper.getBoundingClientRect();
          const lastAtEnd = last.getBoundingClientRect();
          const lastReachable = lastAtEnd.left >= wrapperAtEnd.left - 1
            && lastAtEnd.right <= wrapperAtEnd.right + 1;
          const localScroll = wrapper.scrollWidth > wrapper.clientWidth + 1;
          const contained = wrapperAtStart.left >= -1
            && wrapperAtStart.right <= documentWidth + 1
            && wrapper.clientWidth <= documentWidth + 1
            && (parentAtStart === null
              || (wrapperAtStart.left >= parentAtStart.left - 1
                && wrapperAtStart.right <= parentAtStart.right + 1));
          const figureScroll = figure !== null
            && figure.scrollWidth > figure.clientWidth + 1;
          const round = value => Math.round(value * 10) / 10;
          wrapper.scrollLeft = 0;
          return {
            pictureCount: pictures.length,
            contained,
            localScroll,
            firstReachable,
            lastReachable,
            allVisibleAtStart,
            wrapperLeft: round(wrapperAtStart.left),
            wrapperRight: round(wrapperAtStart.right),
            wrapperWidth: wrapper.clientWidth,
            wrapperScrollWidth: wrapper.scrollWidth,
            rowWidth: round(row.getBoundingClientRect().width),
            parentClass: parent === null ? null : parent.className,
            parentWidth: parent === null ? null : parent.clientWidth,
            parentScrollWidth: parent === null ? null : parent.scrollWidth,
            figureWidth: figure === null ? null : figure.clientWidth,
            figureScrollWidth: figure === null ? null : figure.scrollWidth,
            figureScroll,
          };
        })"""
    )
    assert all(fact["contained"] for fact in facts), facts
    assert not any(fact["figureScroll"] for fact in facts), facts
    assert all(
        fact["localScroll"]
        or fact["allVisibleAtStart"]
        for fact in facts
    ), facts
    assert all(
        fact["firstReachable"] and fact["lastReachable"]
        if fact["localScroll"]
        else fact["allVisibleAtStart"]
        for fact in facts
    ), facts
    document_facts = page.evaluate(
        """() => ({
          scrollWidth: document.documentElement.scrollWidth,
          clientWidth: document.documentElement.clientWidth,
        })"""
    )
    assert document_facts["scrollWidth"] <= document_facts["clientWidth"] + 1, document_facts
    return facts


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--web-root", type=Path, default=Path("blueprint/web"))
    parser.add_argument("--screenshot-dir", type=Path)
    args = parser.parse_args()
    root = args.web_root.resolve()
    repo_root = Path(__file__).resolve().parent.parent
    _assert_source_linked_groups(repo_root)
    for filename in PAGES:
        if not (root / filename).is_file():
            parser.error(f"missing generated blueprint page: {root / filename}")
    if args.screenshot_dir:
        args.screenshot_dir.mkdir(parents=True, exist_ok=True)
    _assert_generated_blocks(root)

    collected: list[dict[str, object]] = []
    mobile: list[dict[str, object]] = []
    with serve(root) as base_url, sync_playwright() as playwright:
        browser = playwright.chromium.launch()
        page = browser.new_page(viewport={"width": 1440, "height": 1000})
        for filename in PAGES:
            page.goto(f"{base_url}/{filename}", wait_until="load")
            # Several source-linked rows live in proofs, which the blueprint UI
            # collapses by default.  Reveal them so geometry is measured rather
            # than inferred from zero-sized hidden descendants.
            page.add_style_tag(content=".proof_content { display: block !important; }")
            page.locator(".tenkz-equation").first.wait_for(state="visible")
            collected.extend(_equation_facts(page))
            _assert_desktop_rows(page)
            if args.screenshot_dir:
                for index, wrapper in enumerate(page.locator(".tenkz-equation").all(), 1):
                    wrapper.screenshot(
                        path=args.screenshot_dir
                        / f"{Path(filename).stem}-{index}-desktop.png"
                    )

            page.set_viewport_size({"width": 360, "height": 800})
            mobile.extend(_assert_mobile_scroll(page))
            if args.screenshot_dir:
                for index, wrapper in enumerate(page.locator(".tenkz-equation").all(), 1):
                    wrapper.screenshot(
                        path=args.screenshot_dir
                        / f"{Path(filename).stem}-{index}-mobile.png"
                    )
            page.set_viewport_size({"width": 1440, "height": 1000})
        browser.close()

    picture_counts = [fact["pictureCount"] for fact in collected]
    assert picture_counts == EXPECTED_PICTURE_COUNTS, picture_counts
    assert all(fact["directChildren"] for fact in collected), collected
    assert not any(fact["insideMathJax"] for fact in collected), collected
    assert not any(fact["visibleRawSource"] for fact in collected), collected
    print(json.dumps({
        "equations": len(collected),
        "picture_counts": picture_counts,
        "mobile": mobile,
    }))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
