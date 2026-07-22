#!/usr/bin/env python3
"""Browser regression for top-level tenkz equation rows in the blueprint."""

from __future__ import annotations

import argparse
import contextlib
import functools
import http.server
import json
import socketserver
import threading
from pathlib import Path

from playwright.sync_api import Page, sync_playwright


EXPECTED_PICTURE_COUNTS = [2, 3, 3, 2, 5, 1]
PAGES = ("ch-mpdo.html", "ch-mpdo_rfp.html")


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
    assert any(fact["localScroll"] for fact in facts), facts
    assert all(fact["contained"] for fact in facts), facts
    assert not any(fact["figureScroll"] for fact in facts), facts
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
    for filename in PAGES:
        if not (root / filename).is_file():
            parser.error(f"missing generated blueprint page: {root / filename}")
    if args.screenshot_dir:
        args.screenshot_dir.mkdir(parents=True, exist_ok=True)

    collected: list[dict[str, object]] = []
    mobile: list[dict[str, object]] = []
    with serve(root) as base_url, sync_playwright() as playwright:
        browser = playwright.chromium.launch()
        page = browser.new_page(viewport={"width": 1440, "height": 1000})
        for filename in PAGES:
            page.goto(f"{base_url}/{filename}", wait_until="load")
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
