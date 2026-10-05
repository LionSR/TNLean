#!/usr/bin/env python3
"""Exercise indexed search, deployment prefixes and bounded result layout.

Run after add_blueprint_search.py. A small fixture makes navigation exclusion,
chapter titles and multi-page result scrolling deterministic; the final smoke
check searches the actual generated blueprint, too.
"""

from __future__ import annotations

import argparse
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from urllib.parse import unquote, urlsplit

from playwright.sync_api import Page, expect, sync_playwright

from test_tenkz_equation_web import _cdn_fetch, serve

SCRIPTS = Path(__file__).resolve().parent


def _fixture(root: Path, web_root: Path) -> None:
    root.mkdir(parents=True)
    (root / 'styles').mkdir()
    for name in ('theme-white.css', 'dep_graph.css', 'extra_styles.css'):
        shutil.copy2(web_root / 'styles' / name, root / 'styles' / name)
    for i in range(8):
        (root / f'chapter-{i}.html').write_text(
            '<!doctype html><html lang="en"><head>'
            f'<title>Chapter {i}</title><meta name="viewport" content="width=device-width">'
            '<link rel="stylesheet" href="styles/theme-white.css">'
            '<link rel="stylesheet" href="styles/extra_styles.css"></head><body>'
            '<header><h1 id="doc_title">Shared site heading</h1></header>'
            '<div class="wrapper"><div class="content"><div class="content-wrapper">'
            '<nav>Navigationonlyword</nav><div class="main-text">'
            f'<h1>Chapter {i}</h1><h2 id="canonical">Canonical forms</h2>'
            '<p>Sharedneedle appears in every chapter, with enough text for a '
            'readable excerpt explaining the canonical forms of tensor networks.</p>'
            '</div></div></div></div></body></html>', encoding='utf-8')
    (root / 'index.html').write_text(
        '<!doctype html><html lang="en"><head><title>Graphs</title></head>'
        '<body>Graphonlyword</body></html>', encoding='utf-8')
    (root / 'graph.html').write_text(
        '<!doctype html><html lang="en"><head><title>Dependency graph</title>'
        '<meta name="viewport" content="width=device-width">'
        '<link rel="stylesheet" href="styles/theme-white.css">'
        '<link rel="stylesheet" href="styles/dep_graph.css">'
        '<link rel="stylesheet" href="styles/extra_styles.css"></head><body>'
        '<header><a href="index.html">Home</a><h1 id="doc_title">Dependencies</h1></header>'
        '<div class="wrapper"><div class="content"><div id="graph">'
        'Graphonlyword</div></div></div></body></html>', encoding='utf-8')
    command = [sys.executable, str(SCRIPTS / 'add_blueprint_search.py'), '--web-root', str(root)]
    subprocess.run(command, check=True)
    first = {p.name: p.read_bytes() for p in root.glob('*.html')}
    subprocess.run(command, check=True)
    assert first == {p.name: p.read_bytes() for p in root.glob('*.html')}, 'rerun changed HTML'


def _search(page: Page, term: str) -> None:
    field = page.locator('#blueprint-search input')
    field.fill(term)
    expect(page.locator('.pagefind-ui__message')).to_contain_text(
        f'results for {term}', timeout=30_000)
    # The result count arrives before the asynchronously loaded excerpts.
    if term == 'sharedneedle' or term == 'injective':
        expect(page.locator('.pagefind-ui__result-link').first).to_be_visible(timeout=30_000)
        expect(page.locator('.pagefind-ui__result-excerpt').first).to_contain_text(
            term, ignore_case=True, timeout=30_000)


def _assert_links(page: Page, site_url: str) -> None:
    links = page.locator('.pagefind-ui__result-link').evaluate_all('(xs) => xs.map(x => x.href)')
    assert links, 'search returned no links'
    assert all(url.startswith(site_url + '/') for url in links), links
    for url in links:
        response = page.request.get(url)
        assert response.ok, (url, response.status)
    # Follow a section result, checking the fragment as well as the HTTP path.
    target = page.locator('.pagefind-ui__result-link[href*="#"]').first
    expect(target).to_be_visible()
    url = target.evaluate('(x) => x.href')
    target.click()
    page.wait_for_url(url, timeout=30_000)
    fragment = unquote(urlsplit(url).fragment)
    assert page.evaluate('(id) => !!document.getElementById(id)', fragment), url


def _assert_layout(page: Page) -> None:
    facts = page.evaluate('''() => {
      const root = document.documentElement;
      const drawer = document.querySelector('.pagefind-ui__drawer');
      const content = document.querySelector('.content');
      const header = document.querySelector('header').getBoundingClientRect();
      const heading = document.querySelector('#doc_title');
      const title = heading.getBoundingClientRect();
      const input = document.querySelector('#blueprint-search input').getBoundingClientRect();
      const box = drawer.getBoundingClientRect();
      return {width: root.clientWidth, scrollWidth: root.scrollWidth,
        drawerBottom: box.bottom, viewportHeight: innerHeight,
        drawerHeight: drawer.clientHeight, drawerScroll: drawer.scrollHeight,
        overflow: getComputedStyle(drawer).overflowY,
        contentHeight: content.getBoundingClientRect().height,
        contentTop: content.getBoundingClientRect().top, headerBottom: header.bottom,
        titleBottom: title.bottom, titleWidth: title.width, titleHeight: title.height,
        titleFont: getComputedStyle(heading).font, inputTop: input.top};
    }''')
    # A broken browser/font combination can collapse text to a 0x0 box while
    # the rest of the page still lays out. Diagnose that before overlap checks.
    assert facts['titleWidth'] > 0 and facts['titleHeight'] > 0, facts
    assert facts['scrollWidth'] <= facts['width'] + 1, facts
    assert facts['drawerBottom'] <= facts['viewportHeight'], facts
    assert facts['contentHeight'] > 100, facts
    assert facts['drawerBottom'] <= facts['headerBottom'] + 1, facts
    assert facts['contentTop'] >= facts['headerBottom'] - 1, facts
    assert facts['titleBottom'] <= facts['inputTop'] + 1, facts
    assert facts['drawerHeight'] < facts['drawerScroll'], facts
    assert facts['overflow'] in ('auto', 'scroll'), facts


def _fixture_browser(browser, site_url: str) -> None:
    for width in (360, 1440):
        page = browser.new_page(viewport={'width': width, 'height': 800})
        errors = []
        page.on('pageerror', lambda error: errors.append(str(error)))
        page.goto(site_url + '/chapter-0.html')
        _search(page, 'sharedneedle')
        expect(page.locator('.pagefind-ui__result-link').first).to_contain_text('Chapter')
        _assert_layout(page)
        _assert_links(page, site_url)
        _search(page, 'sharedneedle')
        page.locator('#blueprint-search input').press('Escape')
        expect(page.locator('.pagefind-ui__drawer')).to_be_hidden()
        _search(page, 'sharedneedle')
        page.locator('.pagefind-ui__search-clear').click()
        expect(page.locator('#blueprint-search input')).to_have_value('')
        expect(page.locator('.pagefind-ui__drawer')).to_be_hidden()
        for term in ('navigationonlyword', 'graphonlyword', 'unfindableword'):
            _search(page, term)
            expect(page.locator('.pagefind-ui__message')).to_have_text(f'No results for {term}')
        # Search remains available on unindexed, headerless utility pages.
        page.goto(site_url + '/index.html')
        _search(page, 'sharedneedle')
        # Graph pages use a different fixed-height, absolutely-positioned header.
        page.goto(site_url + '/graph.html')
        _search(page, 'sharedneedle')
        _assert_layout(page)
        assert not errors, errors
        page.close()


def _generated_browser(browser, web_root: Path) -> None:
    # Serving the repository's parent gives the real blueprint at /blueprint/web/,
    # so a deployment-prefix regression cannot hide behind a root-only test.
    with serve(web_root.parent.parent) as base:
        site_url = f'{base}/{web_root.parent.name}/{web_root.name}'
        page = browser.new_page(viewport={'width': 360, 'height': 800})
        assets = {}

        def external(route):
            url = route.request.url
            if url not in assets:
                assets[url] = _cdn_fetch(url)
            body, content_type = assets[url]
            route.fulfill(body=body, content_type=content_type,
                          headers={'Access-Control-Allow-Origin': '*'})

        page.route('https://cdn.jsdelivr.net/**', external)
        page.goto(site_url + '/ch-mps.html', wait_until='domcontentloaded', timeout=120_000)
        _search(page, 'injective')
        _assert_links(page, site_url)
        page.goto(site_url + '/dep_graph_chapter_2.html', wait_until='domcontentloaded', timeout=120_000)
        _search(page, 'injective')
        _assert_layout(page)
        page.close()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--web-root', type=Path, default=Path('blueprint/web'))
    args = parser.parse_args()
    root = args.web_root.resolve()
    pages = sorted(root.glob('*.html'))
    assert pages, f'no generated pages under {root}'
    for page in pages:
        source = page.read_text(encoding='utf-8')
        assert source.count('id="blueprint-search"') == 1, page.name
        for asset in ('pagefind-ui.js', 'pagefind-ui.css'):
            assert f'pagefind/{asset}' in source, (page.name, asset)
    with tempfile.TemporaryDirectory() as temporary, sync_playwright() as playwright:
        parent = Path(temporary)
        fixture = parent / 'TNLean' / 'blueprint'
        _fixture(fixture, root)
        browser = playwright.chromium.launch()
        try:
            with serve(fixture) as base:
                _fixture_browser(browser, base)
            with serve(parent) as base:
                _fixture_browser(browser, base + '/TNLean/blueprint')
            _generated_browser(browser, root)
        finally:
            browser.close()
    print(f'Search assets checked on {len(pages)} pages; root/subpath browser regressions passed')


if __name__ == '__main__':
    main()
