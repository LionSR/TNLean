#!/usr/bin/env python3
"""Source and deadline regressions for the pinned graph worker; no browser runs.

--write-fixture DIR creates a three-node page with the real bundled JavaScript
and WASM for a separately authorized, small browser check. It renders only the
pinned Jinja template, without parsing or building the blueprint.

--browser-smoke checks that graph and a malformed DOT graph in one browser.
The default tests use no browser.
"""

from __future__ import annotations

import contextlib
import importlib.metadata
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import plasTeX
import plastexdepgraph
from jinja2 import Template

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "blueprint/src/Packages"))
import tnlean_patches as renderer
import test_blueprint_web_render as reader

BUNDLE = Path(plastexdepgraph.__file__).resolve().parent


class _Statement:
    thmName = "lemma"
    caption = "Lemma"
    ref = title = None

    def __init__(self, name):
        self.id = name
        self.url = "index.html#" + name

    def __str__(self):
        return "<p>One statement in a small dependency graph.</p>"


def _fixture_source() -> str:
    template = (BUNDLE / "templates/dep_graph.html").read_text(encoding="utf-8")
    source = Template(template).render(
        context=SimpleNamespace(terms={}),
        config={"html5": {"theme-css": "white", "use-mathjax": False}},
        title="Small dependency graph", legend=[], extra_modal_links=[],
        graph=SimpleNamespace(nodes=[_Statement(name) for name in ("a", "b", "c")]),
        dot='strict digraph { a [label="a"]; b [label="b"]; c [label="c"]; a -> b; b -> c; }',
    )
    return source


def _write_fixture(root: Path) -> Path:
    """Copy the pinned browser assets without fetching or executing them."""
    root.mkdir(parents=True, exist_ok=True)
    (root / "js").mkdir(exist_ok=True)
    (root / "styles").mkdir(exist_ok=True)
    for name in ("d3.min.js", "hpcc.min.js", "d3-graphviz.js",
                 "expatlib.wasm", "graphvizlib.wasm"):
        shutil.copyfile(BUNDLE / "static" / name, root / "js" / name)
    theme = Path(plasTeX.__file__).resolve().parent / "Renderers/HTML5/Themes/default"
    shutil.copyfile(theme / "js/jquery.min.js", root / "js/jquery.min.js")
    shutil.copyfile(theme / "styles/theme-white.css", root / "styles/theme-white.css")
    shutil.copyfile(BUNDLE / "static/dep_graph.css", root / "styles/dep_graph.css")
    shutil.copyfile(theme / "symbol-defs.svg", root / "symbol-defs.svg")
    page = root / "dep_graph_document.html"
    page.write_text(renderer._prepare_dependency_graph(_fixture_source()), encoding="utf-8")
    return page


@contextlib.contextmanager
def _browser_page(browser, base_url):
    """Use only the temporary server, including for worker and WASM requests."""
    context = browser.new_context(viewport={"width": 1280, "height": 900})
    blocked = []
    errors = []

    def route(request_route):
        address = request_route.request.url
        if address.startswith(base_url + "/") or address.startswith(("blob:", "data:")):
            request_route.continue_()
        else:
            blocked.append(address)
            request_route.abort()

    context.route("**/*", route)
    page = context.new_page()
    page.set_default_timeout(30_000)
    page.on("pageerror", lambda error: errors.append(str(error)))
    try:
        yield page, blocked, errors
    finally:
        context.close()


_GRAPH_SNAPSHOT = """() => {
  const graph = document.getElementById('graph');
  return {
    worker: graph.__graphviz__._worker instanceof Worker,
    ready: graph.dataset.graphvizReady === 'true',
    phase: graph.dataset.graphvizPhase,
    error: graph.dataset.graphvizError || '',
    svg: !!graph.querySelector('svg'),
    nodes: graph.querySelectorAll('svg .node').length,
    edges: graph.querySelectorAll('svg .edge').length,
    labels: [...graph.querySelectorAll('svg .node title')]
      .map(node => node.textContent).sort()
  };
}"""


def _browser_smoke() -> None:
    """Check actual rendering and terminal errors without building the book."""
    from playwright.sync_api import sync_playwright

    results = {}
    with tempfile.TemporaryDirectory(prefix="tnlean-graph-smoke-") as temporary:
        root = Path(temporary)
        generated = _write_fixture(root)
        with reader.serve(root) as base_url, sync_playwright() as playwright:
            browser = playwright.chromium.launch(timeout=30_000)
            try:
                with _browser_page(browser, base_url) as (page, blocked, errors):
                    # Only the tiny test's local deadline changes. The reader's
                    # production 300-second budget is unchanged.
                    with patch.object(reader, "PAGE_LOAD_TIMEOUT_MS", 30_000):
                        reader._load_page(page, base_url, generated.name)
                    complete = page.evaluate(_GRAPH_SNAPSHOT)
                    assert complete["worker"] and complete["ready"] and complete["svg"], complete
                    assert complete["phase"] == "complete" and not complete["error"], complete
                    assert complete["nodes"] == 3 and complete["edges"] == 2, complete
                    assert complete["labels"] == ["a", "b", "c"], complete
                    assert not blocked and not errors, (blocked, errors)
                    results["complete"] = complete

                source = generated.read_text(encoding="utf-8")
                dot = 'strict digraph { a [label="a"]; b [label="b"]; c [label="c"]; a -> b; b -> c; }'
                assert source.count(dot) == 1, "Pinned fixture DOT changed"
                generated.write_text(source.replace(dot, 'strict digraph { a -> }', 1), encoding="utf-8")
                with _browser_page(browser, base_url) as (page, blocked, errors):
                    try:
                        with patch.object(reader, "PAGE_LOAD_TIMEOUT_MS", 30_000):
                            reader._load_page(page, base_url, generated.name)
                    except RuntimeError as failure:
                        assert str(failure).startswith("Graphviz failed:"), str(failure)
                        note = failure.__notes__[0]
                        assert generated.name in note and base_url in note, note
                        assert "[blueprint-graph] error" in note, note
                    else:
                        raise AssertionError("Malformed DOT was accepted as a completed graph")
                    failed = page.evaluate(_GRAPH_SNAPSHOT)
                    assert failed["worker"] and failed["error"] and failed["phase"] == "error", failed
                    assert not failed["ready"] and not failed["svg"], failed
                    assert not blocked and not errors, (blocked, errors)
                    results["malformed"] = failed
            finally:
                browser.close()
    print(json.dumps(results, sort_keys=True))


@contextlib.contextmanager
def _in_directory(path):
    previous = Path.cwd()
    os.chdir(path)
    try:
        yield
    finally:
        os.chdir(previous)


class GraphSourceTests(unittest.TestCase):
    def test_exact_bundle_has_the_worker_selector_contract(self):
        self.assertEqual(importlib.metadata.version("plastexdepgraph"), "0.0.5")
        source = (BUNDLE / "static/d3-graphviz.js").read_text(encoding="utf-8")
        self.assertIn("attr('type') == 'javascript/worker'", source)
        self.assertIn("this._worker = new Worker(blobURL)", source)

    def test_small_upstream_page_retains_graph_and_adds_completion(self):
        source = _fixture_source()
        prepared = renderer._prepare_dependency_graph(source)
        self.assertEqual(prepared.count('src="js/hpcc.min.js"'), 1)
        self.assertIn('type="javascript/worker"', prepared)
        self.assertIn('graphviz({useWorker: true})', prepared)
        self.assertIn('dataset.graphvizReady = "true"', prepared)
        self.assertIn('graphviz.onerror(graphFailure)', prepared)
        self.assertIn('addEventListener("error"', prepared)
        self.assertIn('addEventListener("messageerror"', prepared)
        self.assertIn('graphviz.on(phase + ".diagnostics"', prepared)
        self.assertIn('graphPhase("complete")', prepared)
        for content in ('a -> b; b -> c;', '<div id="graph">', 'interactive();',
                        'One statement in a small dependency graph.'):
            self.assertIn(content, prepared)
        self.assertEqual(renderer._prepare_dependency_graph(prepared), prepared)

    def test_changed_or_duplicate_upstream_contract_fails(self):
        source = _fixture_source()
        for changed in (source.replace('src="js/hpcc.min.js"', 'src="js/other.js"'),
                        source.replace('.width(width)', '.width(100)'),
                        source.replace('.on("end", interactive);', ''),
                        source + '<script src="js/hpcc.min.js"></script>'):
            with self.subTest(changed=changed[-100:]):
                with self.assertRaises(ValueError):
                    renderer._prepare_dependency_graph(changed)

    def test_callback_covers_all_graphs_and_preserves_other_pages(self):
        source = _fixture_source()
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            names = ("dep_graph_document.html", "dep_graph_chapter_24.html",
                     "dep_graph_subset_test.html")
            for name in names:
                (root / name).write_text(source, encoding="utf-8")
            for name in ("dep_graphs.html", "chapter.html"):
                (root / name).write_text("ordinary page", encoding="utf-8")
            with _in_directory(root):
                self.assertEqual(renderer._prepare_dependency_graph_pages(None), [])
                renderer._prepare_dependency_graph_pages(None)
            for name in names:
                self.assertIn('type="javascript/worker"', (root / name).read_text())
            for name in ("dep_graphs.html", "chapter.html"):
                self.assertEqual((root / name).read_text(), "ordinary page")


class _Page:
    def __init__(self, failure=None, result=True, emitted=()):
        self.navigation = []
        self.waits = []
        self.failure = failure
        self.result = result
        self.emitted = emitted
        self.listeners = {}
        self.terminal = SimpleNamespace(
            json_value=lambda: self.result, dispose=lambda: None)

    def on(self, event, callback):
        self.listeners[event] = callback

    def remove_listener(self, event, callback):
        assert self.listeners.pop(event) is callback

    def goto(self, url, **options):
        self.navigation.append((url, options))
        for event, value in self.emitted:
            self.listeners[event](value)

    def wait_for_function(self, expression, **options):
        self.waits.append((expression, options))
        if self.failure:
            raise self.failure
        return self.terminal


class GraphDeadlineTests(unittest.TestCase):
    def test_navigation_and_graph_wait_share_original_budget(self):
        page = _Page()
        with patch.object(reader.time, "monotonic", side_effect=[100.0, 125.0]):
            reader._load_page(page, "http://local", "dep_graph_document.html")
        self.assertEqual(page.navigation[0][1]["timeout"], 300_000)
        self.assertEqual(page.waits[0][1]["timeout"], 275_000)
        self.assertIn("graph.dataset.graphvizReady === 'true'", page.waits[0][0])
        self.assertIn("graph.querySelector('svg')", page.waits[0][0])

    def test_chapter_and_graph_chooser_keep_original_navigation(self):
        for name in ("chapter.html", "dep_graphs.html"):
            page = _Page()
            with patch.object(reader.time, "monotonic", return_value=100.0):
                reader._load_page(page, "http://local", name)
            self.assertEqual(page.navigation[0][1]["timeout"], 300_000)
            self.assertEqual(page.waits, [])

    def test_exhausted_budget_is_not_replaced_by_a_fresh_timeout(self):
        page = _Page()
        with patch.object(reader.time, "monotonic", side_effect=[100.0, 401.0]):
            with self.assertRaisesRegex(TimeoutError, "original page deadline"):
                reader._load_page(page, "http://local", "dep_graph_chapter_24.html")
        self.assertEqual(page.waits, [])

    def test_unfinished_graph_failure_propagates(self):
        page = _Page(RuntimeError("graph remained unfinished"))
        with patch.object(reader.time, "monotonic", side_effect=[100.0, 110.0]):
            with self.assertRaisesRegex(RuntimeError, "graph remained unfinished"):
                reader._load_page(page, "http://local", "dep_graph_document.html")
        self.assertEqual(page.listeners, {})

    def test_timeout_names_page_url_phase_and_browser_errors(self):
        failure = TimeoutError("graph wait timed out")
        page = _Page(failure, emitted=(
            ("console", SimpleNamespace(type="info", text="[blueprint-graph] layoutStart")),
            ("worker", SimpleNamespace(url="blob:http://local/worker")),
            ("pageerror", RuntimeError("worker import failed")),
            ("console", SimpleNamespace(type="error", text="WASM fetch failed")),
        ))
        with patch.object(reader.time, "monotonic", side_effect=[100.0, 110.0]):
            with self.assertRaises(TimeoutError) as caught:
                reader._load_page(page, "http://local", "dep_graph_document.html")
        self.assertIs(caught.exception, failure)
        note = failure.__notes__[0]
        for detail in ("dep_graph_document.html", "http://local/dep_graph_document.html",
                       "layoutStart", "blob:http://local/worker", "worker import failed",
                       "WASM fetch failed"):
            self.assertIn(detail, note)
        self.assertEqual(page.listeners, {})

    def test_terminal_graph_error_fails_without_a_second_wait(self):
        page = _Page(result="Graphviz worker message could not be read")
        with patch.object(reader.time, "monotonic", side_effect=[100.0, 125.0]):
            with self.assertRaisesRegex(RuntimeError, "Graphviz failed") as caught:
                reader._load_page(page, "http://local", "dep_graph_chapter_24.html")
        self.assertEqual(len(page.waits), 1)
        self.assertEqual(page.waits[0][1]["timeout"], 275_000)
        self.assertIn("graph.dataset.graphvizError", page.waits[0][0])
        self.assertIn("Graphviz worker message could not be read", str(caught.exception))
        self.assertEqual(page.listeners, {})

    def test_diagnostic_history_bounds_event_count_and_text(self):
        failure = TimeoutError("graph wait timed out")
        page = _Page(failure, emitted=tuple(
            ("console", SimpleNamespace(type="error", text=f"event {i}: " + "x" * 4000))
            for i in range(25)
        ))
        with patch.object(reader.time, "monotonic", side_effect=[100.0, 110.0]):
            with self.assertRaises(TimeoutError):
                reader._load_page(page, "http://local", "dep_graph_document.html")
        events = json.loads(failure.__notes__[0].split("; events: ", 1)[1])
        self.assertEqual(len(events), 20)
        self.assertTrue(events[0].startswith("console.error: event 5:"))
        self.assertTrue(all(len(event) <= len("console.error: ") + 2000 for event in events))


if __name__ == "__main__":
    if len(sys.argv) == 3 and sys.argv[1] == "--write-fixture":
        print(_write_fixture(Path(sys.argv[2]).resolve()))
    elif sys.argv[1:] == ["--browser-smoke"]:
        _browser_smoke()
    else:
        unittest.main()
