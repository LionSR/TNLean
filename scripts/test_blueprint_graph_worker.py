#!/usr/bin/env python3
"""Source and deadline regressions for the pinned graph worker; no browser runs.

--write-fixture DIR creates a three-node page with the real bundled JavaScript
and WASM for a separately authorized, small browser check. It renders only the
pinned Jinja template, without parsing or building the blueprint.
"""

from __future__ import annotations

import contextlib
import importlib.metadata
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
        for content in ('a -> b; b -> c;', '<div id="graph">', 'interactive();',
                        'One statement in a small dependency graph.'):
            self.assertIn(content, prepared)
        self.assertEqual(renderer._prepare_dependency_graph(prepared), prepared)

    def test_changed_or_duplicate_upstream_contract_fails(self):
        source = _fixture_source()
        for changed in (source.replace('src="js/hpcc.min.js"', 'src="js/other.js"'),
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
    def __init__(self, failure=None):
        self.navigation = []
        self.waits = []
        self.failure = failure

    def goto(self, url, **options):
        self.navigation.append((url, options))

    def wait_for_function(self, expression, **options):
        self.waits.append((expression, options))
        if self.failure:
            raise self.failure


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


if __name__ == "__main__":
    if len(sys.argv) == 3 and sys.argv[1] == "--write-fixture":
        print(_write_fixture(Path(sys.argv[2]).resolve()))
    else:
        unittest.main()
