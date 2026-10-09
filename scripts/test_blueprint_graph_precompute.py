#!/usr/bin/env python3
"""Precomputed-route regressions, separate from mandatory live-worker coverage.

--browser-smoke forces only the tiny pinned fixture through precomputation and
checks real interactions and setup failures. Normal invocation uses no browser.
The graph reader keeps its original 300-second deadline.
"""

from __future__ import annotations

import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
import xml.etree.ElementTree as ET

from test_blueprint_graph_worker import (
    _browser_page, _fixture_source, _write_fixture, reader, renderer,
)


class GraphPrecomputationTests(unittest.TestCase):
    def test_precomputed_page_keeps_statements_and_ready_contract(self):
        source = _fixture_source()
        prepared = renderer._precompute_dependency_graph(source)
        self.assertIn(renderer._GRAPH_PRECOMPUTED, prepared)
        self.assertNotIn(".renderDot(`", prepared)
        self.assertIn('dataset.graphvizReady = "true"', prepared)
        for name in ("a", "b", "c"):
            self.assertIn(f"<title>{name}</title>", prepared)
            self.assertIn(f'id="{name}_modal"', prepared)
        start = prepared.index("<svg ", prepared.index(renderer._GRAPH_PRECOMPUTED))
        end = prepared.index("</svg>", start) + len("</svg>")
        svg = ET.fromstring(prepared[start:end])
        self.assertEqual(sorted(title.text for title in svg.findall(
            './/svg:g[@class="edge"]/svg:title', renderer._SVG_NS)), ["a->b", "b->c"])
        self.assertIn('.scaleExtent([0.1, 10])', prepared)
        self.assertIn('<svg width="100%" height="100%"', prepared)
        self.assertEqual(renderer._precompute_dependency_graph(prepared), prepared)

    def test_repeated_callback_rejects_altered_or_truncated_output(self):
        prepared = renderer._precompute_dependency_graph(_fixture_source())
        changed = prepared.replace('stroke="black"', 'stroke="red"', 1)
        self.assertNotEqual(prepared, changed)
        with self.assertRaisesRegex(ValueError, "SVG was altered"):
            renderer._precompute_dependency_graph(changed)
        with self.assertRaisesRegex(ValueError, "Incomplete precomputed"):
            renderer._precompute_dependency_graph(prepared[:-20])

    def test_changed_current_dot_is_rendered_fresh(self):
        source = _fixture_source()
        changed = source.replace('a [label="a"]', 'a [label="changed"]')
        self.assertNotEqual(source, changed)
        with patch.object(renderer, "_render_dependency_graph",
                          wraps=renderer._render_dependency_graph) as render:
            original = renderer._precompute_dependency_graph(source)
            prepared = renderer._precompute_dependency_graph(changed)
        self.assertEqual(render.call_count, 2)
        self.assertNotIn(">changed</text>", original)
        self.assertIn(">changed</text>", prepared)

    def test_unrelated_html_is_retained_exactly(self):
        source = renderer._prepare_dependency_graph(_fixture_source())
        prepared = renderer._precompute_dependency_graph(source)
        before, after = source.split('<div id="graph"></div>', 1)
        self.assertTrue(prepared.startswith(before + renderer._GRAPH_PRECOMPUTED))
        original_modals = after.split(renderer._GRAPH_DIAGNOSTIC_START, 1)[0]
        self.assertIn(original_modals, prepared)
        unchanged_tail = source[source.index("latexLabelEscaper = function"):]
        self.assertTrue(prepared.endswith(unchanged_tail))

    def test_missing_nodes_edges_and_visible_content_fail(self):
        source = renderer._prepare_dependency_graph(_fixture_source())
        dot, svg = renderer._render_dependency_graph(source)
        namespace = renderer._SVG_NS
        for kind in ("node", "edge"):
            with self.subTest(kind=kind):
                root = ET.fromstring(svg)
                graph = root.find("svg:g", namespace)
                graph.remove(graph.find(f'svg:g[@class="{kind}"]', namespace))
                with self.assertRaisesRegex(ValueError, f"{kind} identities"):
                    renderer._validate_dependency_graph_svg(
                        dot, ET.tostring(root, encoding="unicode"), source)
        root = ET.fromstring(svg)
        for parent in root.iter():
            for child in list(parent):
                if child.tag.rsplit("}", 1)[-1] in ("ellipse", "polygon", "path", "text"):
                    parent.remove(child)
        with self.assertRaisesRegex(ValueError, "visible shape or label"):
            renderer._validate_dependency_graph_svg(
                dot, ET.tostring(root, encoding="unicode"), source)

    def test_bad_bounds_and_missing_modals_fail(self):
        source = renderer._prepare_dependency_graph(_fixture_source())
        dot, svg = renderer._render_dependency_graph(source)
        root = ET.fromstring(svg)
        root.set("viewBox", "0 0 nan 20")
        with self.assertRaisesRegex(ValueError, "bounds"):
            renderer._validate_dependency_graph_svg(
                dot, ET.tostring(root, encoding="unicode"), source)
        with self.assertRaisesRegex(ValueError, "statement modal"):
            renderer._validate_dependency_graph_svg(
                dot, svg, source.replace('id="a_modal"', 'id="missing_modal"'))

    def test_layout_failure_is_not_replaced_by_an_empty_graph(self):
        with patch.object(renderer, "_render_dependency_graph",
                          side_effect=RuntimeError("layout failed")):
            with self.assertRaisesRegex(RuntimeError, "layout failed"):
                renderer._precompute_dependency_graph(_fixture_source())

    def test_decode_only_does_not_load_layout_assets(self):
        source = _fixture_source()
        # An absent bundle must not matter when only decoding the DOT literal.
        with patch.object(renderer.plastexdepgraph, "__file__", "/absent/__init__.py"):
            data = renderer._dependency_graph_data(source, layout=False)
        self.assertEqual(set(data), {"dot"})
        self.assertIn("a -> b; b -> c;", data["dot"])

    def test_literal_decoding_matches_javascript_and_rejects_code(self):
        literal = r'.renderDot(`strict digraph { "a\\b" [label="line\\nnext"]; }`)'
        expected = r'strict digraph { "a\b" [label="line\nnext"]; }'
        self.assertEqual(renderer._dependency_graph_data(literal, layout=False)["dot"], expected)
        for source in ('.renderDot(`${process.exit(0)}`)', '.renderDot(`unfinished',
                       '.renderDot(`one`) .renderDot(`two`)', '.renderDot(`x` + `y`)'):
            with self.subTest(source=source), self.assertRaises(RuntimeError):
                renderer._dependency_graph_data(source, layout=False)

    def test_routing_boundaries_use_actual_decoded_dot(self):
        source = _fixture_source()
        old_dot = renderer._dependency_graph_data(source, layout=False)["dot"]
        for nodes, edges, precompute in (
                (999, 1499, False), (1000, 1500, False),
                (1001, 0, True), (1000, 1501, True), (1001, 1501, True)):
            # Non-strict DOT deliberately includes parallel edges: each counts.
            dot = "digraph { " + "; ".join(f"n{i}" for i in range(nodes))
            dot += "; " + "n0 -> n1; " * edges + "}"
            changed = source.replace(old_dot, dot)
            self.assertNotEqual(changed, source)
            with self.subTest(nodes=nodes, edges=edges), patch.object(
                    renderer, "_precompute_dependency_graph", return_value="large route") as render:
                routed = renderer._route_dependency_graph(changed)
                self.assertEqual(render.call_count, int(precompute))
                self.assertEqual(routed, "large route" if precompute else
                                 renderer._prepare_dependency_graph(changed))

    def test_source_name_does_not_select_route_and_small_output_is_unchanged(self):
        source = _fixture_source()
        for name in ("dep_graph_document.html", "dep_graph_chapter_24.html", "tiny fixture"):
            changed = source.replace("Small dependency graph", name)
            with patch.object(renderer, "_render_dependency_graph") as render:
                self.assertEqual(renderer._route_dependency_graph(changed),
                                 renderer._prepare_dependency_graph(changed))
                render.assert_not_called()

    def test_helper_failure_and_generation_bound_propagate(self):
        with patch.object(renderer.shutil, "which", return_value=None):
            with self.assertRaisesRegex(RuntimeError, "Node.js 18"):
                renderer._route_dependency_graph(_fixture_source())
        with patch.object(renderer.subprocess, "run", side_effect=
                          subprocess.TimeoutExpired("node", 600)) as run:
            with self.assertRaises(subprocess.TimeoutExpired):
                renderer._render_dependency_graph(_fixture_source())
            self.assertEqual(run.call_args.kwargs["timeout"], 600)
        failure = subprocess.CompletedProcess("node", 1, "", "layout failure")
        with patch.object(renderer.subprocess, "run", return_value=failure):
            with self.assertRaisesRegex(RuntimeError, "layout failure"):
                renderer._render_dependency_graph(_fixture_source())
        with patch.object(renderer.subprocess, "run", return_value=
                          subprocess.CompletedProcess("node", 0, "not JSON", "")):
            with self.assertRaises(json.JSONDecodeError):
                renderer._render_dependency_graph(_fixture_source())

    def test_active_svg_and_empty_edge_path_fail(self):
        source = _fixture_source()
        dot, svg = renderer._render_dependency_graph(source)
        for kind in ("script", "SCRIPT", "foreignObject", "FoReIgNoBjEcT",
                     "onclick", "empty path"):
            root = ET.fromstring(svg)
            if kind == "onclick":
                root.set(kind, "alert(1)")
            elif kind == "empty path":
                root.find('.//svg:g[@class="edge"]/svg:path', renderer._SVG_NS).set("d", "")
            else:
                ET.SubElement(root, "{http://www.w3.org/2000/svg}" + kind)
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                renderer._validate_dependency_graph_svg(
                    dot, ET.tostring(root, encoding="unicode"), source)

    def test_precomputed_phases_are_honest_and_readiness_follows_interactions(self):
        prepared = renderer._precompute_dependency_graph(_fixture_source())
        self.assertIn(renderer._GRAPH_DIAGNOSTICS, prepared)
        self.assertNotIn('graphPhase("initializing")', prepared)
        self.assertNotIn('graphviz.onerror(', prepared)
        phases = ['graphPhase("precomputed-loaded")', 'graphSvg.call(graphZoom)',
                  'graphPhase("interactionStart")', 'interactive();',
                  'dataset.graphvizReady = "true"', 'graphPhase("complete")']
        positions = [prepared.index(phase) for phase in phases]
        self.assertEqual(positions, sorted(positions))
        self.assertIn('delete graphElement.dataset.graphvizReady;', prepared)
        self.assertIn('graphFailure(error);', prepared)

    def test_active_urls_fail_and_ordinary_links_are_preserved(self):
        source = _fixture_source()
        dot, svg = renderer._render_dependency_graph(source)
        for attribute in ("href", "{http://www.w3.org/1999/xlink}href"):
            for url in ("javascript:alert(1)", " \tJaVa\nScRiPt:alert(1)",
                        "vbscript:msgbox(1)", "data:text/html,<script>bad</script>",
                        "DATA:image/svg+xml;base64,PHN2Zz4=",
                        "data:application/xhtml+xml,<html/>",
                        "data:text/xml,<xml/>", "data:application/xml,<xml/>"):
                root = ET.fromstring(svg)
                ET.SubElement(root, "{http://www.w3.org/2000/svg}a", {attribute: url})
                with self.subTest(attribute=attribute, url=url), self.assertRaisesRegex(
                        ValueError, "active URL"):
                    renderer._validate_dependency_graph_svg(
                        dot, ET.tostring(root, encoding="unicode"), source)
            for url in ("chapter.html#a", "#a_modal", "https://example.org/statement",
                        "../docs/find/#doc/Example", "data:image/png;base64,aGVsbG8="):
                root = ET.fromstring(svg)
                link = ET.SubElement(root, "{http://www.w3.org/2000/svg}a", {attribute: url})
                with self.subTest(attribute=attribute, url=url):
                    self.assertEqual(renderer._validate_dependency_graph_svg(
                        dot, ET.tostring(root, encoding="unicode"), source), (3, 2))
                    self.assertEqual(link.get(attribute), url)


_PRECOMPUTED_SNAPSHOT = """() => {
  const graph = document.getElementById('graph');
  const svg = graph.querySelector('svg');
  return {
    precomputed: graph.dataset.graphvizPrecomputed === 'true',
    mode: graph.dataset.graphvizMode,
    worker: !!graph.__graphviz__?._worker,
    ready: graph.dataset.graphvizReady === 'true',
    phase: graph.dataset.graphvizPhase,
    error: graph.dataset.graphvizError || '',
    svg: !!svg,
    nodes: graph.querySelectorAll('svg .node').length,
    edges: graph.querySelectorAll('svg .edge').length,
    labels: [...graph.querySelectorAll('svg .node text')]
      .map(node => node.textContent).sort(),
    zoom: svg && d3.zoomTransform(svg).toString()
  };
}"""


def _browser_smoke() -> None:
    """Force a tiny graph through the large route; preserve worker smoke tests."""
    from playwright.sync_api import sync_playwright

    results = {}
    with tempfile.TemporaryDirectory(prefix="tnlean-precomputed-smoke-") as temporary:
        root = Path(temporary)
        generated = _write_fixture(root)
        source = renderer._precompute_dependency_graph(_fixture_source())
        generated.write_text(source, encoding="utf-8")
        with reader.serve(root) as base_url, sync_playwright() as playwright:
            browser = playwright.chromium.launch(timeout=30_000)
            try:
                for width in (1280, 390):
                    with _browser_page(browser, base_url) as (page, blocked, errors):
                        page.set_viewport_size({"width": width, "height": 900})
                        with patch.object(reader, "PAGE_LOAD_TIMEOUT_MS", 30_000):
                            reader._load_page(page, base_url, generated.name)
                        complete = page.evaluate(_PRECOMPUTED_SNAPSHOT)
                        assert complete["precomputed"] and complete["mode"] == "precomputed", complete
                        assert not complete["worker"] and complete["ready"] and complete["svg"], complete
                        assert complete["phase"] == "complete" and not complete["error"], complete
                        assert complete["nodes"] == 3 and complete["edges"] == 2, complete
                        assert complete["labels"] == ["a", "b", "c"], complete
                        svg = page.locator("#graph svg")
                        box = svg.bounding_box()
                        assert box and box["width"] > 0 and box["height"] > 0, box
                        assert box["width"] <= width, box
                        page.locator("#graph g.node").filter(
                            has=page.locator("title", has_text="a")).click()
                        modal = page.locator("#a_modal")
                        assert modal.is_visible(), "Node click did not open its statement"
                        assert modal.locator('a[href="index.html#a"]').count() > 0
                        modal.locator(".dep-closebtn").click()
                        assert not modal.is_visible(), "Statement did not close"
                        # Exercise actual browser wheel and pointer handlers.
                        x, y = box["x"] + box["width"] / 2, box["y"] + box["height"] / 2
                        page.mouse.move(x, y)
                        page.mouse.wheel(0, -200)
                        page.wait_for_function("before => d3.zoomTransform(document.querySelector('#graph svg')).toString() !== before",
                                               arg=complete["zoom"])
                        zoomed = page.evaluate(_PRECOMPUTED_SNAPSHOT)["zoom"]
                        page.mouse.move(x, y)
                        page.mouse.down()
                        page.mouse.move(x + 20, y + 20, steps=5)
                        page.mouse.up()
                        panned = page.evaluate(_PRECOMPUTED_SNAPSHOT)["zoom"]
                        assert panned != zoomed, (zoomed, panned)
                        assert not blocked and not errors, (blocked, errors)
                        results[str(width)] = {**complete, "zoomed": zoomed, "panned": panned,
                                               "modal_open_close": True}

                failures = {
                    "structure": source.replace('class="node"', 'class="missing-node"', 1),
                    "zoom": source.replace('const graphZoom = d3.zoom()',
                        'const graphZoom = (() => { throw new Error("forced zoom failure"); })()', 1),
                    "interaction": source.replace('interactive();',
                        'throw new Error("forced interaction failure");', 1),
                }
                for kind, changed in failures.items():
                    assert changed != source, kind
                    generated.write_text(changed, encoding="utf-8")
                    with _browser_page(browser, base_url) as (page, blocked, errors):
                        try:
                            with patch.object(reader, "PAGE_LOAD_TIMEOUT_MS", 30_000):
                                reader._load_page(page, base_url, generated.name)
                        except RuntimeError as failure:
                            assert str(failure).startswith("Graphviz failed:"), str(failure)
                            assert generated.name in failure.__notes__[0], failure.__notes__
                            assert "[blueprint-graph] error" in failure.__notes__[0], failure.__notes__
                        else:
                            raise AssertionError(f"{kind} setup failure was accepted")
                        failed = page.evaluate(_PRECOMPUTED_SNAPSHOT)
                        assert failed["error"] and failed["phase"] == "error", failed
                        assert not failed["ready"] and not failed["worker"], failed
                        assert not blocked, blocked
                        results[kind] = failed
            finally:
                browser.close()
    print(json.dumps(results, sort_keys=True))


if __name__ == "__main__":
    if sys.argv[1:] == ["--browser-smoke"]:
        _browser_smoke()
    else:
        unittest.main()
