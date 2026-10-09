"""TNLean-local additions to the shared texra_patches plasTeX package.

The shared patch layer lives in the ``texra_blueprint`` plugin; this shim
carries the repair map entry for a ``\\lean`` declaration observed mangled
in #398 and dependency-graph preparation for pinned plastexdepgraph 0.0.5.
Large graphs use fresh build-time default-quality layout with its bundled
WASM; smaller graphs retain the live browser worker. The ``\\tenkzkernel`` declaration is registered by
``tenkz_pic``.
"""

from collections import Counter
import hashlib
import json
import math
from pathlib import Path
import re
import shutil
import subprocess
import xml.etree.ElementTree as ET

import plastexdepgraph
from pygraphviz import AGraph

from plasTeX.PackageResource import PackagePreCleanupCB
from texra_blueprint.Packages.texra_patches import DECL_REPLACEMENTS

# In-place mutation of the plugin's module-level dict is the documented
# extension point at the pinned texra-blueprint version; a version bump
# must re-verify that DECL_REPLACEMENTS stays a plain mutable dict.

DECL_REPLACEMENTS["MPSTensor.exponentialconvergenceofprimitive"] = (
    "MPSTensor.exponential_convergence_of_primitive"
)


# plastexdepgraph 0.0.5 requests a worker, but its bundled d3-graphviz only
# recognizes this script type for a local hpcc URL. The ordinary upstream
# tag otherwise makes the complete graph layout run on the browser thread.
_GRAPH_HPCC_TAG = '<script src="js/hpcc.min.js"></script>'
_GRAPH_WORKER_TAG = '<script src="js/hpcc.min.js" type="javascript/worker"></script>'
_GRAPH_RENDER_START = 'graphContainer.graphviz({useWorker: true})\n    .width(width)'
_GRAPH_DIAGNOSTICS = """const graphElement = graphContainer.node();
function graphPhase(phase) {
    graphElement.dataset.graphvizPhase = phase;
    console.info("[blueprint-graph] " + phase);
}
function graphFailure(error) {
    graphElement.dataset.graphvizError = String(error && error.message || error);
    graphPhase("error");
    console.error("[blueprint-graph] " + graphElement.dataset.graphvizError);
}
"""
_GRAPH_DIAGNOSTIC_START = _GRAPH_DIAGNOSTICS + """graphPhase("initializing");
const graphviz = graphContainer.graphviz({useWorker: true});
graphviz.onerror(graphFailure);
if (graphviz._worker) {
    graphviz._worker.addEventListener("error", function (event) {
        graphFailure(event.message || "Graphviz worker failed");
    });
    graphviz._worker.addEventListener("messageerror", function () {
        graphFailure("Graphviz worker message could not be read");
    });
}
for (const phase of ["initEnd", "layoutStart", "layoutEnd", "dataExtractEnd",
                     "dataProcessPass1End", "dataProcessPass2End",
                     "renderStart", "renderEnd"]) {
    graphviz.on(phase + ".diagnostics", function () { graphPhase(phase); });
}
graphviz
    .width(width)"""
_GRAPH_END_HANDLER = '.on("end", interactive);'
_GRAPH_READY_HANDLER = """.on("end", function () {
      try {
        interactive();
        graphElement.dataset.graphvizReady = "true";
        graphPhase("complete");
      } catch (error) {
        graphFailure(error);
        throw error;
      }
    });"""


def _prepare_dependency_graph(source: str) -> str:
    """Enable the bundled worker and record completion of graph interaction.

    These substitutions belong to the pinned upstream template. A changed
    template must be reviewed rather than silently losing the worker,
    completion check, or diagnostics.
    """
    if (source.count(_GRAPH_WORKER_TAG) == 1
            and source.count(_GRAPH_DIAGNOSTIC_START) == 1
            and source.count(_GRAPH_READY_HANDLER) == 1
            and _GRAPH_HPCC_TAG not in source and _GRAPH_END_HANDLER not in source
            and _GRAPH_RENDER_START not in source):
        return source
    if (source.count(_GRAPH_HPCC_TAG) != 1
            or source.count(_GRAPH_RENDER_START) != 1
            or source.count(_GRAPH_END_HANDLER) != 1
            or _GRAPH_WORKER_TAG in source or _GRAPH_READY_HANDLER in source
            or _GRAPH_DIAGNOSTIC_START in source):
        raise ValueError("Dependency graph differs from the pinned worker template")
    return source.replace(_GRAPH_HPCC_TAG, _GRAPH_WORKER_TAG, 1).replace(
        _GRAPH_RENDER_START, _GRAPH_DIAGNOSTIC_START, 1).replace(
        _GRAPH_END_HANDLER, _GRAPH_READY_HANDLER, 1)


# This marks output of this callback, never an input cache. Upstream emits the
# current DOT afresh on every build. A repeated callback in the same build can
# leave its already-produced page alone.
_GRAPH_PRECOMPUTED = '<div id="graph" data-graphviz-precomputed="true"'
_SVG_NS = {"svg": "http://www.w3.org/2000/svg"}
_GRAPH_LAYOUT_TIMEOUT_SECONDS = 600


def _dependency_graph_data(source: str, *, layout: bool) -> dict:
    """Decode the pinned literal and optionally render it with the same helper."""
    node = shutil.which("node")
    if node is None:
        raise RuntimeError("Dependency graph precomputation requires Node.js 18 or newer")
    assets = Path(plastexdepgraph.__file__).resolve().parent / "static"
    helper = Path(__file__).with_name("render_dependency_graph.cjs")
    result = subprocess.run(
        [node, str(helper)],
        input=json.dumps({"source": source, "assets": str(assets), "layout": layout}),
        text=True, capture_output=True, timeout=_GRAPH_LAYOUT_TIMEOUT_SECONDS,
        check=False,
    )
    if result.returncode:
        raise RuntimeError("Dependency graph helper failed: " + result.stderr[-4000:])
    return json.loads(result.stdout)


def _render_dependency_graph(source: str) -> tuple[str, str]:
    """Render the current page's DOT afresh, using the installed pinned bundle."""
    rendered = _dependency_graph_data(source, layout=True)
    return rendered["dot"], rendered["svg"]


def _route_dependency_graph(source: str) -> str:
    """Route by actual decoded DOT size, never by page or fixture name.

    These conservative thresholds include the measured slow full graph and
    some fast chapters. They are a routing policy, not a runtime guarantee:
    topology also affects layout cost. Both routes preserve default quality.
    Node.js >=18 is required for decoding; only the large route loads WASM.
    """
    if _GRAPH_PRECOMPUTED in source:
        return _precompute_dependency_graph(source)
    prepared = _prepare_dependency_graph(source)
    dot = _dependency_graph_data(prepared, layout=False)["dot"]
    graph = AGraph(string=dot)
    if len(graph.nodes()) > 1000 or len(graph.edges()) > 1500:
        return _precompute_dependency_graph(prepared)
    return prepared


def _validate_dependency_graph_svg(dot: str, svg: str, source: str) -> tuple[int, int]:
    """Reject missing identities or visible content before publishing the page.

    Freshness comes from rendering the current DOT directly above, not from
    accepting a saved SVG with matching IDs. All statement/modals/link markup
    stays in the source outside the two replacement regions.
    """
    graph = AGraph(string=dot)
    expected_nodes = Counter(str(node) for node in graph.nodes())
    expected_edges = Counter(str(edge[0]) + "->" + str(edge[1]) for edge in graph.edges())
    root = ET.fromstring(svg)
    if root.tag != "{http://www.w3.org/2000/svg}svg":
        raise ValueError("Graphviz did not return an SVG")
    bounds = [float(value) for value in root.get("viewBox", "").split()]
    if (len(root.findall('svg:g[@class="graph"]', _SVG_NS)) != 1
            or len(bounds) != 4 or not all(math.isfinite(value) for value in bounds)
            or bounds[2] <= 0 or bounds[3] <= 0):
        raise ValueError("Invalid dependency graph root or bounds")
    groups = {}
    for kind, expected in (("node", expected_nodes), ("edge", expected_edges)):
        groups[kind] = root.findall(f'.//svg:g[@class="{kind}"]', _SVG_NS)
        titles = [group.find("svg:title", _SVG_NS) for group in groups[kind]]
        if any(title is None for title in titles):
            raise ValueError(f"Dependency graph has a {kind} without a title")
        if Counter(title.text for title in titles) != expected:
            raise ValueError(f"Dependency graph changed {kind} identities")
    for group in groups["node"]:
        shape = any(group.findall(".//svg:" + tag, _SVG_NS)
                    for tag in ("ellipse", "polygon", "path", "rect"))
        label = any("".join(text.itertext()).strip()
                    for text in group.findall(".//svg:text", _SVG_NS))
        if not shape or not label:
            raise ValueError("Dependency graph node has no visible shape or label")
    for group in groups["edge"]:
        paths = group.findall(".//svg:path", _SVG_NS)
        if not paths or any(not path.get("d", "").strip() for path in paths):
            raise ValueError("Dependency graph edge has no visible path")
    # This consumes trusted Graphviz output, not arbitrary uploaded SVG.
    for element in root.iter():
        if (element.tag.rsplit("}", 1)[-1].lower() in ("script", "foreignobject")
                or any(key.lower().startswith("on") for key in element.attrib)):
            raise ValueError("Unexpected active content in dependency graph SVG")
        for key, value in element.attrib.items():
            if key.rsplit("}", 1)[-1].lower() not in ("href", "src"):
                continue
            # XML parsing has already decoded character references. Normalize
            # URL whitespace/control obfuscation, including namespaced href.
            url = re.sub(r"[\x00-\x20\x7f]", "", value).lower()
            media_type = url[5:].split(",", 1)[0].split(";", 1)[0]
            if (url.startswith(("javascript:", "vbscript:"))
                    or (url.startswith("data:") and media_type in (
                        "text/html", "application/xhtml+xml", "image/svg+xml",
                        "text/xml", "application/xml"))):
                raise ValueError("Unexpected active URL in dependency graph SVG")
    ids = set(re.findall(r'id="([^"]*)"', source))
    if any(name + "_modal" not in ids for name in expected_nodes):
        raise ValueError("Dependency graph node has no statement modal")
    return sum(expected_nodes.values()), sum(expected_edges.values())


def _precompute_dependency_graph(source: str) -> str:
    """Insert newly rendered SVG and keep the existing fit/zoom/modal behavior."""
    if _GRAPH_PRECOMPUTED in source:
        # Integrity check for a repeated callback, not a cross-build SVG cache.
        marker = re.search(re.escape(_GRAPH_PRECOMPUTED)
                           + r' data-svg-sha256="([0-9a-f]{64})">', source)
        if (source.count(_GRAPH_PRECOMPUTED) != 1 or marker is None
                or source.count('graphElement.dataset.graphvizReady = "true";') != 1
                or not source.rstrip().endswith("</html>")):
            raise ValueError("Incomplete precomputed dependency graph page")
        end = source.find("</svg>", marker.end())
        if end < 0:
            raise ValueError("Incomplete precomputed dependency graph SVG")
        inline_svg = source[marker.end():end + len("</svg>")]
        if hashlib.sha256(inline_svg.encode()).hexdigest() != marker[1]:
            raise ValueError("Precomputed dependency graph SVG was altered")
        return source
    prepared = _prepare_dependency_graph(source)
    dot, svg = _render_dependency_graph(prepared)
    node_count, edge_count = _validate_dependency_graph_svg(dot, svg, prepared)
    if prepared.count('<div id="graph"></div>') != 1:
        raise ValueError("Dependency graph container differs from the pinned template")
    start = prepared.index(_GRAPH_DIAGNOSTIC_START)
    end = prepared.index("\nlatexLabelEscaper = function", start)
    old = prepared[start:end]
    if old.count(".renderDot(`") != 1 or old.count(_GRAPH_READY_HANDLER) != 1:
        raise ValueError("Dependency graph render call differs from the pinned template")
    # The XML prolog/doctype do not belong inside HTML. Preserve SVG itself.
    svg_start = re.search(r"<svg\b", svg).start()
    inline_svg = svg[svg_start:svg.rindex("</svg>") + len("</svg>")]
    # Inline SVG exists before bootstrap runs. Constrain its presentation size
    # immediately, so its large intrinsic width cannot influence clientWidth.
    # The viewBox and every laid-out element remain exactly as Graphviz emitted.
    opening_end = inline_svg.index(">") + 1
    opening = inline_svg[:opening_end]
    for dimension in ("width", "height"):
        opening, count = re.subn(rf'\b{dimension}="[^"]*"',
                                 dimension + '="100%"', opening)
        if count != 1:
            raise ValueError("Unexpected Graphviz SVG presentation dimensions")
    inline_svg = opening + inline_svg[opening_end:]
    bootstrap = _GRAPH_DIAGNOSTICS + f'''try {{
graphElement.dataset.graphvizMode = "precomputed";
graphPhase("precomputed-loaded");
const graphSvg = graphContainer.select("svg");
const graphGroup = graphSvg.select("g.graph");
if (graphSvg.empty() || graphGroup.empty()
    || graphSvg.selectAll("g.node").size() !== {node_count}
    || graphSvg.selectAll("g.edge").size() !== {edge_count}) {{
  throw new Error("Dependency graph is missing structural content");
}}
const graphNodes = [...graphSvg.node().querySelectorAll("g.node")];
const graphEdges = [...graphSvg.node().querySelectorAll("g.edge")];
if (graphNodes.some(node => !node.querySelector("ellipse,polygon,path,rect")
    || !node.querySelector("text")?.textContent.trim())
    || graphEdges.some(edge => !edge.querySelector("path")?.getAttribute("d")?.trim())) {{
  throw new Error("Dependency graph is missing visible content");
}}
// Retaining viewBox is the existing fit(true), scale(1) behavior.
graphSvg.attr("width", width).attr("height", height);
const graphMatrix = graphGroup.node().transform.baseVal.consolidate().matrix;
if (graphMatrix.b !== 0 || graphMatrix.c !== 0
    || graphMatrix.a !== graphMatrix.d || graphMatrix.a <= 0) {{
  throw new Error("Unexpected Graphviz root transform");
}}
const graphZoom = d3.zoom()
  .scaleExtent([0.1, 10])
  .translateExtent([[-Infinity, -Infinity], [Infinity, Infinity]])
  .interpolate(d3.interpolate)
  .on("zoom", function () {{ graphGroup.attr("transform", d3.event.transform); }});
graphSvg.call(graphZoom);
graphSvg.call(graphZoom.transform,
  d3.zoomIdentity.translate(graphMatrix.e, graphMatrix.f).scale(graphMatrix.a));
graphPhase("interactionStart");
interactive();
graphElement.dataset.graphvizReady = "true";
graphPhase("complete");
}} catch (error) {{
  delete graphElement.dataset.graphvizReady;
  graphFailure(error);
  throw error;
}}

'''
    output = prepared[:start] + bootstrap + prepared[end:]
    digest = hashlib.sha256(inline_svg.encode()).hexdigest()
    container = _GRAPH_PRECOMPUTED + ' data-svg-sha256="' + digest + '">'
    return output.replace('<div id="graph"></div>', container + inline_svg + "</div>", 1)


def _prepare_dependency_graph_pages(document):
    """Run after upstream graph rendering and the graph-navigation callback."""
    for page in sorted(Path.cwd().glob("dep_graph_*.html")):
        source = page.read_text(encoding="utf-8")
        prepared = _route_dependency_graph(source)
        if prepared != source:
            page.write_text(prepared, encoding="utf-8")
    # The upstream callbacks already own the output-file inventory.
    return []


def ProcessOptions(options, document):  # noqa: N802 (plasTeX package hook)
    document.addPackageResource([
        PackagePreCleanupCB(data=_prepare_dependency_graph_pages)])
