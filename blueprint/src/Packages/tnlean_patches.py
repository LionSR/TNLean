"""TNLean-local additions to the shared texra_patches plasTeX package.

The shared patch layer lives in the ``texra_blueprint`` plugin; this shim
carries the repair map entry for a ``\\lean`` declaration observed mangled
in #398 and the dependency-graph worker correction needed by the pinned
plastexdepgraph 0.0.5. The ``\\tenkzkernel`` declaration is registered by
``tenkz_pic``.
"""

from pathlib import Path

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
_GRAPH_DIAGNOSTIC_START = """const graphElement = graphContainer.node();
function graphPhase(phase) {
    graphElement.dataset.graphvizPhase = phase;
    console.info("[blueprint-graph] " + phase);
}
function graphFailure(error) {
    graphElement.dataset.graphvizError = String(error && error.message || error);
    graphPhase("error");
    console.error("[blueprint-graph] " + graphElement.dataset.graphvizError);
}
graphPhase("initializing");
const graphviz = graphContainer.graphviz({useWorker: true});
graphviz.onerror(graphFailure);
// In plastexdepgraph 0.0.5's bundled d3-graphviz, selection_graphviz calls
// new Graphviz synchronously. Its constructor assigns _worker before
// initViz starts worker initialization and before returning the instance.
// Attach now: waiting for initEnd would miss initialization failures.
// The source regression checks this private-field contract on bundle bumps.
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


def _prepare_dependency_graph_pages(document):
    """Run after upstream graph rendering and the graph-navigation callback."""
    for page in sorted(Path.cwd().glob("dep_graph_*.html")):
        source = page.read_text(encoding="utf-8")
        prepared = _prepare_dependency_graph(source)
        if prepared != source:
            page.write_text(prepared, encoding="utf-8")
    # The upstream callbacks already own the output-file inventory.
    return []


def ProcessOptions(options, document):  # noqa: N802 (plasTeX package hook)
    document.addPackageResource([
        PackagePreCleanupCB(data=_prepare_dependency_graph_pages)])
