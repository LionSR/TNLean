# Dependency-graph rendering

The local post-render callback decodes the pinned graph template's DOT using
JavaScript string-literal semantics, then counts nodes and edges with the
blueprint stack's existing pygraphviz dependency. More than 1,000 nodes or
more than 1,500 edges selects build-time rendering. At or below both thresholds,
the existing browser worker and its diagnostics are unchanged.

These thresholds are a conservative routing policy, not a runtime guarantee.
Topology affects layout time too. A measured full graph with 8,369 nodes and
14,400 edges took about 420 seconds with the bundled default-quality renderer,
longer than the reader's existing 300-second page deadline. The large route
moves that same default-quality computation into generation; it does not
shorten layout iterations or remove graph content.

Generation requires Node.js 18 or newer already on PATH. The helper uses only
Node standard modules and the JavaScript/WASM shipped by pinned plastexdepgraph
0.0.5. It installs nothing and fetches no remote assets. It renders the current
decoded DOT afresh, consumes that returned SVG directly, and has no saved-SVG
input or cross-build cache. Each helper process has a 600-second safety bound.
Missing Node, invalid DOT/SVG, layout failure and timeout fail generation.

The SVG retains its labels, colors, styles, geometry, nodes and edges. Only the
root width and height presentation attributes are adapted to the container.
Statement modals, links, and the original fit, pan and zoom behavior remain in
place. In particular, the inherited maximum 10× zoom can still make labels on
the very wide full graph unreadable; precomputation does not solve that
existing usability limitation.

Both routes use the same phase/error diagnostic functions. Precomputed pages
report `precomputed-loaded`, `interactionStart`, then `complete`; they do not
report browser layout or a worker. Readiness is recorded only after SVG
structure, zoom setup and interaction initialization succeed. Setup failures
report an error and leave readiness unset. The normal page reader still checks
every generated page, requires readiness plus SVG, and shares the original
300-second budget between navigation and rendering. Graph pages remain serial
after the parallel content-page pass.

## Regression checks

With the pinned blueprint dependencies and browser runtime already available:

```sh
python3 scripts/test_blueprint_graph_worker.py
python3 scripts/test_blueprint_graph_precompute.py
python3 scripts/test_blueprint_graph_worker.py --browser-smoke
python3 scripts/test_blueprint_graph_precompute.py --browser-smoke
python3 scripts/test_blueprint_web_render.py --web-root blueprint/web
```

The live-worker smoke test remains mandatory and checks both valid and
malformed DOT. The separate precomputed smoke forces only the tiny fixture
through build-time rendering. It checks labels, node/edge counts, completion,
modal/link behavior, actual pan/zoom at desktop and narrow widths, and
structural, zoom and interaction failures. Each smoke step has its own
two-minute CI bound and uses a 30-second tiny-page deadline. Neither changes
the complete generated-page reader's budget.
