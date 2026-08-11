# What tenkz needs, and who reads it

The archive carries eleven runtime files and nothing else. Everything below is
what an installation must already have for those eleven to load and draw. The
list is not copied from the package's load line: each entry names the code that
reads the library, so a reader can check the claim, and the classification is
pinned in `MANIFEST.toml` so a library that enters or leaves the load list
without a traced consumer fails `scripts/tenkz_ctan.py check`.

## 1. The one package

`tikz`, loaded by `tenkz.sty`. Everything else on this page is a TikZ library.

Two of the libraries are not part of pgf and come from packages of their own.
`hobby` and `spath3` are separate CTAN packages, and an installation without
them fails at package load rather than at the first curve. They are the two
names a distribution build has to be told about.

## 2. Placement and model ownership

These are what the package computes and places with. Take one away and the
model has no answer for where a tensor, a wire, or a crossing goes. None of
them is reachable from a host document's styles: an author never writes to
them, and a host that redefined one would be changing where tenkz puts things
rather than how they look.

| Library | Read by | For |
|---|---|---|
| `calc` | `tenkz-tree.code.tex` (18 lines, from line 40) | The partway modifier that places a fusion tree's vertices and its patch control points along the segment between two known points. |
| `hobby` | `tenkz-string.code.tex` (line 232 asserts the library is present) | The curve through a string's waypoints. A string is given its route as a point sequence, and this is what turns the sequence into one smooth path. |
| `spath3` | `tenkz-string.code.tex` (71 lines), `tenkz-kernel.code.tex` (lines 14993, 15443, 16648), `tenkz-render.code.tex` (lines 85 and 189) | Saving a string's route as a path and cutting it. Crossing surgery is a split of a saved path at its intersections; the renderer then draws the saved route rather than recomputing it. |
| `intersections` | `tenkz-string.code.tex` (lines 234, 573, 905), `tenkz-kernel.code.tex` (line 9942) | Counting and locating where two routes meet. A declared crossing that produces no intersection is a coded error, and this is the engine that decides. |

## 3. Host ink

These are what the drawing needs. Take one away and the network is placed and
undrawable: an arrow tip, a brace, a direction mark, or a station outline is
missing. The distinction from the previous group matters to an author, because
this is the group a host document's own TikZ styles reach into.

| Library | Read by | For |
|---|---|---|
| `arrows.meta` | `tenkz-core.code.tex` (lines 372 to 392) | The barb an oriented index carries. |
| `decorations.markings` | `tenkz-core.code.tex` (lines 370 to 393), `tenkz-string.code.tex` (line 1511) | Placing a direction mark at a stated position along a wire, and placing the coordinate a string's bead is reported at. |
| `decorations.pathreplacing` | `tenkz-core.code.tex` (lines 396 and 397) | The brace an annotation draws. |
| `shapes.geometric` | `tenkz-core.code.tex` (lines 231, 1129 to 1157) | The isosceles triangle a library-owned glyph is built on, together with the three anchors the package adds to it. |

## 4. Loaded and unread

`backgrounds` and `fit` are loaded by `tenkz.sty` and read by nothing: no file
under `tex/tenkz/` calls either, and no case in `tests/tenkz/` or picture in
`docs/tenkz/` does. `backgrounds` is named twice in the source, both times in a
sentence saying the renderer's class order does the work a background layer
would do elsewhere, which is a statement that the library is not used. `fit`
does not appear at all.

They are recorded rather than dropped. Both come from pgf, so an installation
that has `tikz` has them, and carrying them costs nobody anything; removing the
loads would change what a host document inherits when it loads tenkz, which is
a release decision about the package's load-time surface rather than a staging
one. The entries sit in `MANIFEST.toml` under `unconsumed` so that the decision
stays visible, and so a later consumer moves the entry rather than appearing
without one.

## 5. What is gone

The commutative-diagram, free-placement, and lattice front ends were removed
along with the loads they brought. No file under `tex/tenkz/` loads `tikz-cd`,
`tikzcd`, or `quantikz`. The one occurrence of the phrase in the package is a
sentence in `tenkz.sty` saying commutative diagrams belong to tikz-cd and are
outside this language, and the closure walk blanks comments before it reads a
load, so that sentence cannot reach the dependency list and a surviving load
would be the only way the name could. `scripts/tenkz_ctan.py check` reads the
absence from the walked closure rather than asserting it.

The blueprint keeps its own `tikz-cd` load in
`blueprint/src/macros/diagrams.tex`. That is the blueprint's dependency, not
the package's: it is not on the load graph walked from `tenkz.sty`, and nothing
the archive carries reads it.

## 6. The offline flat

`python3 scripts/tenkz_ctan.py offline` builds the archive, unpacks it into one
directory with no subdirectory, writes representative corpus cases beside it,
and compiles each one there. It is the arXiv reading of the same files: a
source submission is unpacked beside a manuscript rather than installed, so a
runtime that only resolves through a directory would fail, and so would one
that had to be generated before it could be read.

Eight cases are compiled, covering the six picture classes an upload is judged
on: a flat placement, a plane frame, a circle frame, a string with crossings,
an enclosure, and a diagrammatic equation. Six are the review benchmark's
preamble-free cases, compiled inside the standalone document an author would
write around them; two are kernel probes, which carry their own preamble and
are compiled as they stand, so the self-contained document form is covered as
well as the fragment form.

Each run is read rather than counted. The engine writes an input record, and
every runtime file it opened must have resolved inside the flat directory. The
event stream goes through `scripts/tenkz_audit.py`, which is the audit
`HACKING.md` prescribes, so an empty picture, a detached closure, a crossing
that produced no occlusion, or an equation whose two sides expose different
boundaries is a failed run. On top of the audit, each case has to show its own
class in the stream: a plane frame writes a frame record naming the plane map,
a circle frame writes a boundary signature with a numeric compass face because
it transports each port along its station's outward radius, a crossing writes
crossing records, an enclosure writes an enclosure mark, an equation writes a
check record that folded its panels into a relation, and a flat placement
writes no frame record at all. A case swapped for one of another class fails on
both the source it declares and the stream it writes.

### What the isolation is

The run gets an environment built rather than inherited. The home directory and
the three TeX trees an installation lets a user override are pointed at empty
directories, so no personally installed copy of tenkz can answer. The search
path is the current directory and then the installation, which is what leaves
`tikz`, `hobby`, and `spath3` findable and is also why the input record decides
where the runtime came from. The four variables that let kpathsea build a font
or a format on demand are set to refuse. Fourteen installers and fetchers,
`tlmgr` and the `mktex` family among them, are shadowed by scripts that record
their own call and fail, and the run fails if any of them was reached for. The
engine is invoked with no shell escape, so it can start no process of its own.
Proxy variables point at the discard port.

### What it does not prove

It does not prove the machine had no network. It proves that the runs installed
nothing, fetched nothing, generated no font and no format, and read no file
from this repository: every tenkz file came from the unpacked archive, and
everything else came from the pinned installation. A stronger claim would need
the run confined to a network namespace, which is not portable to the platforms
this harness runs on.
