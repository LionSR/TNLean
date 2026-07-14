# Tensor-Network Diagram Grammar

This document fixes the mathematical meaning of the tensor-network glyphs used
in the blueprint and slide collection. The aim is that a reader can identify
the object represented by a diagram before reading the surrounding proof.
Graphical appearance carries mathematical meaning: changing a label does not
change the kind of object represented, and changing the kind of object requires
changing its graphical form. Every index line ends exactly at the boundary of
the object carrying that index.

## Atomic Graphical Calculus

The common grammar describes a tensor network by small composable units. An
atom is a named graphical object together with named ports on its boundary. A
port represents one occurrence of a virtual index, one occurrence of a physical
index, or one endpoint of a morphism. Composition joins only ports of the same
declared type.

For example, the following construction places two tensors, names their four
virtual ports, and contracts one pair:

```tex
\TN@tensor{leftTensor}{(0,0)}
\TN@vport{leftIn}{leftTensor}{west}
\TN@vport{leftOut}{leftTensor}{east}

\TN@tensor{rightTensor}{(1.4,0)}
\TN@vport{rightIn}{rightTensor}{west}
\TN@vport{rightOut}{rightTensor}{east}

\TN@vopenport{leftIn}{-0.6,0}
\TN@vconnectports{leftOut}{rightIn}
\TN@vopenport{rightOut}{0.6,0}
```

The names `leftOut` and `rightIn` refer to exact boundary points; no numerical
coordinate is chosen to approximate either endpoint. The same atoms can be
placed elsewhere or composed with different atoms without changing their
internal definitions. This example is written in the private macro scope,
where `@` is a letter; a standalone use should be enclosed by
`\makeatletter` and `\makeatother`.

The constructors `\TN@vport`, `\TN@pport`, and `\TN@mport` name a standard
boundary anchor and register it as virtual, physical, or morphism-valued. For
several ports on one side of a box, use a typed side constructor such as
`\TN@vwestport` or `\TN@pnorthport`, or use `\TN@typedbetweenport` on a general
boundary segment. The constructors `\TN@vterminal`, `\TN@pterminal`, and
`\TN@mterminal` name external endpoints. The operations `\TN@vconnectports`,
`\TN@pconnectports`, and `\TN@mconnectports` join like-typed ports and reject a
type mismatch. The operations `\TN@vopenport` and `\TN@popenport` create a
named external terminal and join it to the given port. The untyped and
anchor-based forms remain only for compatibility inside older local
constructions.

## Basic Glyphs

- Tensor sites are black dots. A physical index is drawn as a thicker vertical
  leg. Virtual indices are drawn as thinner horizontal or slanted legs.
- A tensor label is placed outside its black dot in the blueprint; a label does
  not change the kind of object. The enlarged tensor circles in dark slides
  may carry the same label internally for legibility. A neutral square box
  denotes a named tensor whose internal contraction is suppressed. A displayed
  tensor-product or direct-sum factor is a pale plate. A linear map, including
  an isometry or coisometry, is a rounded blue box. A state displayed without
  its constituent tensors is a rounded gray box. A parenthesized algebraic
  expression is shown in the distinct expression box. These glyphs are
  distinct from the red dots used for matrices inserted on individual legs.
- A contraction junction is a black dot substantially smaller than a local
  tensor. It marks a common endpoint of several index lines and is not another
  tensor.
- An MPS tensor is a black dot with left and right virtual legs and one
  physical leg. A blocked MPS tensor is drawn by enclosing consecutive sites in
  a rectangle, with the blocked physical word represented by the external
  physical legs of the block.
- An MPO or MPDO tensor is drawn as the corresponding double-layer object. The
  two physical legs of a ket-bra pair should remain visible unless the diagram
  explicitly represents their contraction.
- A PEPS tensor is a black dot with the appropriate local virtual legs in the
  lattice directions and a physical leg. A PEPS region is drawn as a rectangle
  or polygon around the sites in the region, not as a new tensor site.
- A virtual operator, gauge, or arbitrary matrix insertion is a red dot on a
  virtual leg. A physical operation is a red dot on a physical leg. These two
  cases should not be interchanged.
- A gauge transform is a virtual operator insertion together with its inverse
  on the adjacent oriented virtual leg when the diagram represents a
  cancellation. If only one red dot is shown, the diagram represents a single
  inserted matrix, not a completed gauge cancellation.
- A physical isometry or coarse-graining map is drawn on the physical legs, not
  on the virtual bonds. It should be visually distinct from a virtual gauge.
- A diagonal weight, fixed-point density, or scalar block weight is drawn as a
  labeled operator on the virtual index or on the block label, according to the
  source formula. It should not be represented by relabeling a tensor site.
- A contracted physical index is indicated by joining the corresponding
  physical legs, or by omitting the external physical legs only when the
  surrounding formula states the contraction, for example in a transfer map or
  an overlap.
- Contracted indices are drawn with solid strokes. An open contraction routed
  around another glyph uses the shared bent-leg style; it is not a closure
  merely because its path bends. A one-dimensional periodic trace is a rounded
  solid closure, including when an operator splits the return path into two
  pieces. Solid rounded rectangles around tensor-product factors are factor
  boundaries, distinct from dashed grouping boundaries. Dashed strokes are
  reserved for grouping boundaries, changes of multiplicity basis, and an
  explicitly identified boundary of a periodic lattice. A purification
  contraction is a solid physical-index stroke joining dedicated ancillary
  legs; it is not dashed and should not share an attachment point with an open
  virtual leg.

Every contraction joins two registered ports of the same type. Virtual trace
closures join named ports through `\TN@vtraceportsbelow`,
`\TN@vtraceportsabove`, or `\TN@vtraceportsright`; physical trace closures use
`\TN@ptraceportsbelow`, `\TN@ptraceportsabove`, or
`\TN@ptraceportsright`. An open index ends at an explicitly named typed
terminal; it does not end at a numerical point chosen near a tensor or map. A
red insertion divides an index line into two contractions ending on the
insertion.

The library supplies four standard open interfaces. The construction
`\TN@openhorizontalports` exposes the west and east virtual indices,
`\TN@openvverticalports` exposes two vertical virtual indices,
`\TN@openpverticalports` exposes the north and south physical indices, and
`\TN@openmpoports` combines the first and third interfaces. These interfaces
use the common virtual and physical leg lengths. Consequently two occurrences
of the same local tensor have the same boundary geometry.

Trivalent maps are typed by their mathematical domain and codomain. The maps
`\TN@splitmap` and `\TN@mergemap` have only virtual ports. The maps
`\TN@physicalsplitmap` and `\TN@physicalmergemap` have only physical ports.
The construction `\TN@bondpairmap` has two virtual half-bonds and one physical
index. Each physical split or merge uses the same `Trunk`, `Left`, and `Right`
interface. Thus blocking a physical Hilbert space, fusing virtual sectors, and
realizing a physical site from two virtual half-bonds cannot be confused by a
change of labels or by reflecting the map.

The action tensors of an MPO on an MPS are constructed by `\TN@actionmap` and
`\TN@coactionmap`. Their three virtual ports are named `MPO`, `StateIn`, and
`StateOut`, corresponding to the blocks \(a\), \(x\), and \(y\) in
\(V_{ax}^{y,i}\). The glyph remains the ordinary trivalent linear-map box;
the additional names record the module roles of its indices.

A canonical-form gauge \(X_{j,q}\) is constructed by `\TN@sectorgauge`.
Besides the horizontal bond ports `W` and `E`, it has distinct virtual ports
`Block` and `Copy` for the indices \(j\) and \(q\). Attaching these ports
separately to parallel sector buses preserves the distinction between the two
indices. The reflected construction `\TN@inverseSectorgauge` retains these
port roles while reversing their planar order for \(X_{j,q}^{-1}\).

A sector index which passes through several factors is represented by
`\TN@vbus`. Its endpoints and every contraction point are named virtual ports.
A parallel sector index is obtained from it by `\TN@vparallelbus`, which
inherits the same horizontal extent and applies a common signed displacement.
A tap may be placed at a fixed relative position by `\TN@vbustap`, or projected
from a port of the attached tensor by `\TN@vbusprojecttap`. Projection makes
the attachment depend on the tensor placement rather than on a second copy of
its horizontal coordinate.

Orthogonal virtual contractions use `\TN@vconnectportshv` or
`\TN@vconnectportsvh`; the suffix records the order of the horizontal and
vertical segments. A span annotation such as \(n\), \(\geq \ell\), or
\(\geq \ell'\) uses `\TN@spanbraceabove` or `\TN@spanbracebelow`. Such a brace
is an annotation and never denotes an additional index. Its endpoints are
named by `\TN@annotationterminal`, which deliberately carries no index type.

Tensor products are written with $\otimes$. A horizontal line never means
mere adjacency or tensor product. The construction `\TN@factorpair` displays
two factor plates and places $\otimes$ between them. When two factors carry a
contracted index, the contraction is drawn explicitly instead.

## Blocks, Regions, and Labels

- A rectangle around several tensor sites denotes a blocked tensor or an
  injective region. The label under the rectangle names the blocked tensor or
  the region, not an auxiliary construction in the formalization.
- Labels should be mathematical labels from the source statement whenever
  possible: for example \(A^{[L]}\), \(R\), \(S\), \(T\), \(X\), \(Y\), or
  \(\lambda\). Avoid labels that name a local proof step rather than the
  tensor, region, or operator appearing in the paper.
- When the blueprint translates a boxed tensor diagram from a source paper into
  the local dot convention, the translation must preserve the distinction
  between tensor sites, blocked regions, virtual insertions, physical
  operations, and gauges. A box in the source may become a rectangle around
  several dots, but it should not become a single dot unless the source is
  explicitly passing to a blocked tensor.

## Canonical Examples

- The transfer map \(\E_A(X) = \sum_i A^i X (A^i)^\dagger\) is drawn as a
  double-layer contraction with the physical index summed and \(X\) inserted on
  the virtual leg.
- MPS blocking is drawn by enclosing consecutive tensor sites and leaving the
  boundary virtual legs external. The physical word is represented by the
  physical legs inside the block.
- The RFP isometry criterion is drawn with the isometry on physical legs and
  the virtual fixed-point operator on the virtual index.
- A PEPS gauge move is drawn as oriented virtual gauges on incident edges of a
  local tensor, with the absorbed tensor labeled \(\widetilde B_v\).
- A PEPS edge insertion is drawn as a single virtual matrix on the chosen edge;
  the physical realization of that insertion is a separate diagram with the
  operator on a neighboring physical leg.

## PEPS Fundamental-Theorem Diagrams

- A PEPS edge-blocking diagram should show the chosen edge and then the
  corresponding three-site chain. The pre-blocking side should keep enough of
  the original graph visible to identify the two endpoint regions and the
  complementary middle block, following the source-paper convention of marking
  the two endpoints separately from the boxed complement.
  In the diagram corresponding to `eq:block_to_mps` in arXiv:1804.04964,
  the upper-left circled endpoint is \(A'_1\), the lower-left circled endpoint
  is \(A'_2\), and the boxed complement is \(A'_3\); do not interchange the two
  endpoint labels.
- In diagrams following arXiv:1804.04964, Section 3, the matrix-insertion
  comparison is represented by an arbitrary virtual matrix on a bond in the
  first three-site chain and the corresponding virtual matrix in the second
  chain. The physical-realization step is represented separately by putting the
  resulting physical operation on either neighboring physical leg.
- The converse physical-to-virtual step should be represented separately:
  two neighboring physical operations that act identically on the state
  determine a virtual operation on their shared bond.
- The post-absorption comparison corresponding to equation `eq:inj_equal_edge`
  should be preceded by the local absorption of the edge gauges into the
  second tensor family. The absorption picture should draw the incident
  oriented edge gauges at a vertex of the \(B\)-tensor and label the resulting
  tensor \(\widetilde B_v\). The subsequent `eq:inj_equal_edge` comparison is
  a separate theorem-level step and should be drawn on the full PEPS graph, not
  only on the blocked three-site chain, because the paper uses it for every
  edge of the original graph.
- The final injective-PEPS comparison should not be folded into the local gauge
  sketch. First draw the generalized two-injective-tensor comparison from
  Lemma `inj_equal_tensors_2`, with several shared virtual bonds and an
  arbitrary insertion on one bond. Its proof should also draw the residual
  virtual operators on the exposed legs after the second injective tensor is
  inverted, since this is where the paper proves that those operators are
  scalar. Then draw the one-vertex-versus-complement specialization: two
  injective regions that differ by one vertex imply proportionality of the two
  local tensors after the edge gauges have been absorbed.
- Normal-PEPS diagrams from arXiv:1804.04964, Section 3, should be attached to
  their own normal theorem nodes. The union-of-injective-regions picture should
  show the four regions \(A\setminus B\), \(A\cap B\), \(B\setminus A\), and
  \((A\cup B)^c\). The square-lattice normal proof should show the regions
  \(R\), \(S\), and \(T\), then the red/blue/complementary blocking around a
  distinguished edge, before reusing the three-site injective-chain theorem.
  The translationally invariant normal gauge formula should distinguish the
  horizontal gauge \(X\) from the vertical gauge \(Y\).

## Public Commands

- Public tensor-network commands should be named by the mathematical move they
  draw. A chapter should not use an unattached generic diagram when the proof
  step is a specific contraction, insertion, blocking, or gauge absorption.
- Public commands should be built from the common glyphs above. If a diagram
  requires a new glyph, first record the mathematical meaning here and then add
  the corresponding private TikZ primitive and web-rendering support.
- Repeated chain and square-lattice diagrams should be built from the atomic
  and layout commands in `tex/tn/tn_core.tex` and `tex/tn/tn_library.tex`, so
  that the public command records the
  tensor network rather than a coordinate calculation.
- Repeated PEPS graph motifs, such as a five-site edge patch, a two-injective
  comparison pair, or a trivalent residual-gauge vertex, should likewise be
  factored through private layout commands before being used in theorem-level
  public diagrams.
- A theorem-level figure belongs in `blueprint/src/macros/tn_print.tex`, even
  when its mathematical content is specific to one chapter. This gives the
  printed and web blueprints one common definition. Chapter sources call the
  registered command and do not carry a second local TikZ construction.
- Semantic glyphs, theme slots, typed ports, and primitive contractions belong
  in `tex/tn/tn_core.tex`. Reusable MPS, MPO, MPDO, PEPS, and fusion
  compositions belong in `tex/tn/tn_library.tex`. Chapter-facing figures
  belong in `blueprint/src/macros/tn_print.tex`; the two files under
  `blueprint/src/macros/` with the core and library names are compatibility
  entry points.

The library provides `\TN@mpssite`, `\TN@mposite`, and `\TN@pepssite` for
local tensor sites; `\TN@doublelayer` for the local contraction in a transfer
construction; `\TN@operatorstate` for a density matrix or operator with paired
system ports; `\TN@splitmap`, `\TN@mergemap`, `\TN@physicalsplitmap`,
`\TN@physicalmergemap`, `\TN@bondpairmap`, and `\TN@fusionmap` for the typed
trivalent maps; `\TN@vbus` for a virtual sector line;
`\TN@squarelatticepatch` and `\TN@squarepepspatch` for finite square lattices;
and `\TN@openMPSword`, `\TN@openMPOword`, and `\TN@closedMPOword` for standard
finite words. MPS and MPO words are declared by distinct constructors, since
an MPS site has one physical index whereas an MPO site has two. These
constructions determine the conventional index directions once. Each local
site atom declares stable boundary ports and draws no open stub. The
corresponding
`\TN@mpssiteWithOpenLegs`, `\TN@mpositeWithOpenLegs`,
`\TN@pepssiteWithOpenLegs`, and `\TN@doublelayerWithOpenLegs` motifs add named
free endpoints when a complete standalone object is required. A complete
figure should compose these units rather than choose the same leg positions
independently at each occurrence.

The common lengths `\TN@layerpitch`, `\TN@virtualleglen`,
`\TN@physicalleglen`, `\TN@traceclearance`, `\TN@busoffset`, and
`\TN@buspitch` fix the standard separations. The two
branch positions of a trivalent map are fixed by
`\TN@branchfirstfraction` and `\TN@branchsecondfraction`. A theorem-level figure
may scale the whole picture, but should not reproduce one of these distances
as a local numerical constant.

The web blueprint renders the same complete figure commands as cached SVG
images. A new chapter-facing command therefore also requires an argument
declaration in `blueprint/src/Packages/tn_diagrams.py` and a name in
`blueprint/src/plastex_templates/TensorNetworkDiagrams.jinja2s`. A private
construction in `tex/tn/tn_core.tex` or `tex/tn/tn_library.tex` requires no
such declaration.

## Slide Diagrams

The slide collection loads the shared semantic core and reusable atoms from
`tex/tn/`. The file `docs/slides/tn_library_dark.tex` changes only the
`tn theme ...` slots and defines the complete figures used by the slide
collection. Thus the slides remain independent of the blueprint build files
while sharing the meanings of tensors, insertions, maps, states, expressions,
ports, contractions, traces, and grouping boundaries.

The slide preamble imports this library. A slide should call one of its complete
diagram commands rather than declare local tensor-network styles or draw a
second version of a standard construction.
