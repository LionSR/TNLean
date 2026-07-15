# Tensor-Network Diagram Grammar

This document fixes the mathematical meaning of every tensor-network glyph in
the repository. A reader should be able to identify the represented object
before reading the surrounding proof.
Graphical appearance carries mathematical meaning: changing a label does not
change the kind of object represented, and changing the kind of object requires
changing its graphical form. Every index line ends exactly at the boundary of
the object carrying that index.

The files `tex/tn/tn_core.tex` and `tex/tn/tn_library.tex` are the single
source of truth. They determine the light and dark renderings, the PDF and web
blueprints, the slides, the audit gallery, and the reference images. A client
document may select a theme slot or a layout profile, but it may not redefine
geometry, ports, glyphs, or contractions.

## Atomic Graphical Calculus

The common grammar describes a tensor network by small composable units. An
atom is a named graphical object together with named ports on its boundary. A
port represents one occurrence of a virtual index, one occurrence of a physical
index, or one endpoint of a morphism. Composition joins only ports of the same
declared type.

For example, the following construction places two MPS sites and contracts one
pair of virtual ports:

```tex
\begin{TNDiagram}[normal]
  \TNMPSSite{leftTensor}{(0,0)}{A}
  \TNMPSSite{rightTensor}{(1.4,0)}{B}
  \TNOpenVirtualWest{leftTensorWest}
  \TNConnectVirtual{leftTensorEast}{rightTensorWest}
  \TNOpenVirtualEast{rightTensorEast}
\end{TNDiagram}
```

The names `leftTensorEast` and `rightTensorWest` refer to exact boundary
points; no numerical
coordinate is chosen to approximate either endpoint. The same atoms can be
placed elsewhere or composed with different atoms without changing their
internal definitions.

Complete diagrams use `TNDiagram`. Short identities use `TNEquationRow`,
`TNTerm`, and `TNRelation`; related identities use `TNEquationRows` so that
their relation signs share one column. The `normal` profile is used for structural
figures; `compact` is used for definitions and local identities. These profiles
fix the pitches, leg lengths, branch positions, relation gaps, trace
clearances, and outer margins.

The operations `TNConnectVirtual`, `TNConnectPhysical`, and
`TNConnectMorphism`, together with their typed orthogonal variants, join
like-typed ports and reject a type mismatch. Typed `TNTrace...` commands form
periodic or trace closures. `TNPortAlias` gives a declared port another role
name while preserving its type. Direct use of a TikZ anchor is not a
contraction operation.

The standard port roles are as follows.

| Atom | Virtual ports | Physical ports |
|---|---|---|
| MPS site | `West`, `East` | `Ket` |
| MPO or MPDO site | `West`, `East` | `Ket` north, `Bra` south |
| Rotated MPO or MPDO site | `North`, `South` | `Ket` west, `Bra` east |
| PEPS site | `West`, `East`, `North`, `South` | `Ket` |
| Trivalent map | `Combined`, `FactorOne`, `FactorTwo` | none, unless physical |

For a stacked MPO product, `UpperBra` is contracted with `LowerKet`. An action
map also exposes `StateOut`, `MPO`, and `StateIn`. A sector gauge has distinct
`Block` and `Copy` ports. A purification site has two ancillary ports, joined
by a straight physical contraction.

Split, merge, fusion, cofusion, action, coaction, and physical blocking maps
are orientations of one trivalent constructor. Thus the map box, branch
fractions, and port roles have the same meaning in every occurrence.

## Basic Glyphs

- Tensor sites are black dots. A physical index is drawn as a thicker vertical
  leg. Virtual indices are drawn as thinner horizontal or slanted legs.
- A tensor label is placed outside its black dot; a label does not change the
  kind of object. Dark slides change only the palette, not the geometry or
  typography of the glyph. A neutral square box
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
- A virtual operator, gauge, or arbitrary matrix insertion is a fixed-size red
  dot on a virtual leg, with its label placed outside the dot by a profile
  clearance. A physical operation is the same fixed marker on a physical leg.
  Its diameter does not depend on the length of its label. These two cases
  should not be interchanged. The directional `TNLabelAbove`, `TNLabelBelow`,
  `TNLabelLeft`, and `TNLabelRight` operations choose the clear side when the
  insertion lies inside a vertical or horizontal composition.
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
closures join named ports through `\TNTraceVirtualBelow`,
`\TNTraceVirtualAbove`, or `\TNTraceVirtualRight`; physical trace closures use
`\TNTracePhysicalBelow`, `\TNTracePhysicalAbove`, or
`\TNTracePhysicalRight`. An open index ends at an explicitly named typed
terminal; it does not end at a numerical point chosen near a tensor or map. A
red insertion divides an index line into two contractions ending on the
insertion.

The operations `\TNOpenVirtualWest`, `\TNOpenVirtualEast`,
`\TNOpenVirtualNorth`, `\TNOpenVirtualSouth`, and their physical analogues
extend a declared port by the common leg length. Consequently two occurrences
of the same local tensor have the same boundary geometry.

Trivalent maps are typed by their mathematical domain and codomain. The maps
`\TNSplitMap` and `\TNMergeMap` have only virtual ports, while
`\TNPhysicalSplitMap` and `\TNPhysicalMergeMap` have only physical ports. The
general `\TNTrivalentMap` fixes the same box and branch geometry for mixed
interfaces. Each orientation uses the roles `Combined`, `FactorOne`, and
`FactorTwo`. Thus blocking a physical Hilbert space, fusing virtual sectors,
and realizing a physical site from two virtual half-bonds cannot be confused
by a change of labels or by reflecting the map.

The action tensors of an MPO on an MPS are constructed by `\TNActionMap` and
`\TNCoactionMap`. Their three virtual ports are named `MPO`, `StateIn`, and
`StateOut`, corresponding to the blocks \(a\), \(x\), and \(y\) in
\(V_{ax}^{y,i}\). The glyph remains the ordinary trivalent linear-map box;
the additional names record the module roles of its indices.

A canonical-form gauge \(X_{j,q}\) is constructed by `\TNSectorGauge`.
Besides the horizontal bond ports `W` and `E`, it has distinct virtual ports
`Block` and `Copy` for the indices \(j\) and \(q\). Attaching these ports
separately to parallel sector buses preserves the distinction between the two
indices. The reflected construction `\TNInverseSectorGauge` retains these
port roles while reversing their planar order for \(X_{j,q}^{-1}\).

A sector index which passes through several factors is represented by
`\TNSectorBus`. Its endpoints and every contraction point are named virtual
ports. A parallel sector index is obtained from it by `\TNParallelSectorBus`,
which inherits the same horizontal extent and applies a common signed
displacement. A tap is placed by `\TNSectorBusTap`; its endpoint remains a
named virtual port.

Orthogonal virtual contractions use `\TNConnectVirtualHV` or
`\TNConnectVirtualVH`; the suffix records the order of the horizontal and
vertical segments. The corresponding physical and morphism operations follow
the same convention. An annotation endpoint is declared by `\TNPoint`, which
deliberately carries no index type.

Tensor products are written with $\otimes$. A horizontal line never means
mere adjacency or tensor product. The construction `\TNFactorPair` displays
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

The public library provides `\TNMPSSite`, `\TNMPOSite`, `\TNRotatedMPOSite`,
and `\TNPEPSSite` for local tensor sites; `\TNDoubleLayer` for the local
contraction in a transfer construction; `\TNOperatorState` for a density
matrix or operator with paired system ports; `\TNSplitMap`, `\TNMergeMap`,
`\TNPhysicalSplitMap`, `\TNPhysicalMergeMap`, and `\TNFusionMap` for typed
trivalent maps; `\TNSectorBus` for a virtual sector line;
`\TNSquarePEPSPatch` for a finite square lattice; and `\TNHorizontalWord` and
`\TNVerticalWord` for standard finite words. The common gauge and periodic
constructions are `\TNGaugeConjugatedMPSSite`, `\TNFourBondGaugeStar`,
`\TNCardinalGaugeCross`, and `\TNCyclicMPSWord`. MPS and MPO words are declared by
distinct constructors, since an MPS site has one physical index whereas an MPO
site has two. These constructions determine the conventional index directions
once. Each local atom declares stable boundary ports; the `\TNOpen...`
operations extend only those declared ports. A complete figure composes these
units rather than choosing the same leg positions independently at each
occurrence.

The named profiles fix all standard separations and the branch positions of a
trivalent map. A theorem-level diagram selects `normal` or `compact`; it does
not rescale the picture or reproduce one of these distances locally.

The web blueprint renders the same complete figure commands as cached SVG
images. Zero-argument registrations are derived from the TeX declarations.
Only parameterized chapter commands require an argument declaration in
`blueprint/src/Packages/tn_diagrams.py`; every chapter-facing command also has
an explicit `display` or `figure` role and an HTML template entry. A private
construction in `tex/tn/tn_core.tex` or `tex/tn/tn_library.tex` requires no
such declaration.

Commands whose names contain `TN@` are private and occur only in `tex/tn/`.
Blueprint diagrams, slides, examples, galleries, and tests use the public
calculus.

## Author Checklist

- Every contraction has two named endpoints of the same type.
- A line does not stop short of a port, pass behind a glyph, or enter a box
  except through a declared port.
- Curves represent genuine trace or periodic topology. Purification and other
  ordinary local contractions are straight.
- A semicircle is not used as bra or ket notation.
- A glyph has one meaning throughout the repository; changing its label does
  not change its object class.
- Pure algebra remains algebra. A decorative enclosure does not turn a direct
  sum or tensor product into a tensor network.
- Definitions and local identities are compact displays rather than floats.
- Labels are positioned relative to named ports and do not meet sites, lines,
  or region boundaries.
- Repeated pitches, leg lengths, branch positions, relation gaps, and loop
  clearances are taken from the selected layout profile.
- A figure is retained only when spatial topology, nontrivial routing, a
  fusion tree, or a multistage construction is part of the assertion.
- The isolated rendering and the actual page have both been inspected at
  normal size. Their ink remains strictly inside the canvas boundary.

## Slide Diagrams

The slide collection loads the shared semantic core and reusable atoms from
`tex/tn/`. The file `docs/slides/tn_library_dark.tex` appends only palette
choices to the `tn theme ...` slots and defines the complete figures used by
the slide collection. Thus the slides remain independent of the blueprint
build files while sharing the meanings of tensors, insertions, maps, states,
expressions, ports, contractions, traces, and grouping boundaries.

The slide preamble imports this library. A slide should call one of its complete
diagram commands rather than declare local tensor-network styles or draw a
second version of a standard construction.
