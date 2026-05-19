# Tensor-Network Diagram Grammar

This document fixes the mathematical meaning of the tensor-network glyphs used
in the blueprint. The aim is that a reader can identify the object represented
by a diagram before reading the surrounding proof.

## Basic Glyphs

- Tensor sites are black dots. A physical index is drawn as a thicker vertical
  leg. Virtual indices are drawn as thinner horizontal or slanted legs.
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
- Repeated chain and square-lattice diagrams should be built from the layout
  commands in `blueprint/src/macros/tn_core.tex`, so that the public command
  records the tensor network rather than a coordinate calculation.
- Private glyphs and lengths belong in `blueprint/src/macros/tn_core.tex`.
  Chapter-facing diagrams belong in `blueprint/src/macros/tn_print.tex`.
