# Tensor-Network Diagram Grammar

- Tensor sites are black dots. A physical index is drawn as a thicker vertical
  leg. Virtual indices are drawn as thinner horizontal or slanted legs.
- A virtual operator, gauge, or matrix insertion is a red dot on a virtual leg.
  A physical operation is a red dot on a physical leg. These two cases should
  not be interchanged.
- A rectangle around several tensor sites denotes a blocked tensor or an
  injective region. The label under the rectangle names the blocked tensor or
  the region, not an auxiliary construction in the formalization.
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
  \((A\cup B)^c\). The square-lattice normal route should show the regions
  \(R\), \(S\), and \(T\), then the red/blue/complementary blocking around a
  distinguished edge, before reusing the three-site injective-chain theorem.
  The translationally invariant normal gauge formula should distinguish the
  horizontal gauge \(X\) from the vertical gauge \(Y\).
- The blueprint may use the local dot convention rather than the exact boxed
  tensor glyphs of a source paper, but any such change must preserve the
  mathematical distinction between tensor sites, blocked regions, virtual
  insertions, physical operations, and gauges.
- Public tensor-network commands should be named by the mathematical move they
  draw. A chapter should not use an unattached generic diagram when the proof
  step is a specific contraction, insertion, blocking, or gauge absorption.
