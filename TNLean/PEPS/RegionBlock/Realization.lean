import TNLean.PEPS.RegionBlock.Recovery
import TNLean.PEPS.RegionBlock.Algebra
import TNLean.PEPS.InsertionAlgebra

/-!
# Region physical realization and the region insertion transfer

For a boundary edge `f` of an arbitrary finite region `R`, with single in-region
endpoint vertex `v`, this file realizes the region-inserted matrix insertion on
`f` as a physical operator at `v` and transfers it across `SameState` to build the
region analogue of `edgeTransferMatrix`. This supplies the data of a
`RegionInsertionTransfer` on `f`, the last gating ingredient of the per-edge gauge
for the normal PEPS Fundamental Theorem.

The development mirrors `TNLean.PEPS.InsertionAlgebra` piece by piece, with the
single in-region endpoint vertex `v` playing the role of the edge's right
endpoint:

* `regionBoundaryEdgeInVertex` is the in-region endpoint of a boundary edge; the
  edge is read as an incident edge `regionBoundaryEdgeInIncident` at that vertex.
* `regionRealizationSum_eq_regionInsertedCoeff` is the region analogue of
  `edgeRealizationSum_right_eq_sum_edgeBlockedCoeff`: the region-inserted
  coefficient equals a realization sum over physical configurations at `v`, with
  the inserted matrix carried by a physical operator at `v`.
* `regionRightInsertionOp` is the region analogue of `edgeRightInsertionOp`: the
  physical operator at `v` realizing the matrix insertion on `f`.
* `regionTransferMatrix` is the region analogue of `edgeTransferMatrix`: the
  matrix read off after transferring the realization across `SameState`.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, Lemma
  `inj_isomorph`, lines 254--582 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### The in-region endpoint vertex of a boundary edge

A boundary edge of `R` has exactly one endpoint in `R`. That endpoint is the
vertex at which a matrix insertion on the edge is realized as a physical operator.
The edge, read as an incident edge at that vertex, is the distinguished bond of
the insertion. -/

/-- The in-region endpoint of a boundary edge `f` of `R`: the unique endpoint
lying in `R`. -/
noncomputable def regionBoundaryEdgeInVertex (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) : V :=
  if f.1.1.1 ∈ R then f.1.1.1 else f.1.1.2

omit [Fintype V] [DecidableRel G.Adj] in
/-- The in-region endpoint of a boundary edge lies in `R`. -/
theorem regionBoundaryEdgeInVertex_mem (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) :
    regionBoundaryEdgeInVertex (G := G) R f ∈ R := by
  unfold regionBoundaryEdgeInVertex
  split_ifs with h
  · exact h
  · rcases f.2 with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact absurd h1 h
    · exact h2

omit [Fintype V] [DecidableRel G.Adj] in
/-- The boundary edge `f` is incident to its in-region endpoint. -/
theorem regionBoundaryEdgeInVertex_incident (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) :
    f.1.1.1 = regionBoundaryEdgeInVertex (G := G) R f ∨
      f.1.1.2 = regionBoundaryEdgeInVertex (G := G) R f := by
  unfold regionBoundaryEdgeInVertex
  split_ifs with h
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The boundary edge `f` as an incident edge at its in-region endpoint vertex. -/
noncomputable def regionBoundaryEdgeInIncident (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) :
    IncidentEdge G (regionBoundaryEdgeInVertex (G := G) R f) :=
  ⟨f.1, regionBoundaryEdgeInVertex_incident (G := G) R f⟩

omit [Fintype V] [DecidableRel G.Adj] in
@[simp] theorem regionBoundaryEdgeInIncident_edge (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) :
    (regionBoundaryEdgeInIncident (G := G) R f).1 = f.1 := rfl

end PEPS
end TNLean
