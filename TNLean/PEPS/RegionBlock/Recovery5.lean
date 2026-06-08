import TNLean.PEPS.RegionBlock.Recovery4

/-!
# Region physical-to-virtual recovery: the out-of-region endpoint of a boundary edge

This file develops the out-of-region endpoint of a boundary edge `f` of a region
`R`, the second endpoint feeding the region resonate step behind the normal PEPS
Fundamental Theorem (remaining obligation 4 of
`docs/paper-gaps/peps_normal_ft_section3_route.tex`).

A boundary edge `f` of `R` is also a boundary edge of the set complement
`univ \ R` (`regionBoundaryEdgeToCompl`), and its in-region endpoint with respect
to the complement is the out-of-region endpoint of `f` with respect to `R`. The
complement-side reading of the region-inserted coefficient
(`regionInsertedCoeff_eq_complementTwoBlock`, `TNLean.PEPS.RegionBlock.Recovery4`)
contracts the complement block first, so realizing the inserted coefficient
through the out-of-region endpoint is the complement-region instance of the
v-side realization `regionInsertedCoeff_eq_smul_op_regionStateVec`.

This file records the endpoint identity and the basic structural facts that the
complement-side realization needs, isolating the dependent-type reindexing
`univ \ (univ \ R) = R` into dedicated transport lemmas rather than threading it
through the realization argument.

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

/-! ### The out-of-region endpoint of a boundary edge

The out-of-region endpoint of a boundary edge `f` of `R` is the unique endpoint of
`f` lying outside `R`. It coincides with the in-region endpoint of `f` viewed as a
boundary edge of the set complement `univ \ R`. -/

/-- The out-of-region endpoint of a boundary edge `f` of `R`: the unique endpoint
of `f` not lying in `R`. -/
def regionBoundaryEdgeOutVertex (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) : V :=
  if f.1.1.1 ∈ R then f.1.1.2 else f.1.1.1

omit [Fintype V] [DecidableRel G.Adj] in
/-- The out-of-region endpoint of a boundary edge does not lie in `R`. -/
theorem regionBoundaryEdgeOutVertex_not_mem (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) :
    regionBoundaryEdgeOutVertex (G := G) R f ∉ R := by
  unfold regionBoundaryEdgeOutVertex
  rcases f.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos h1]; exact h2
  · rw [if_neg h1]; exact h1

omit [DecidableRel G.Adj] in
/-- The out-of-region endpoint of a boundary edge lies in the set complement
`univ \ R`. -/
theorem regionBoundaryEdgeOutVertex_mem_compl (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) :
    regionBoundaryEdgeOutVertex (G := G) R f ∈ Finset.univ \ R := by
  rw [Finset.mem_sdiff]
  exact ⟨Finset.mem_univ _, regionBoundaryEdgeOutVertex_not_mem (G := G) R f⟩

omit [DecidableRel G.Adj] in
/-- The out-of-region endpoint of `f` is the in-region endpoint of `f` viewed as a
boundary edge of the set complement `univ \ R`.

The complement membership predicate `w ∈ univ \ R` is `w ∉ R`, so the conditional
defining the in-region endpoint of the complement boundary edge selects the
endpoint of `f` outside `R`, which is the out-of-region endpoint of `f`. -/
theorem regionBoundaryEdgeInVertex_compl_eq_outVertex (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) :
    regionBoundaryEdgeInVertex (G := G) (Finset.univ \ R)
        (regionBoundaryEdgeToCompl (G := G) R f) =
      regionBoundaryEdgeOutVertex (G := G) R f := by
  rw [regionBoundaryEdgeInVertex, regionBoundaryEdgeOutVertex,
    regionBoundaryEdgeToCompl]
  rcases f.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos h1, if_neg (by rw [Finset.mem_sdiff]; push_neg; exact fun _ => h1)]
  · rw [if_neg h1, if_pos (by rw [Finset.mem_sdiff]; exact ⟨Finset.mem_univ _, h1⟩)]

end PEPS
end TNLean
