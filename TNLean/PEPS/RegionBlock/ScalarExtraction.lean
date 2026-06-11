import TNLean.PEPS.RegionBlock.InsertResidual

/-!
# The inserted-site scalar extraction for the normal PEPS Fundamental Theorem

This file performs the scalar-extraction step of the normal PEPS Fundamental
Theorem's final comparison (arXiv:1804.04964, Section 3, proof of Theorem 3,
lines 1544--1571 of `Papers/1804.04964/paper_normal.tex`).

The region comparison `regionComplement_comparison` delivers, at a region `R` and
at the one-site-larger region `insert v R`, the two scalar proportionalities
`A_R = c_R · B̃_R` and `A_S = c_S · B̃_S` of the blocked weights.  Feeding both
through the landed inserted-site factorization
`insertOuterBondProd_smul_regionBlockedWeight_insert` cancels the bond-only
inserted-site multiplicity and leaves, at every inserted-site local configuration
`η`, the inserted-site tensor of `A` against the bridge-label blocked weight of `R`
matched with `c_S` against the inserted-site tensor of `B̃` against the same
bridge-label weight, scaled by `c_R` after substituting the `R`-proportionality.

The bridge labels of the *consistent* local configurations `η` at `v` are in
bijection with `η` itself: a consistent `η` is determined by the bridge label on
the `v`-incident edges that bound `R` and by `μ` on the `v`-incident edges that do
not.  Linear independence of `B̃`'s `R`-blocked family therefore separates the
`η`-coefficients to a single term each, yielding the per-vertex relation
`A.component v η = (c_S / c_R) · B̃.component v η` at every local configuration `η`.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, proof of
  Theorem 3, lines 1544--1571 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### Consistent local configurations are determined by their bridge label

A local configuration `η` at the inserted site `v` is read by the bridge label
`boundaryLabelOfInsert μ η` on exactly the `v`-incident edges that bound `R`; the
remaining `v`-incident edges run from `v` to a vertex outside `insert v R`, where
inserted-site consistency pins `η` to `μ`.  Hence a consistent `η` is determined by
`μ` together with its bridge label, and two consistent local configurations with
the same bridge label coincide. -/

omit [Fintype V] [DecidableRel G.Adj] in
/-- A `v`-incident edge bounds `R` exactly when it is incident to `R`: its `R`-side
endpoint lies in `R` and its `v` endpoint does not. -/
theorem isRegionBoundaryEdge_of_vIncident_regionIncident (R : Finset V) {v : V}
    (hv : v ∉ R) {e : Edge G} (hev : e.1.1 = v ∨ e.1.2 = v)
    (hinc : IsRegionIncidentEdge (G := G) R e) :
    IsRegionBoundaryEdge (G := G) R e := by
  rcases hev with he | he
  · -- `e.1.1 = v ∉ R`; incidence forces the other endpoint into `R`.
    have h1 : e.1.1 ∉ R := by rw [he]; exact hv
    rcases hinc with h | h
    · exact absurd h h1
    · exact Or.inr ⟨h1, h⟩
  · have h2 : e.1.2 ∉ R := by rw [he]; exact hv
    rcases hinc with h | h
    · exact Or.inl ⟨h, h2⟩
    · exact absurd h h2

omit [Fintype V] in
/-- **Inserted-site consistency pins a local configuration to its bridge label.**

Under inserted-site consistency, the local configuration `η` at `v` is determined
by `μ` and the bridge label `boundaryLabelOfInsert μ η`: on a `v`-incident edge that
bounds `R` it is read from the bridge label, and on a `v`-incident edge that does not
bound `R` (so runs to a vertex outside `insert v R`) consistency reads it from `μ`. -/
theorem localConfig_eq_of_insertConsistent (A : Tensor G d) (R : Finset V) {v : V}
    (hv : v ∉ R)
    (μ : RegionBoundaryConfig (G := G) A (insert v R)) (η η' : LocalVirtualConfig A v)
    (hcons : InsertConsistent (G := G) A R μ η)
    (hcons' : InsertConsistent (G := G) A R μ η')
    (hbridge : boundaryLabelOfInsert (G := G) A R hv μ η =
      boundaryLabelOfInsert (G := G) A R hv μ η') :
    η = η' := by
  classical
  funext ie
  by_cases hinc : IsRegionIncidentEdge (G := G) R ie.1
  · -- `v`-incident and `R`-incident: an `R`-boundary edge; the bridge label reads `η`.
    have hb : IsRegionBoundaryEdge (G := G) R ie.1 :=
      isRegionBoundaryEdge_of_vIncident_regionIncident (G := G) R hv ie.2 hinc
    have h1 : boundaryLabelOfInsert (G := G) A R hv μ η ⟨ie.1, hb⟩ = η ie := by
      rw [boundaryLabelOfInsert, dif_pos ie.2]
    have h2 : boundaryLabelOfInsert (G := G) A R hv μ η' ⟨ie.1, hb⟩ = η' ie := by
      rw [boundaryLabelOfInsert, dif_pos ie.2]
    rw [← h1, ← h2, congrFun hbridge ⟨ie.1, hb⟩]
  · -- `v`-incident, non-`R`-incident: a `v`-incident `insert v R`-boundary edge.
    have hb : IsRegionBoundaryEdge (G := G) (insert v R) ie.1 :=
      isRegionBoundaryEdge_insert_of_vIncident_not_regionIncident (G := G) R ie.2 hinc
    have h1 : η ie = μ ⟨ie.1, hb⟩ := (hcons ⟨ie.1, hb⟩ ie.2).symm
    have h2 : η' ie = μ ⟨ie.1, hb⟩ := (hcons' ⟨ie.1, hb⟩ ie.2).symm
    rw [h1, h2]

end PEPS
end TNLean
