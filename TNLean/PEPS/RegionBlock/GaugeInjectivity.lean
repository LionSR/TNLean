import TNLean.PEPS.RegionBlock.GaugeBridge

/-!
# Region-blocked injectivity is preserved by a gauge

This file begins the gauge-absorbed analogue of the rectangle injectivity used in the final
comparison of the normal PEPS Fundamental Theorem (arXiv:1804.04964, Section 3, proof of Theorem 3,
lines 1519--1571 of `Papers/1804.04964/paper_normal.tex`).

The region comparison `regionComplement_comparison` consumes blocked-tensor injectivity of the
gauge-absorbed second tensor `applyGauge B X` over the comparison regions.  Because a gauge
preserves the closed state (`applyGauge_stateCoeff`), it also preserves blocked-region linear
independence: the gauge cancels pairwise on every interior edge of a region, and on every boundary
edge it acts as an invertible matrix on the open boundary leg, so the blocked-region tensor family
of `applyGauge B X` is the family of `B` precomposed with an invertible linear map of the boundary
configuration space.

This file supplies the foundational product regrouping: the product over the vertices of a region
`R` of a per-incidence factor regroups, edge by edge, into the contributions of each edge's
endpoints that lie in `R`.  An edge with both endpoints in `R` contributes both endpoint factors
(an interior edge); an edge with exactly one endpoint in `R` contributes only that endpoint's
factor (a boundary edge); an edge with no endpoint in `R` contributes nothing.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1571 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- **Region incidence product regrouped by edges.**

The product, over the vertices of a region `R`, of a per-incidence factor `f w ie` over the edges
`ie` incident to `w`, regroups edge by edge: each edge contributes its left-endpoint factor when
that endpoint lies in `R` (and `1` otherwise) times its right-endpoint factor when that endpoint
lies in `R` (and `1` otherwise).

This is the region-restricted analogue of `prod_incident_eq_prod_edge`.  An edge with both
endpoints in `R` contributes both factors; a boundary edge of `R` contributes exactly one; an edge
disjoint from `R` contributes nothing.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1544 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem prod_region_incident_eq_prod_edge (R : Finset V) (f : (w : V) → IncidentEdge G w → ℂ) :
    (∏ w : {w : V // w ∈ R}, ∏ ie : IncidentEdge G w.1, f w.1 ie) =
      ∏ e : Edge G,
        (if e.1.1 ∈ R then f e.1.1 (edgeLeftIncident (G := G) e) else 1) *
          (if e.1.2 ∈ R then f e.1.2 (edgeRightIncident (G := G) e) else 1) := by
  classical
  have hLHS : (∏ w : {w : V // w ∈ R}, ∏ ie : IncidentEdge G w.1, f w.1 ie) =
      ∏ w : V, ∏ ie : IncidentEdge G w,
        (if w ∈ R then f w ie else (1 : ℂ)) := by
    rw [Finset.prod_coe_sort R (fun w => ∏ ie : IncidentEdge G w, f w ie)]
    have hsub : (∏ w ∈ R, ∏ ie : IncidentEdge G w, (if w ∈ R then f w ie else (1 : ℂ)))
        = ∏ w ∈ (Finset.univ : Finset V), ∏ ie : IncidentEdge G w,
            (if w ∈ R then f w ie else (1 : ℂ)) :=
      Finset.prod_subset (Finset.subset_univ R) (fun w _ hw =>
        Finset.prod_eq_one (fun ie _ => by rw [if_neg hw]))
    rw [← hsub]
    refine Finset.prod_congr rfl (fun w hw => ?_)
    refine Finset.prod_congr rfl (fun ie _ => ?_)
    rw [if_pos hw]
  rw [hLHS, prod_incident_eq_prod_edge (G := G) (fun w ie => if w ∈ R then f w ie else (1 : ℂ))]

/-! ### Region-local configurations

The gauge cancellation over a region sums each gauged vertex tensor over its own inner virtual
indices.  Before the per-edge gauge contraction glues them, the inner indices form a
*region-local configuration*: one index per vertex of `R` and per incident edge, with the two
endpoints of an interior edge of `R` allowed to disagree.  This is the region-restricted
analogue of the vertex-wise local configurations used in the closed-state cancellation. -/

/-- A region-local configuration on `R`: one virtual index for each vertex `w ∈ R` and each
edge incident to `w`.  The two endpoints of an interior edge of `R` may carry different
indices; the per-edge gauge contraction glues them.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1544 of
`Papers/1804.04964/paper_normal.tex`. -/
abbrev RegionLocalConfig (B : Tensor G d) (R : Finset V) : Type _ :=
  (w : {w : V // w ∈ R}) → (ie : IncidentEdge G w.1) → Fin (B.bondDim ie.1)

/-- The region-local configuration read off a global virtual configuration. -/
def regionLocalOfGlobal (B : Tensor G d) (R : Finset V) (ζ : VirtualConfig B) :
    RegionLocalConfig (G := G) B R :=
  fun _w ie => ζ ie.1

omit [Fintype V] [DecidableRel G.Adj] in
/-- A non-boundary edge whose left endpoint lies in `R` has its right endpoint in `R`. -/
theorem nonboundary_right_mem (R : Finset V) {e : Edge G}
    (he : ¬ IsRegionBoundaryEdge (G := G) R e) (h1 : e.1.1 ∈ R) : e.1.2 ∈ R := by
  by_contra h2
  exact he (Or.inl ⟨h1, h2⟩)

omit [Fintype V] [DecidableRel G.Adj] in
/-- A non-boundary edge whose left endpoint lies outside `R` has its right endpoint
outside `R`. -/
theorem nonboundary_right_not_mem (R : Finset V) {e : Edge G}
    (he : ¬ IsRegionBoundaryEdge (G := G) R e) (h1 : e.1.1 ∉ R) : e.1.2 ∉ R := by
  intro h2
  exact he (Or.inr ⟨h1, h2⟩)

omit [Fintype V] [DecidableRel G.Adj] in
/-- A boundary edge whose left endpoint lies outside `R` has its right endpoint in `R`. -/
theorem boundary_right_mem (R : Finset V) {f : Edge G}
    (hf : IsRegionBoundaryEdge (G := G) R f) (h1 : f.1.1 ∉ R) : f.1.2 ∈ R := by
  rcases hf with ⟨hl, _⟩ | ⟨_, hr⟩
  · exact absurd hl h1
  · exact hr

/-- Read a region-local configuration at the in-region endpoint of a boundary edge of `R`. -/
noncomputable def regionLocalBoundary (B : Tensor G d) (R : Finset V)
    (ξ : RegionLocalConfig (G := G) B R)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) : Fin (B.bondDim f.1) :=
  if h : f.1.1.1 ∈ R then ξ ⟨f.1.1.1, h⟩ (edgeLeftIncident (G := G) f.1)
  else ξ ⟨f.1.1.2, boundary_right_mem (G := G) R f.2 h⟩ (edgeRightIncident (G := G) f.1)

omit [Fintype V] in
/-- The boundary reading of the region-local configuration of a global configuration is the
global label of the boundary edge. -/
theorem regionLocalBoundary_ofGlobal (B : Tensor G d) (R : Finset V) (ζ : VirtualConfig B)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) :
    regionLocalBoundary (G := G) B R (regionLocalOfGlobal (G := G) B R ζ) f = ζ f.1 := by
  rw [regionLocalBoundary]
  split <;> rfl

/-- A region-local configuration is *consistent* when the two endpoints of every interior
edge of `R` carry the same virtual index. -/
def IsRegionConsistent (B : Tensor G d) (R : Finset V)
    (ξ : RegionLocalConfig (G := G) B R) : Prop :=
  ∀ (e : Edge G) (h1 : e.1.1 ∈ R) (h2 : e.1.2 ∈ R),
    ξ ⟨e.1.1, h1⟩ (edgeLeftIncident (G := G) e) =
      ξ ⟨e.1.2, h2⟩ (edgeRightIncident (G := G) e)

/-! ### The surviving boundary gauge and its inverse

On a boundary edge of `R` only the endpoint inside `R` carries a gauge factor, so after the
outer sum the edge retains a single invertible matrix coupling the pinned outer label to the
free inner label: the gauge `X_f` when the in-region endpoint is the left endpoint of `f`,
and `(X_f⁻¹)ᵀ` when it is the right one (per the orientation convention of `edgeGaugeAt`). -/

/-- The surviving gauge matrix on a boundary edge of `R`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1544 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def regionBoundaryGauge (B : Tensor G d)
    (X : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) :
    Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ :=
  if f.1.1.1 ∈ R then ↑(X f.1) else (↑((X f.1)⁻¹))ᵀ

/-- The two-sided matrix inverse of the surviving boundary gauge. -/
noncomputable def regionBoundaryGaugeInv (B : Tensor G d)
    (X : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) :
    Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ :=
  if f.1.1.1 ∈ R then ↑((X f.1)⁻¹) else (↑(X f.1))ᵀ

omit [Fintype V] in
/-- The surviving boundary gauge times its inverse is the identity. -/
theorem regionBoundaryGauge_mul_inv (B : Tensor G d)
    (X : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) :
    regionBoundaryGauge (G := G) B X R f * regionBoundaryGaugeInv (G := G) B X R f = 1 := by
  rw [regionBoundaryGauge, regionBoundaryGaugeInv]
  by_cases h : f.1.1.1 ∈ R
  · rw [if_pos h, if_pos h]
    simp
  · rw [if_neg h, if_neg h, ← Matrix.transpose_mul]
    simp

end PEPS
end TNLean
