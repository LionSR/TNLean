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

end PEPS
end TNLean
