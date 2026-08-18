/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
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
        Finset.prod_eq_one (fun ie _ => by rw [ite_eq_right hw]))
    rw [← hsub]
    refine Finset.prod_congr rfl (fun w hw => ?_)
    refine Finset.prod_congr rfl (fun ie _ => ?_)
    rw [ite_eq_left hw]
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
private theorem regionLocalBoundary_eq_left (B : Tensor G d) (R : Finset V)
    (ξ : RegionLocalConfig (G := G) B R)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) (h : f.1.1.1 ∈ R) :
    regionLocalBoundary (G := G) B R ξ f =
      ξ ⟨f.1.1.1, h⟩ (edgeLeftIncident (G := G) f.1) := by
  unfold regionLocalBoundary
  exact dite_eq_left h

omit [Fintype V] in
private theorem regionLocalBoundary_eq_right (B : Tensor G d) (R : Finset V)
    (ξ : RegionLocalConfig (G := G) B R)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) (h : f.1.1.1 ∉ R) :
    regionLocalBoundary (G := G) B R ξ f =
      ξ ⟨f.1.1.2, boundary_right_mem (G := G) R f.2 h⟩
        (edgeRightIncident (G := G) f.1) := by
  unfold regionLocalBoundary
  exact dite_eq_right h

omit [Fintype V] in
/-- The boundary reading of the region-local configuration of a global configuration is the
global label of the boundary edge. -/
theorem regionLocalBoundary_ofGlobal (B : Tensor G d) (R : Finset V) (ζ : VirtualConfig B)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) :
    regionLocalBoundary (G := G) B R (regionLocalOfGlobal (G := G) B R ζ) f = ζ f.1 := by
  by_cases h : f.1.1.1 ∈ R
  · exact (regionLocalBoundary_eq_left B R _ f h).trans rfl
  · exact (regionLocalBoundary_eq_right B R _ f h).trans rfl

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
  · rw [ite_eq_left h, ite_eq_left h]
    simp
  · rw [ite_eq_right h, ite_eq_right h, ← Matrix.transpose_mul]
    simp

/-! ### Expanding the gauged region product

Each gauged vertex tensor of the region is a sum over its own inner indices; exchanging the
region product with these sums produces one sum over region-local configurations, and the
gauge factors regroup edge by edge through `prod_region_incident_eq_prod_edge`. -/

/-- The product over the region of gauged vertex tensors, read against a global outer
configuration, expands into a sum over region-local inner configurations with one
gauge-matrix factor on each half-edge of the region.

This is the region-restricted analogue of the vertex-wise expansion used in the closed-state
gauge cancellation.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1544 of
`Papers/1804.04964/paper_normal.tex`. -/
lemma prod_gaugeVertex_region_eq_sum_local (B : Tensor G d)
    (X : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ) (R : Finset V)
    (ζ : VirtualConfig B) (τ : RegionPhysicalConfig (V := V) (d := d) R) :
    (∏ w : {w : V // w ∈ R}, gaugeVertex B X w.1 (fun ie => ζ ie.1) (τ w)) =
      ∑ ξ : RegionLocalConfig (G := G) B R,
        ∏ w : {w : V // w ∈ R},
          (∏ ie : IncidentEdge G w.1, edgeGaugeAt B X w.1 ie (ζ ie.1) (ξ w ie)) *
            B.component w.1 (ξ w) (τ w) := by
  classical
  simp_rw [gaugeVertex]
  rw [show (∏ w : {w : V // w ∈ R},
        ∑ η' : (ie : IncidentEdge G w.1) → Fin (B.bondDim ie.1),
          (∏ ie : IncidentEdge G w.1, edgeGaugeAt B X w.1 ie (ζ ie.1) (η' ie)) *
            B.component w.1 η' (τ w)) =
      ∑ ξ : RegionLocalConfig (G := G) B R,
        ∏ w : {w : V // w ∈ R},
          (∏ ie : IncidentEdge G w.1, edgeGaugeAt B X w.1 ie (ζ ie.1) (ξ w ie)) *
            B.component w.1 (ξ w) (τ w) by
    simpa only [Fintype.piFinset_univ, RegionLocalConfig] using
      (Finset.prod_univ_sum (fun w : {w : V // w ∈ R} => Finset.univ)
        (fun w η' =>
          (∏ ie : IncidentEdge G w.1, edgeGaugeAt B X w.1 ie (ζ ie.1) (η' ie)) *
            B.component w.1 η' (τ w)))]

/-- The two endpoint gauge factors an edge contributes to the gauged region product: each
endpoint lying in `R` contributes the oriented gauge matrix entry coupling the outer label
`z` to the inner reading of the region-local configuration at that endpoint; an endpoint
outside `R` contributes nothing. -/
noncomputable def regionGaugeFactor (B : Tensor G d)
    (X : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ) (R : Finset V)
    (ξ : RegionLocalConfig (G := G) B R) (e : Edge G) (z : Fin (B.bondDim e)) : ℂ :=
  (if h : e.1.1 ∈ R then
      edgeGaugeAt B X e.1.1 (edgeLeftIncident (G := G) e) z
        (ξ ⟨e.1.1, h⟩ (edgeLeftIncident (G := G) e))
    else 1) *
    if h : e.1.2 ∈ R then
      edgeGaugeAt B X e.1.2 (edgeRightIncident (G := G) e) z
        (ξ ⟨e.1.2, h⟩ (edgeRightIncident (G := G) e))
    else 1

/-- The gauge factors of the region product regroup edge by edge: the product over the
vertices of `R` of the gauge factors on their incident half-edges is the product over all
edges of the two endpoint contributions `regionGaugeFactor`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1544 of
`Papers/1804.04964/paper_normal.tex`. -/
lemma prod_region_edgeGauge_eq_prod_factor (B : Tensor G d)
    (X : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ) (R : Finset V)
    (ζ : VirtualConfig B) (ξ : RegionLocalConfig (G := G) B R) :
    (∏ w : {w : V // w ∈ R}, ∏ ie : IncidentEdge G w.1,
        edgeGaugeAt B X w.1 ie (ζ ie.1) (ξ w ie)) =
      ∏ e : Edge G, regionGaugeFactor (G := G) B X R ξ e (ζ e) := by
  classical
  rw [show (∏ w : {w : V // w ∈ R}, ∏ ie : IncidentEdge G w.1,
        edgeGaugeAt B X w.1 ie (ζ ie.1) (ξ w ie)) =
      ∏ w : {w : V // w ∈ R}, ∏ ie : IncidentEdge G w.1,
        (fun (v : V) (ie : IncidentEdge G v) =>
          if h : v ∈ R then edgeGaugeAt B X v ie (ζ ie.1) (ξ ⟨v, h⟩ ie) else 1) w.1 ie from
    Finset.prod_congr rfl fun w _ => Finset.prod_congr rfl fun ie _ => by
      change edgeGaugeAt B X w.1 ie (ζ ie.1) (ξ w ie) =
        if h : w.1 ∈ R then edgeGaugeAt B X w.1 ie (ζ ie.1) (ξ ⟨w.1, h⟩ ie) else 1
      rw [dite_eq_left w.2]]
  rw [prod_region_incident_eq_prod_edge R
    (fun (v : V) (ie : IncidentEdge G v) =>
      if h : v ∈ R then edgeGaugeAt B X v ie (ζ ie.1) (ξ ⟨v, h⟩ ie) else 1)]
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [regionGaugeFactor]
  by_cases h1 : e.1.1 ∈ R <;> by_cases h2 : e.1.2 ∈ R <;> simp [h1, h2]

/-! ### Factorizing the boundary-pinned outer sum

The outer sum of the blocked-region weight runs over global virtual configurations pinned to
the boundary configuration on the boundary edges of `R`.  Such configurations are exactly the
free labels on the non-boundary edges, so a per-edge product summed over them factorizes:
each boundary edge contributes its pinned factor, each non-boundary edge the sum of its
factor over the free label. -/

/-- Global virtual configurations restricting to `bdry` on the boundary edges of `R` are the
assignments of free labels to the non-boundary edges. -/
noncomputable def regionBoundaryFiberEquiv (B : Tensor G d) (R : Finset V)
    (bdry : RegionBoundaryConfig (G := G) B R) :
    {ζ : VirtualConfig B // regionBoundaryLabel (G := G) B R ζ = bdry} ≃
      ((e : {e : Edge G // ¬ IsRegionBoundaryEdge (G := G) R e}) → Fin (B.bondDim e.1)) where
  toFun ζ e := ζ.1 e.1
  invFun h := ⟨fun e =>
      if hb : IsRegionBoundaryEdge (G := G) R e then bdry ⟨e, hb⟩ else h ⟨e, hb⟩, by
    funext f
    rw [regionBoundaryLabel_apply, dite_eq_left f.2]⟩
  left_inv ζ := by
    apply Subtype.ext
    funext e
    change (if hb : IsRegionBoundaryEdge (G := G) R e then bdry ⟨e, hb⟩ else ζ.1 e) = ζ.1 e
    by_cases hb : IsRegionBoundaryEdge (G := G) R e
    · rw [dite_eq_left hb]
      exact (congrFun ζ.2 ⟨e, hb⟩).symm
    · rw [dite_eq_right hb]
  right_inv h := by
    funext e
    change (if hb : IsRegionBoundaryEdge (G := G) R e.1 then bdry ⟨e.1, hb⟩ else h ⟨e.1, hb⟩) =
      h e
    rw [dite_eq_right e.2]

open scoped Classical in
/-- **Boundary-pinned factorization of the outer sum.**  A per-edge product summed over the
global virtual configurations pinned to `bdry` on the boundary edges of `R` factorizes into
the pinned boundary factors times, for each non-boundary edge, the sum of its factor over
the free label.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1544 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem sum_boundaryFiber_prod_edge (B : Tensor G d) (R : Finset V)
    (bdry : RegionBoundaryConfig (G := G) B R)
    (g : (e : Edge G) → Fin (B.bondDim e) → ℂ) :
    (∑ ζ ∈ Finset.univ.filter
        (fun ζ : VirtualConfig B => regionBoundaryLabel (G := G) B R ζ = bdry),
      ∏ e : Edge G, g e (ζ e)) =
      (∏ f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}, g f.1 (bdry f)) *
        ∏ e : {e : Edge G // ¬ IsRegionBoundaryEdge (G := G) R e},
          ∑ z : Fin (B.bondDim e.1), g e.1 z := by
  classical
  -- View the pinned sum as a sum over the boundary fiber subtype.
  rw [Finset.sum_subtype (Finset.univ.filter
      (fun ζ : VirtualConfig B => regionBoundaryLabel (G := G) B R ζ = bdry))
    (p := fun ζ : VirtualConfig B => regionBoundaryLabel (G := G) B R ζ = bdry)
    (fun ζ => by simp) (fun ζ => ∏ e : Edge G, g e (ζ e))]
  -- Reindex the fiber by the free labels on the non-boundary edges.
  rw [Fintype.sum_equiv (regionBoundaryFiberEquiv (G := G) B R bdry)
    (fun ζ => ∏ e : Edge G, g e (ζ.1 e))
    (fun h => ∏ e : Edge G,
      g e (if hb : IsRegionBoundaryEdge (G := G) R e then bdry ⟨e, hb⟩ else h ⟨e, hb⟩))
    (fun ζ => Finset.prod_congr rfl fun e _ => by
      by_cases hb : IsRegionBoundaryEdge (G := G) R e
      · rw [dite_eq_left hb]
        exact congrArg (g e) (congrFun ζ.2 ⟨e, hb⟩)
      · rw [dite_eq_right hb]
        rfl)]
  -- Split each edge product into the pinned boundary part and the free part.
  rw [Finset.sum_congr rfl (fun h _ => show
      (∏ e : Edge G,
        g e (if hb : IsRegionBoundaryEdge (G := G) R e then bdry ⟨e, hb⟩ else h ⟨e, hb⟩)) =
      (∏ f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}, g f.1 (bdry f)) *
        ∏ e : {e : Edge G // ¬ IsRegionBoundaryEdge (G := G) R e}, g e.1 (h e) from by
    rw [← Fintype.prod_subtype_mul_prod_subtype
      (fun e : Edge G => IsRegionBoundaryEdge (G := G) R e)
      (fun e =>
        g e (if hb : IsRegionBoundaryEdge (G := G) R e then bdry ⟨e, hb⟩ else h ⟨e, hb⟩))]
    congr 1
    · exact Finset.prod_congr rfl fun f _ => by rw [dite_eq_left f.2]
    · exact Finset.prod_congr rfl fun e _ => by rw [dite_eq_right e.2])]
  -- Pull the pinned factor out and exchange the free sum with the edge product.
  rw [← Finset.mul_sum]
  congr 1
  simpa only [Fintype.piFinset_univ] using
    (Finset.prod_univ_sum
      (fun e : {e : Edge G // ¬ IsRegionBoundaryEdge (G := G) R e} => Finset.univ)
      (fun e z => g e.1 z)).symm

/-! ### Evaluating the per-edge factors

On a boundary edge only the in-region endpoint carries a gauge factor, which becomes the
surviving boundary gauge.  On a non-boundary edge the outer label is summed: an interior
edge of `R` carries the gauge at one endpoint and its inverse-transpose at the other, which
contract to the gluing delta of the two endpoint readings; an edge disjoint from `R` carries
no factor, and the free outer label is merely counted. -/

omit [Fintype V] in
/-- The oriented endpoint gauge at the left endpoint of an edge is the gauge matrix. -/
theorem edgeGaugeAt_left (B : Tensor G d)
    (X : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ) (e : Edge G) :
    edgeGaugeAt B X e.1.1 (edgeLeftIncident (G := G) e) =
      (X e : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) := by
  simp [edgeGaugeAt]

omit [Fintype V] in
/-- The oriented endpoint gauge at the right endpoint of an edge is the transpose of the
inverse gauge matrix. -/
theorem edgeGaugeAt_right (B : Tensor G d)
    (X : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ) (e : Edge G) :
    edgeGaugeAt B X e.1.2 (edgeRightIncident (G := G) e) =
      (((X e)⁻¹ : GL (Fin (B.bondDim e)) ℂ) :
        Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ)ᵀ := by
  have hne : ¬ e.1.1 = e.1.2 := ne_of_lt e.2.1
  simp only [edgeGaugeAt, edgeRightIncident, hne, ↓reduceIte]
  rfl

omit [Fintype V] in
/-- On a boundary edge of `R`, the per-edge gauge factor is the surviving boundary gauge
entry coupling the outer label to the in-region boundary reading.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1544 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionGaugeFactor_boundary (B : Tensor G d)
    (X : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ) (R : Finset V)
    (ξ : RegionLocalConfig (G := G) B R)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) (z : Fin (B.bondDim f.1)) :
    regionGaugeFactor (G := G) B X R ξ f.1 z =
      regionBoundaryGauge (G := G) B X R f z (regionLocalBoundary (G := G) B R ξ f) := by
  by_cases h1 : f.1.1.1 ∈ R
  · have h2 : f.1.1.2 ∉ R := by
      rcases f.2 with ⟨_, hr⟩ | ⟨hl, _⟩
      · exact hr
      · exact absurd h1 hl
    let q : Fin (B.bondDim f.1) :=
      ξ ⟨f.1.1.1, h1⟩ (edgeLeftIncident (G := G) f.1)
    have hfactor : regionGaugeFactor (G := G) B X R ξ f.1 z =
        edgeGaugeAt B X f.1.1.1 (edgeLeftIncident (G := G) f.1) z q := by
      unfold regionGaugeFactor
      exact (congrArg₂ (· * ·) (dite_eq_left h1) (dite_eq_right h2)).trans (mul_one _)
    have hboundary : regionBoundaryGauge (G := G) B X R f z
        (regionLocalBoundary (G := G) B R ξ f) =
          (X f.1 : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) z q := by
      unfold regionBoundaryGauge
      calc
        _ = (X f.1 : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) z
            (regionLocalBoundary (G := G) B R ξ f) :=
          congrArg (fun Y : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ =>
            Y z (regionLocalBoundary (G := G) B R ξ f)) (ite_eq_left h1)
        _ = _ := congrArg
          (fun x => (X f.1 : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) z x)
          (regionLocalBoundary_eq_left B R ξ f h1)
    exact hfactor.trans ((congrFun (congrFun (edgeGaugeAt_left B X f.1) z) q).trans hboundary.symm)
  · have h2 : f.1.1.2 ∈ R := boundary_right_mem (G := G) R f.2 h1
    let q : Fin (B.bondDim f.1) :=
      ξ ⟨f.1.1.2, h2⟩ (edgeRightIncident (G := G) f.1)
    have hfactor : regionGaugeFactor (G := G) B X R ξ f.1 z =
        edgeGaugeAt B X f.1.1.2 (edgeRightIncident (G := G) f.1) z q := by
      unfold regionGaugeFactor
      exact (congrArg₂ (· * ·) (dite_eq_right h1) (dite_eq_left h2)).trans (one_mul _)
    have hboundary : regionBoundaryGauge (G := G) B X R f z
        (regionLocalBoundary (G := G) B R ξ f) =
          (((X f.1)⁻¹ : GL (Fin (B.bondDim f.1)) ℂ) :
            Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)ᵀ z q := by
      unfold regionBoundaryGauge
      calc
        _ = (((X f.1)⁻¹ : GL (Fin (B.bondDim f.1)) ℂ) :
              Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)ᵀ z
            (regionLocalBoundary (G := G) B R ξ f) :=
          congrArg (fun Y : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ =>
            Y z (regionLocalBoundary (G := G) B R ξ f)) (ite_eq_right h1)
        _ = _ := congrArg
          (fun x => (((X f.1)⁻¹ : GL (Fin (B.bondDim f.1)) ℂ) :
            Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)ᵀ z x)
          (regionLocalBoundary_eq_right B R ξ f h1)
    exact hfactor.trans ((congrFun (congrFun (edgeGaugeAt_right B X f.1) z) q).trans hboundary.symm)

open scoped Classical in
/-- The contribution of a non-boundary edge to the gauged region weight after the outer
sum: an interior edge of `R` contributes the gluing delta of its two endpoint readings, an
edge disjoint from `R` contributes its bond dimension. -/
noncomputable def regionEdgeContraction (B : Tensor G d) (R : Finset V)
    (ξ : RegionLocalConfig (G := G) B R) (e : Edge G) : ℂ :=
  if IsRegionIncidentEdge (G := G) R e then
    (if ∀ (h1 : e.1.1 ∈ R) (h2 : e.1.2 ∈ R),
        ξ ⟨e.1.1, h1⟩ (edgeLeftIncident (G := G) e) =
          ξ ⟨e.1.2, h2⟩ (edgeRightIncident (G := G) e) then 1 else 0)
  else (B.bondDim e : ℂ)

omit [Fintype V] in
open scoped Classical in
/-- Summing the per-edge gauge factor of a non-boundary edge over the free outer label: on
an interior edge of `R` the gauge and its inverse contract to the gluing delta of the two
endpoint readings, on an edge disjoint from `R` the sum counts the bond dimension.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1544 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem sum_regionGaugeFactor_nonboundary (B : Tensor G d)
    (X : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ) (R : Finset V)
    (ξ : RegionLocalConfig (G := G) B R)
    (e : {e : Edge G // ¬ IsRegionBoundaryEdge (G := G) R e}) :
    (∑ z : Fin (B.bondDim e.1), regionGaugeFactor (G := G) B X R ξ e.1 z) =
      regionEdgeContraction (G := G) B R ξ e.1 := by
  by_cases h1 : e.1.1.1 ∈ R
  · have h2 : e.1.1.2 ∈ R := nonboundary_right_mem (G := G) R e.2 h1
    have hinc : IsRegionIncidentEdge (G := G) R e.1 := Or.inl h1
    rw [regionEdgeContraction, ite_eq_left hinc]
    let a : Fin (B.bondDim e.1) :=
      ξ ⟨e.1.1.1, h1⟩ (edgeLeftIncident (G := G) e.1)
    let b : Fin (B.bondDim e.1) :=
      ξ ⟨e.1.1.2, h2⟩ (edgeRightIncident (G := G) e.1)
    calc
      (∑ z : Fin (B.bondDim e.1), regionGaugeFactor (G := G) B X R ξ e.1 z) =
          ∑ z : Fin (B.bondDim e.1),
            (X e.1 : Matrix (Fin (B.bondDim e.1)) (Fin (B.bondDim e.1)) ℂ) z a *
              ((X e.1 : Matrix (Fin (B.bondDim e.1)) (Fin (B.bondDim e.1)) ℂ)⁻¹) b z := by
        refine Finset.sum_congr rfl fun z _ => ?_
        unfold regionGaugeFactor
        simp only [h1, h2, dite_true]
        change edgeGaugeAt B X e.1.1.1 (edgeLeftIncident (G := G) e.1) z a *
            edgeGaugeAt B X e.1.1.2 (edgeRightIncident (G := G) e.1) z b = _
        calc
          _ = (X e.1 : Matrix (Fin (B.bondDim e.1)) (Fin (B.bondDim e.1)) ℂ) z a *
              (((X e.1)⁻¹ : GL (Fin (B.bondDim e.1)) ℂ) :
                Matrix (Fin (B.bondDim e.1)) (Fin (B.bondDim e.1)) ℂ)ᵀ z b :=
            congrArg₂ (· * ·)
              (congrFun (congrFun (edgeGaugeAt_left B X e.1) z) a)
              (congrFun (congrFun (edgeGaugeAt_right B X e.1) z) b)
          _ = _ := congrArg
            (fun Y : Matrix (Fin (B.bondDim e.1)) (Fin (B.bondDim e.1)) ℂ =>
              (X e.1 : Matrix (Fin (B.bondDim e.1)) (Fin (B.bondDim e.1)) ℂ) z a * Y b z)
            (Matrix.GeneralLinearGroup.coe_inv (X e.1))
      _ = if a = b then 1 else 0 := by
        by_cases hab : a = b
        · simpa only [ite_eq_left hab] using gauge_sum_left_right_matrix_inv (X e.1) a b
        · simpa only [ite_eq_right hab] using gauge_sum_left_right_matrix_inv (X e.1) a b
      _ = if ∀ (h1 : e.1.1.1 ∈ R) (h2 : e.1.1.2 ∈ R),
          ξ ⟨e.1.1.1, h1⟩ (edgeLeftIncident (G := G) e.1) =
            ξ ⟨e.1.1.2, h2⟩ (edgeRightIncident (G := G) e.1) then 1 else 0 := by
        refine if_congr ?_ rfl rfl
        constructor
        · intro hab _ _
          exact hab
        · intro h
          exact h h1 h2
  · have h2 : e.1.1.2 ∉ R := nonboundary_right_not_mem (G := G) R e.2 h1
    have hninc : ¬ IsRegionIncidentEdge (G := G) R e.1 :=
      fun hinc => hinc.elim (fun h => absurd h h1) (fun h => absurd h h2)
    rw [regionEdgeContraction, ite_eq_right hninc]
    rw [Finset.sum_congr rfl (fun z _ =>
      show regionGaugeFactor (G := G) B X R ξ e.1 z = 1 by
        rw [regionGaugeFactor, dite_eq_right h1, dite_eq_right h2, mul_one])]
    simp

/-! ### Collapsing the gluing deltas to a global configuration

After the per-edge contraction, the interior deltas force a region-local configuration to be
consistent, and a consistent configuration is the region reading of a global virtual
configuration, each such reading being attained by one global configuration for every choice
of free labels on the edges not incident to `R`. -/

/-- The bond-dimension product over the edges not incident to `R`: the multiplicity with
which a consistent region-local configuration is read off global virtual configurations. -/
noncomputable def regionNonincidentBondProd (B : Tensor G d) (R : Finset V) : ℕ :=
  ∏ e ∈ Finset.univ.filter (fun e : Edge G => ¬ IsRegionIncidentEdge (G := G) R e),
    B.bondDim e

open scoped Classical in
/-- **The contraction product collapses to consistency.**  Over the non-boundary edges, the
per-edge contractions multiply to the bond-dimension product over the edges not incident to
`R` when the region-local configuration is consistent, and to zero otherwise.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1544 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem prod_regionEdgeContraction (B : Tensor G d) (R : Finset V)
    (ξ : RegionLocalConfig (G := G) B R) :
    (∏ e : {e : Edge G // ¬ IsRegionBoundaryEdge (G := G) R e},
        regionEdgeContraction (G := G) B R ξ e.1) =
      if IsRegionConsistent (G := G) B R ξ
      then (regionNonincidentBondProd (G := G) B R : ℂ) else 0 := by
  classical
  -- Split each contraction into its gluing delta and its counting factor.
  have hsplit : ∀ e : {e : Edge G // ¬ IsRegionBoundaryEdge (G := G) R e},
      regionEdgeContraction (G := G) B R ξ e.1 =
        (if ∀ (h1 : e.1.1.1 ∈ R) (h2 : e.1.1.2 ∈ R),
            ξ ⟨e.1.1.1, h1⟩ (edgeLeftIncident (G := G) e.1) =
              ξ ⟨e.1.1.2, h2⟩ (edgeRightIncident (G := G) e.1) then (1 : ℂ) else 0) *
          if IsRegionIncidentEdge (G := G) R e.1 then (1 : ℂ) else (B.bondDim e.1 : ℂ) := by
    intro e
    rw [regionEdgeContraction]
    by_cases hinc : IsRegionIncidentEdge (G := G) R e.1
    · rw [ite_eq_left hinc, ite_eq_left hinc, mul_one]
    · rw [ite_eq_right hinc, ite_eq_right hinc,
        ite_eq_left (fun h1 _ => absurd h1 (fun hm => hinc (Or.inl hm))), one_mul]
  rw [Finset.prod_congr rfl (fun e _ => hsplit e), Finset.prod_mul_distrib,
    Fintype.prod_boole, ite_mul, one_mul, zero_mul]
  refine if_congr ?_ ?_ rfl
  · -- The per-edge deltas over the non-boundary edges are consistency.
    constructor
    · intro h e h1 h2
      have hb : ¬ IsRegionBoundaryEdge (G := G) R e := fun hb => by
        rcases hb with ⟨_, hr⟩ | ⟨hl, _⟩
        · exact hr h2
        · exact hl h1
      exact h ⟨e, hb⟩ h1 h2
    · intro h e h1 h2
      exact h e.1 h1 h2
  · -- The counting factors multiply to the non-incident bond product.
    rw [← Finset.prod_subtype (Finset.univ.filter
        (fun e : Edge G => ¬ IsRegionBoundaryEdge (G := G) R e))
      (fun e => by simp)
      (fun e => if IsRegionIncidentEdge (G := G) R e then (1 : ℂ) else (B.bondDim e : ℂ))]
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.filter_filter,
      regionNonincidentBondProd, Nat.cast_prod]
    refine Finset.prod_congr (Finset.ext fun e => ?_) (fun _ _ => rfl)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨not_boundary_of_not_incident (G := G) R h, h⟩⟩

/-- Read a region-local configuration at an `R`-incident edge: at the left endpoint when it
lies in `R`, at the right endpoint otherwise. -/
noncomputable def regionIncidentRead (B : Tensor G d) (R : Finset V)
    (ξ : RegionLocalConfig (G := G) B R) (e : Edge G)
    (he : IsRegionIncidentEdge (G := G) R e) : Fin (B.bondDim e) :=
  if h1 : e.1.1 ∈ R then ξ ⟨e.1.1, h1⟩ (edgeLeftIncident (G := G) e)
  else ξ ⟨e.1.2, he.resolve_left h1⟩ (edgeRightIncident (G := G) e)

omit [Fintype V] in
private theorem regionIncidentRead_eq_left (B : Tensor G d) (R : Finset V)
    (ξ : RegionLocalConfig (G := G) B R) (e : Edge G)
    (he : IsRegionIncidentEdge (G := G) R e) (h1 : e.1.1 ∈ R) :
    regionIncidentRead (G := G) B R ξ e he =
      (ξ ⟨e.1.1, h1⟩ (edgeLeftIncident (G := G) e) : Fin (B.bondDim e)) := by
  unfold regionIncidentRead
  exact dite_eq_left h1

omit [Fintype V] in
private theorem regionIncidentRead_eq_right (B : Tensor G d) (R : Finset V)
    (ξ : RegionLocalConfig (G := G) B R) (e : Edge G)
    (he : IsRegionIncidentEdge (G := G) R e) (h1 : e.1.1 ∉ R) :
    regionIncidentRead (G := G) B R ξ e he =
      (ξ ⟨e.1.2, he.resolve_left h1⟩ (edgeRightIncident (G := G) e) : Fin (B.bondDim e)) := by
  unfold regionIncidentRead
  exact dite_eq_right h1

open scoped Classical in
/-- Rebuild a global virtual configuration from a region-local configuration on the
`R`-incident edges and free labels on the remaining edges. -/
noncomputable def regionGlobalOfLocal (B : Tensor G d) (R : Finset V)
    (ξ : RegionLocalConfig (G := G) B R)
    (h : (e : {e : Edge G // ¬ IsRegionIncidentEdge (G := G) R e}) → Fin (B.bondDim e.1)) :
    VirtualConfig B :=
  fun e => if he : IsRegionIncidentEdge (G := G) R e then
      regionIncidentRead (G := G) B R ξ e he
    else h ⟨e, he⟩

omit [Fintype V] in
private theorem regionGlobalOfLocal_eq_incident (B : Tensor G d) (R : Finset V)
    (ξ : RegionLocalConfig (G := G) B R)
    (h : (e : {e : Edge G // ¬ IsRegionIncidentEdge (G := G) R e}) → Fin (B.bondDim e.1))
    (e : Edge G) (he : IsRegionIncidentEdge (G := G) R e) :
    regionGlobalOfLocal (G := G) B R ξ h e = regionIncidentRead (G := G) B R ξ e he := by
  unfold regionGlobalOfLocal
  exact dite_eq_left he

omit [Fintype V] in
private theorem regionGlobalOfLocal_eq_nonincident (B : Tensor G d) (R : Finset V)
    (ξ : RegionLocalConfig (G := G) B R)
    (h : (e : {e : Edge G // ¬ IsRegionIncidentEdge (G := G) R e}) → Fin (B.bondDim e.1))
    (e : Edge G) (he : ¬ IsRegionIncidentEdge (G := G) R e) :
    regionGlobalOfLocal (G := G) B R ξ h e = h ⟨e, he⟩ := by
  unfold regionGlobalOfLocal
  exact dite_eq_right he

open scoped Classical in
/-- The fiber of the region reading over a consistent region-local configuration has one
global configuration for every choice of free labels on the edges not incident to `R`. -/
theorem regionLocalOfGlobal_fiber_card (B : Tensor G d) (R : Finset V)
    (ξ : RegionLocalConfig (G := G) B R) (hξ : IsRegionConsistent (G := G) B R ξ) :
    (Finset.univ.filter (fun ζ : VirtualConfig B =>
        regionLocalOfGlobal (G := G) B R ζ = ξ)).card =
      regionNonincidentBondProd (G := G) B R := by
  classical
  rw [show regionNonincidentBondProd (G := G) B R =
      (Finset.univ : Finset ((e : {e : Edge G // ¬ IsRegionIncidentEdge (G := G) R e}) →
        Fin (B.bondDim e.1))).card from ?_]
  · refine Finset.card_nbij'
      (fun ζ => fun e => ζ e.1) (regionGlobalOfLocal (G := G) B R ξ) ?_ ?_ ?_ ?_
    · intro ζ _
      exact Finset.mem_univ _
    · -- The rebuilt configuration lies in the fiber: its region reading is `ξ`.
      intro h _
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      funext w ie
      obtain ⟨v, hv⟩ := w
      obtain ⟨e, hie⟩ := ie
      change regionGlobalOfLocal (G := G) B R ξ h e = ξ ⟨v, hv⟩ ⟨e, hie⟩
      by_cases hleft : e.1.1 = v
      · subst v
        have hinc : IsRegionIncidentEdge (G := G) R e := Or.inl hv
        have hg := regionGlobalOfLocal_eq_incident B R ξ h e hinc
        have hr := regionIncidentRead_eq_left B R ξ e hinc hv
        exact Fin.eq_of_val_eq ((congrArg Fin.val hg).trans ((congrArg Fin.val hr).trans rfl))
      · have hright : e.1.2 = v := by
          rcases hie with hL | hR
          · exact absurd hL hleft
          · exact hR
        subst v
        have hinc : IsRegionIncidentEdge (G := G) R e := Or.inr hv
        by_cases h1 : e.1.1 ∈ R
        · have hg := regionGlobalOfLocal_eq_incident B R ξ h e hinc
          have hr := regionIncidentRead_eq_left B R ξ e hinc h1
          exact Fin.eq_of_val_eq ((congrArg Fin.val hg).trans
            ((congrArg Fin.val hr).trans (congrArg Fin.val (hξ e h1 hv))))
        · have hg := regionGlobalOfLocal_eq_incident B R ξ h e hinc
          have hr := regionIncidentRead_eq_right B R ξ e hinc h1
          exact Fin.eq_of_val_eq ((congrArg Fin.val hg).trans ((congrArg Fin.val hr).trans rfl))
    · -- Rebuilding from the free labels of a fiber member recovers it.
      intro ζ hζ
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hζ
      funext e
      by_cases he : IsRegionIncidentEdge (G := G) R e
      · subst hζ
        by_cases h1 : e.1.1 ∈ R
        · have hg := regionGlobalOfLocal_eq_incident B R
            (regionLocalOfGlobal (G := G) B R ζ) (fun e => ζ e.1) e he
          have hr := regionIncidentRead_eq_left B R
            (regionLocalOfGlobal (G := G) B R ζ) e he h1
          exact Fin.eq_of_val_eq ((congrArg Fin.val hg).trans ((congrArg Fin.val hr).trans rfl))
        · have hg := regionGlobalOfLocal_eq_incident B R
            (regionLocalOfGlobal (G := G) B R ζ) (fun e => ζ e.1) e he
          have hr := regionIncidentRead_eq_right B R
            (regionLocalOfGlobal (G := G) B R ζ) e he h1
          exact Fin.eq_of_val_eq ((congrArg Fin.val hg).trans ((congrArg Fin.val hr).trans rfl))
      · exact regionGlobalOfLocal_eq_nonincident B R ξ (fun e => ζ e.1) e he
    · -- The free labels of a rebuilt configuration are the free labels.
      intro h _
      funext e
      change regionGlobalOfLocal (G := G) B R ξ h e.1 = h e
      exact regionGlobalOfLocal_eq_nonincident B R ξ h e.1 e.2
  · rw [Finset.card_univ, Fintype.card_pi]
    simp only [Fintype.card_fin]
    rw [regionNonincidentBondProd,
      ← Finset.prod_subtype (Finset.univ.filter
          (fun e : Edge G => ¬ IsRegionIncidentEdge (G := G) R e))
        (fun e => by simp) (fun e => B.bondDim e)]

open scoped Classical in
/-- **The region-reading fiber collapse.**  Summing a function of the region reading of a
global virtual configuration over all global configurations equals the bond-dimension
product over the edges not incident to `R` times the sum over consistent region-local
configurations.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1571 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem sum_regionLocalOfGlobal_fiber_collapse (B : Tensor G d) (R : Finset V)
    (g : RegionLocalConfig (G := G) B R → ℂ) :
    (∑ ζ : VirtualConfig B, g (regionLocalOfGlobal (G := G) B R ζ)) =
      regionNonincidentBondProd (G := G) B R •
        ∑ ξ ∈ Finset.univ.filter (fun ξ : RegionLocalConfig (G := G) B R =>
            IsRegionConsistent (G := G) B R ξ), g ξ := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun ζ : VirtualConfig B => regionLocalOfGlobal (G := G) B R ζ)
    (t := Finset.univ.filter (fun ξ : RegionLocalConfig (G := G) B R =>
        IsRegionConsistent (G := G) B R ξ))
    (f := fun ζ => g (regionLocalOfGlobal (G := G) B R ζ))
    (s := Finset.univ) ?_]
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun ξ hξ => ?_)
    rw [Finset.mem_filter] at hξ
    rw [Finset.sum_congr rfl (g := fun _ => g ξ)
        (fun ζ hζ => by rw [Finset.mem_filter] at hζ; rw [hζ.2]),
      Finset.sum_const]
    rw [show (Finset.univ.filter (fun ζ : VirtualConfig B =>
        regionLocalOfGlobal (G := G) B R ζ = ξ)).card =
        regionNonincidentBondProd (G := G) B R from
      regionLocalOfGlobal_fiber_card (G := G) B R ξ hξ.2]
  · intro ζ _
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, fun e h1 h2 => rfl⟩

/-! ### The gauged blocked-region weight over global configurations

Assembling the pieces: expand each gauged vertex over its inner indices, regroup the gauge
factors edge by edge, sum the pinned outer configuration edge by edge, collapse the interior
deltas, and reassemble the surviving inner labels into a global configuration of the ungauged
tensor.  Each boundary edge retains its surviving gauge coupling the pinned outer label to
the global configuration; the multiplicity of the edges not incident to `R` matches the one
inside the ungauged blocked-region weight, so the factorization is exact. -/

open scoped Classical in
/-- **Global-configuration form of the gauged blocked-region weight.**  The blocked-region
weight of `applyGauge B X` is the sum, over global virtual configurations of `B`, of the
surviving boundary gauge entries times the region vertex product of `B`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1571 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionBlockedWeight_applyGauge_eq_globalSum (B : Tensor G d)
    (X : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ) (R : Finset V)
    (bdry : RegionBoundaryConfig (G := G) B R)
    (τ : RegionPhysicalConfig (V := V) (d := d) R) :
    regionBlockedWeight (G := G) (applyGauge B X) R bdry τ =
      ∑ ζ : VirtualConfig B,
        (∏ f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f},
          regionBoundaryGauge (G := G) B X R f (bdry f) (ζ f.1)) *
          ∏ w : {w : V // w ∈ R}, B.component w.1 (fun ie => ζ ie.1) (τ w) := by
  have hLHS : regionBlockedWeight (G := G) (applyGauge B X) R bdry τ =
      ∑ ζ ∈ Finset.univ.filter
          (fun ζ : VirtualConfig B => regionBoundaryLabel (G := G) B R ζ = bdry),
        ∏ w : {w : V // w ∈ R}, gaugeVertex B X w.1 (fun ie => ζ ie.1) (τ w) := rfl
  classical
  rw [hLHS]
  calc
    (∑ ζ ∈ Finset.univ.filter
        (fun ζ : VirtualConfig B => regionBoundaryLabel (G := G) B R ζ = bdry),
      ∏ w : {w : V // w ∈ R}, gaugeVertex B X w.1 (fun ie => ζ ie.1) (τ w))
      -- Expand each gauged vertex over region-local inner configurations and regroup the
      -- gauge factors edge by edge.
      = ∑ ζ ∈ Finset.univ.filter
            (fun ζ : VirtualConfig B => regionBoundaryLabel (G := G) B R ζ = bdry),
          ∑ ξ : RegionLocalConfig (G := G) B R,
            (∏ e : Edge G, regionGaugeFactor (G := G) B X R ξ e (ζ e)) *
              ∏ w : {w : V // w ∈ R}, B.component w.1 (ξ w) (τ w) := by
        refine Finset.sum_congr rfl fun ζ _ => ?_
        rw [prod_gaugeVertex_region_eq_sum_local (G := G) B X R ζ τ]
        refine Finset.sum_congr rfl fun ξ _ => ?_
        rw [Finset.prod_mul_distrib, prod_region_edgeGauge_eq_prod_factor (G := G) B X R ζ ξ]
    -- Exchange the sums and pull the tensor part out of the outer sum.
    _ = ∑ ξ : RegionLocalConfig (G := G) B R,
          (∑ ζ ∈ Finset.univ.filter
            (fun ζ : VirtualConfig B => regionBoundaryLabel (G := G) B R ζ = bdry),
            ∏ e : Edge G, regionGaugeFactor (G := G) B X R ξ e (ζ e)) *
            ∏ w : {w : V // w ∈ R}, B.component w.1 (ξ w) (τ w) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun ξ _ => ?_
        rw [Finset.sum_mul]
    -- Carry out the pinned outer sum edge by edge.
    _ = ∑ ξ : RegionLocalConfig (G := G) B R,
          ((∏ f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f},
            regionBoundaryGauge (G := G) B X R f (bdry f)
              (regionLocalBoundary (G := G) B R ξ f)) *
            ∏ e : {e : Edge G // ¬ IsRegionBoundaryEdge (G := G) R e},
              regionEdgeContraction (G := G) B R ξ e.1) *
            ∏ w : {w : V // w ∈ R}, B.component w.1 (ξ w) (τ w) := by
        refine Finset.sum_congr rfl fun ξ _ => ?_
        congr 1
        rw [sum_boundaryFiber_prod_edge (G := G) B R bdry (regionGaugeFactor (G := G) B X R ξ)]
        congr 1
        · exact Finset.prod_congr rfl fun f _ =>
            regionGaugeFactor_boundary (G := G) B X R ξ f (bdry f)
        · exact Finset.prod_congr rfl fun e _ =>
            sum_regionGaugeFactor_nonboundary (G := G) B X R ξ e
    -- Collapse the interior deltas to consistency.
    _ = ∑ ξ : RegionLocalConfig (G := G) B R,
          (if IsRegionConsistent (G := G) B R ξ
            then (regionNonincidentBondProd (G := G) B R : ℂ) else 0) *
            ((∏ f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f},
              regionBoundaryGauge (G := G) B X R f (bdry f)
                (regionLocalBoundary (G := G) B R ξ f)) *
              ∏ w : {w : V // w ∈ R}, B.component w.1 (ξ w) (τ w)) := by
        refine Finset.sum_congr rfl fun ξ _ => ?_
        rw [← prod_regionEdgeContraction (G := G) B R ξ]
        ring
    -- Restrict to consistent configurations with the non-incident multiplicity.
    _ = (regionNonincidentBondProd (G := G) B R : ℂ) *
          ∑ ξ ∈ Finset.univ.filter (fun ξ : RegionLocalConfig (G := G) B R =>
              IsRegionConsistent (G := G) B R ξ),
            (∏ f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f},
              regionBoundaryGauge (G := G) B X R f (bdry f)
                (regionLocalBoundary (G := G) B R ξ f)) *
              ∏ w : {w : V // w ∈ R}, B.component w.1 (ξ w) (τ w) := by
        rw [Finset.mul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun ξ _ => ?_
        by_cases hcons : IsRegionConsistent (G := G) B R ξ
        · rw [ite_eq_left hcons, ite_eq_left hcons]
        · rw [ite_eq_right hcons, ite_eq_right hcons, zero_mul]
    -- Reassemble the consistent configurations into global configurations.
    _ = ∑ ζ : VirtualConfig B,
          (∏ f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f},
            regionBoundaryGauge (G := G) B X R f (bdry f)
              (regionLocalBoundary (G := G) B R (regionLocalOfGlobal (G := G) B R ζ) f)) *
            ∏ w : {w : V // w ∈ R},
              B.component w.1 (regionLocalOfGlobal (G := G) B R ζ w) (τ w) := by
        refine Eq.symm ((sum_regionLocalOfGlobal_fiber_collapse (G := G) B R
          (fun ξ => (∏ f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f},
            regionBoundaryGauge (G := G) B X R f (bdry f)
              (regionLocalBoundary (G := G) B R ξ f)) *
            ∏ w : {w : V // w ∈ R}, B.component w.1 (ξ w) (τ w))).trans ?_)
        exact nsmul_eq_mul _ _
    -- Read the boundary labels off the global configurations.
    _ = ∑ ζ : VirtualConfig B,
          (∏ f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f},
            regionBoundaryGauge (G := G) B X R f (bdry f) (ζ f.1)) *
            ∏ w : {w : V // w ∈ R}, B.component w.1 (fun ie => ζ ie.1) (τ w) := by
        refine Finset.sum_congr rfl fun ζ _ => ?_
        congr 1
        exact Finset.prod_congr rfl fun f _ => by
          rw [regionLocalBoundary_ofGlobal (G := G) B R ζ f]

end PEPS
end TNLean
