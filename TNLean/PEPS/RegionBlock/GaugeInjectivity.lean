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
      show edgeGaugeAt B X w.1 ie (ζ ie.1) (ξ w ie) =
        if h : w.1 ∈ R then edgeGaugeAt B X w.1 ie (ζ ie.1) (ξ ⟨w.1, h⟩ ie) else 1
      rw [dif_pos w.2]]
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
    rw [regionBoundaryLabel_apply, dif_pos f.2]⟩
  left_inv ζ := by
    apply Subtype.ext
    funext e
    show (if hb : IsRegionBoundaryEdge (G := G) R e then bdry ⟨e, hb⟩ else ζ.1 e) = ζ.1 e
    by_cases hb : IsRegionBoundaryEdge (G := G) R e
    · rw [dif_pos hb]
      exact (congrFun ζ.2 ⟨e, hb⟩).symm
    · rw [dif_neg hb]
  right_inv h := by
    funext e
    show (if hb : IsRegionBoundaryEdge (G := G) R e.1 then bdry ⟨e.1, hb⟩ else h ⟨e.1, hb⟩) =
      h e
    rw [dif_neg e.2]

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
      · rw [dif_pos hb]
        exact congrArg (g e) (congrFun ζ.2 ⟨e, hb⟩)
      · rw [dif_neg hb]
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
    · exact Finset.prod_congr rfl fun f _ => by rw [dif_pos f.2]
    · exact Finset.prod_congr rfl fun e _ => by rw [dif_neg e.2])]
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
  rw [regionGaugeFactor, regionBoundaryGauge, regionLocalBoundary]
  by_cases h1 : f.1.1.1 ∈ R
  · have h2 : f.1.1.2 ∉ R := by
      rcases f.2 with ⟨_, hr⟩ | ⟨hl, _⟩
      · exact hr
      · exact absurd h1 hl
    rw [dif_pos h1, dif_neg h2, mul_one, if_pos h1, dif_pos h1, edgeGaugeAt_left]
  · have h2 : f.1.1.2 ∈ R := boundary_right_mem (G := G) R f.2 h1
    rw [dif_neg h1, dif_pos h2, one_mul, if_neg h1, dif_neg h1, edgeGaugeAt_right]

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
    rw [regionEdgeContraction, if_pos hinc]
    rw [show (∑ z : Fin (B.bondDim e.1), regionGaugeFactor (G := G) B X R ξ e.1 z) =
        ∑ z : Fin (B.bondDim e.1),
          (X e.1 : Matrix (Fin (B.bondDim e.1)) (Fin (B.bondDim e.1)) ℂ) z
              (ξ ⟨e.1.1.1, h1⟩ (edgeLeftIncident (G := G) e.1)) *
            ((X e.1 : Matrix (Fin (B.bondDim e.1)) (Fin (B.bondDim e.1)) ℂ)⁻¹)
              (ξ ⟨e.1.1.2, h2⟩ (edgeRightIncident (G := G) e.1)) z from
      Finset.sum_congr rfl fun z _ => by
        rw [regionGaugeFactor, dif_pos h1, dif_pos h2, edgeGaugeAt_left, edgeGaugeAt_right,
          Matrix.GeneralLinearGroup.coe_inv, Matrix.transpose_apply]]
    rw [gauge_sum_left_right_matrix_inv (X e.1)]
    refine if_congr ?_ rfl rfl
    constructor
    · intro hab _ _
      exact hab
    · intro h
      exact h h1 h2
  · have h2 : e.1.1.2 ∉ R := nonboundary_right_not_mem (G := G) R e.2 h1
    have hninc : ¬ IsRegionIncidentEdge (G := G) R e.1 :=
      fun hinc => hinc.elim (fun h => absurd h h1) (fun h => absurd h h2)
    rw [regionEdgeContraction, if_neg hninc]
    rw [Finset.sum_congr rfl (fun z _ =>
      show regionGaugeFactor (G := G) B X R ξ e.1 z = 1 by
        rw [regionGaugeFactor, dif_neg h1, dif_neg h2, mul_one])]
    simp

end PEPS
end TNLean
