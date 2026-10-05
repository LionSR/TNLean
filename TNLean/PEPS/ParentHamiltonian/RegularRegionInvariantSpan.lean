/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegularRegionOrbitCoordinates

/-!
# Orbit expansion on an open regular region

Left vertex invariance and shared internal right invariance give an explicit
expansion in the actual inserted regional columns. Boundary half-edges remain
independent throughout. This is the regional orbit argument for SCP10,
arXiv:1001.3807, Theorem 6.12, lines 2131–2153.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- Averaging the independent vertex gauges fixes every left-invariant
function of the actual regional half-edge labels. -/
theorem sum_regularRegionProjectorProduct_eq (R : Finset V)
    (f : RegionHalfEdgeConfig (Γ := Γ) G R → ℂ)
    (hleft : ∀ k α, f (regularRegionGaugePhysicalLabels R k α) = f α)
    (α : RegionHalfEdgeConfig (Γ := Γ) G R) :
    (∑ β, f β * ∏ v : {v : V // v ∈ R},
      regularLegProjector (IncidentEdge Γ v.1) (α v) (β v)) = f α := by
  classical
  have hkernel (β : RegionHalfEdgeConfig (Γ := Γ) G R) :
      (∏ v : {v : V // v ∈ R}, regularLegProjector (IncidentEdge Γ v.1) (α v) (β v)) =
      (Fintype.card G : ℂ)⁻¹ ^ R.card *
        ∑ k : {v : V // v ∈ R} → G, if α = (fun v e => k v * β v e) then 1 else 0 := by
    have h := congrFun (congrFun
      (regionPhysicalProductMatrix_regularLegProjector_eq_sum_vertexTranslation
        (Γ := Γ) (G := G) R) α) β
    simpa only [regionPhysicalProductMatrix, Matrix.smul_apply, Matrix.sum_apply,
      smul_eq_mul, regularRegionVertexTranslationMatrix_apply] using h
  simp_rw [hkernel, ← mul_assoc, mul_comm (f _) ((Fintype.card G : ℂ)⁻¹ ^ _), mul_assoc]
  rw [← Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hinner (k : {v : V // v ∈ R} → G) :
      (∑ β : RegionHalfEdgeConfig (Γ := Γ) G R,
        f β * if α = (fun v e => k v * β v e) then 1 else 0) = f α := by
    have heq (β : RegionHalfEdgeConfig (Γ := Γ) G R) :
        α = (fun v e => k v * β v e) ↔ β = regularRegionGaugePhysicalLabels R k α := by
      constructor
      · intro h
        funext v e
        have hv := congrFun (congrFun h v) e
        simp only [regularRegionGaugePhysicalLabels_apply, hv, inv_mul_cancel_left]
      · rintro rfl
        funext v e
        simp only [regularRegionGaugePhysicalLabels_apply, mul_inv_cancel_left]
    simp_rw [heq, mul_ite, mul_one, mul_zero]
    rw [Fintype.sum_ite_eq']
    exact hleft _ _
  simp_rw [← Finset.mul_sum, hinner]
  simp [← Nat.cast_pow]

/-- Every function invariant under vertex gauges and shared internal right
translations is an explicit linear combination of the actual inserted open
region columns. No support or flatness assumption enters this expansion. -/
theorem eq_sum_regularProjectorTwistedRegionMatrix_of_invariant (R : Finset V)
    (f : RegionHalfEdgeConfig (Γ := Γ) G R → ℂ)
    (hleft : ∀ k α, f (regularRegionGaugePhysicalLabels R k α) = f α)
    (hright : ∀ r : Edge Γ → G, (∀ e, IsRegionBoundaryEdge R e → r e = 1) →
      ∀ α, f (regularRegionHalfEdgeRightMul R r α) = f α) :
    f = ∑ u : RegularRegionInternalEdge (Γ := Γ) R → G,
      ∑ θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G,
        f (regularRegionHalfEdgesOfBonds R u (regularRegionCanonicalReferences R θ)) •
          (fun α => regularProjectorTwistedRegionMatrix R
            (regularRegionInternalExtension R u) α θ) := by
  classical
  funext α
  rw [← sum_regularRegionProjectorProduct_eq R f hleft α]
  rw [← Equiv.sum_comp (regularRegionHalfEdgeConfigEquiv (Γ := Γ) (G := G) R),
    Fintype.sum_prod_type]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro u _
  change (∑ η, f (regularRegionHalfEdgesOfBonds R u η) *
    ∏ v : {v : V // v ∈ R}, regularLegProjector (IncidentEdge Γ v.1) (α v)
      (regularRegionHalfEdgesOfBonds R u η v)) = _
  simp only [regularProjectorTwistedRegionMatrix, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro η _
  rw [regularRegionHalfEdgesOfBonds_apply_of_rightInvariant R f hright u η]
  simp only [mul_ite, mul_zero]
  rw [Fintype.sum_ite_eq]
  rfl

/-- Gauging a canonical inserted region transports only its boundary columns.
The equality follows from the original shared-bond summation. -/
theorem regularProjectorTwistedRegionMatrix_regionGauge (R : Finset V)
    (k : {v : V // v ∈ R} → G) (u : Edge Γ → G)
    (α : RegionHalfEdgeConfig (Γ := Γ) G R)
    (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G) :
    regularProjectorTwistedRegionMatrix R u α θ =
      regularProjectorTwistedRegionMatrix R (regularRegionGaugeEdgeOperators R k u)
        α (regularRegionBoundaryTransport R k u θ) := by
  classical
  unfold regularProjectorTwistedRegionMatrix
  conv_rhs => rw [← Equiv.sum_comp (regularRegionGaugeIncidentLabels R k u)]
  apply Finset.sum_congr rfl
  intro η _
  simp only [regularRegionGaugeIncidentLabels_boundary,
    (regularRegionBoundaryTransport R k u).injective.eq_iff]
  split_ifs
  · apply Finset.prod_congr rfl
    intro v _
    rw [regularRegionGaugeIncidentLabels_twisted]
    exact (isGIsometric_regularLegProjector.toIsGInjective.regularSiteMap_translation
      (k v)⁻¹ _ (α v)).symm
  · rfl

/-- Removing the internal quotients makes the actual inserted column an
untwisted column at a transported boundary label. -/
theorem regularProjectorTwistedRegionMatrix_eq_open_of_flat (R : Finset V)
    (k : {v : V // v ∈ R} → G) (u : Edge Γ → G)
    (hflat : ∀ e, regularRegionGaugeResidual R k u e = 1)
    (α : RegionHalfEdgeConfig (Γ := Γ) G R)
    (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G) :
    regularProjectorTwistedRegionMatrix R u α θ =
      regularProjectorOpenRegionMatrix R α (regularRegionBoundaryTransport R k u θ) := by
  rw [regularProjectorTwistedRegionMatrix_regionGauge R k u α θ]
  have hop : regularRegionGaugeEdgeOperators R k u = fun _ => 1 := by
    funext e
    unfold regularRegionGaugeEdgeOperators
    split_ifs
    · exact hflat _
    · rfl
  rw [hop, regularProjectorTwistedRegionMatrix_one]

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G] in
/-- Flatness of a canonical representative supplies a gauge removing its
internal quotients. -/
theorem exists_regularRegionGaugeResidual_eq_one_of_flat (R : Finset V)
    (u : RegularRegionInternalEdge (Γ := Γ) R → G)
    (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G)
    (hflat : IsRegularRegionHalfEdgeFlat R
      (regularRegionHalfEdgesOfBonds R u (regularRegionCanonicalReferences R θ))) :
    ∃ k : {v : V // v ∈ R} → G,
      ∀ e, regularRegionGaugeResidual R k (regularRegionInternalExtension R u) e = 1 := by
  obtain ⟨k, hk⟩ := hflat
  refine ⟨k, fun e => ?_⟩
  have h := hk e
  rw [regularRegionHalfEdgesOfBonds_tail, regularRegionHalfEdgesOfBonds_head] at h
  simp only [regularRegionCanonicalReferences, dite_eq_left e.2, mul_one] at h
  simp only [regularRegionGaugeResidual, regularRegionInternalExtension, dite_eq_left e.2]
  rw [← h, inv_mul_cancel]

/-- The actual untwisted open-region range contains every left-vertex- and
internal-right-invariant function supported on flat configurations.
No spanning tree or connectedness assumption is needed. -/
theorem mem_regularProjectorOpenRegionRange_of_invariant_flat (R : Finset V)
    (f : RegionHalfEdgeConfig (Γ := Γ) G R → ℂ)
    (hleft : ∀ k α, f (regularRegionGaugePhysicalLabels R k α) = f α)
    (hright : ∀ r : Edge Γ → G, (∀ e, IsRegionBoundaryEdge R e → r e = 1) →
      ∀ α, f (regularRegionHalfEdgeRightMul R r α) = f α)
    (hsupport : ∀ α, ¬ IsRegularRegionHalfEdgeFlat R α → f α = 0) :
    f ∈ (Matrix.mulVecLin (regularProjectorOpenRegionMatrix (G := G) R)).range := by
  classical
  rw [eq_sum_regularProjectorTwistedRegionMatrix_of_invariant R f hleft hright]
  apply Submodule.sum_mem
  intro u _
  apply Submodule.sum_mem
  intro θ _
  by_cases hc : f (regularRegionHalfEdgesOfBonds R u (regularRegionCanonicalReferences R θ)) = 0
  · rw [hc, zero_smul]
    exact Submodule.zero_mem _
  apply Submodule.smul_mem
  have hflat : IsRegularRegionHalfEdgeFlat R
      (regularRegionHalfEdgesOfBonds R u (regularRegionCanonicalReferences R θ)) := by
    by_contra h
    exact hc (hsupport _ h)
  obtain ⟨k, hk⟩ := exists_regularRegionGaugeResidual_eq_one_of_flat R u θ hflat
  refine ⟨Pi.single (regularRegionBoundaryTransport R k (regularRegionInternalExtension R u) θ) 1,
    ?_⟩
  change regularProjectorOpenRegionMatrix R *ᵥ Pi.single _ 1 = _
  rw [Matrix.mulVec_single_one]
  funext α
  exact (regularProjectorTwistedRegionMatrix_eq_open_of_flat R k _ hk α θ).symm

/-- Every actual untwisted column vanishes off the flat half-edge locus. -/
theorem regularProjectorOpenRegionMatrix_eq_zero_of_not_flat (R : Finset V)
    (α : RegionHalfEdgeConfig (Γ := Γ) G R)
    (hα : ¬ IsRegularRegionHalfEdgeFlat R α)
    (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G) :
    regularProjectorOpenRegionMatrix R α θ = 0 := by
  classical
  rw [regularProjectorOpenRegionMatrix_apply]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro η _
  apply Finset.sum_eq_zero
  intro q _
  split_ifs with h
  · exfalso
    apply hα
    refine ⟨q, fun e => ?_⟩
    rw [h.2 ⟨e.1.1.1, e.2.1⟩, h.2 ⟨e.1.1.2, e.2.2⟩]
    simp only [Pi.smul_apply, smul_eq_mul, inv_mul_cancel_left]
  · rfl

/-- The actual untwisted columns are invariant under independent left vertex gauges. -/
theorem regularProjectorOpenRegionMatrix_gauge (R : Finset V)
    (k : {v : V // v ∈ R} → G) (α : RegionHalfEdgeConfig (Γ := Γ) G R)
    (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G) :
    regularProjectorOpenRegionMatrix R (regularRegionGaugePhysicalLabels R k α) θ =
      regularProjectorOpenRegionMatrix R α θ := by
  classical
  unfold regularProjectorOpenRegionMatrix
  apply Finset.sum_congr rfl
  intro η _
  split_ifs
  · apply Finset.prod_congr rfl
    intro v _
    have h := (regularLegRepresentation (G := G) (IncidentEdge Γ v.1)).averageMap_invariant
      (Pi.single (fun f => η ⟨f.1, isRegionIncidentEdge_of_regionVertex R v f⟩) 1) (k v)
    have hα := congrFun h (α v)
    have hlabels : regularRegionGaugePhysicalLabels R k α v = (k v)⁻¹ • α v := by
      funext e
      rfl
    rw [hlabels]
    simpa only [regularLegProjector, LinearMap.toMatrix'_apply,
      regularLegRepresentation_apply] using hα
  · rfl

/-- The actual open-region range is exactly the space of left-vertex- and
internal-right-invariant functions supported on flat half-edge configurations.
This equality is valid on disconnected regions as well. -/
theorem mem_regularProjectorOpenRegionRange_iff (R : Finset V)
    (f : RegionHalfEdgeConfig (Γ := Γ) G R → ℂ) :
    f ∈ (Matrix.mulVecLin (regularProjectorOpenRegionMatrix (G := G) R)).range ↔
      (∀ k α, f (regularRegionGaugePhysicalLabels R k α) = f α) ∧
      (∀ r : Edge Γ → G, (∀ e, IsRegionBoundaryEdge R e → r e = 1) →
        ∀ α, f (regularRegionHalfEdgeRightMul R r α) = f α) ∧
      (∀ α, ¬ IsRegularRegionHalfEdgeFlat R α → f α = 0) := by
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · intro k α
      change (∑ θ, regularProjectorOpenRegionMatrix R
        (regularRegionGaugePhysicalLabels R k α) θ * x θ) = _
      simp_rw [regularProjectorOpenRegionMatrix_gauge]
      rfl
    · intro r hr α
      change (∑ θ, regularProjectorOpenRegionMatrix R
        (regularRegionHalfEdgeRightMul R r α) θ * x θ) = _
      simp_rw [regularProjectorOpenRegionMatrix_halfEdgeRightMul R r hr]
      rfl
    · intro α hα
      change (∑ θ, regularProjectorOpenRegionMatrix R α θ * x θ) = 0
      simp only [regularProjectorOpenRegionMatrix_eq_zero_of_not_flat R α hα,
        zero_mul, Finset.sum_const_zero]
  · rintro ⟨hl, hr, hs⟩
    exact mem_regularProjectorOpenRegionRange_of_invariant_flat R f hl hr hs

end TNLean.PEPS
