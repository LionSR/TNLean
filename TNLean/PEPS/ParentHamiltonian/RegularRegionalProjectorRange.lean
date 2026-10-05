/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegularLiftedRegionRange
import TNLean.Algebra.PiMulSingleInduction

/-!
# The commuting product is the actual extended regional range projector

The common fixed-space calculation identifies the concrete commuting product
with the actual regional range condition on every complementary slice.
No restriction is imposed on exterior half-edge coordinates.
Source: SCP10, arXiv:1001.3807, Theorem 6.12, lines 2131–2153.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

omit [Fintype G] [DecidableEq G] in
private theorem extendGauge_mulSingle (R : Finset V) (v : {v : V // v ∈ R}) (g : G) :
    regularRegionExtendVertexGauge R (Pi.mulSingle v g) =
      fun w => if w.1 = v.1 then g else 1 := by
  funext w
  by_cases hw : w.1 ∈ R
  · simp [regularRegionExtendVertexGauge, hw, Pi.mulSingle_apply, Subtype.ext_iff, eq_comm]
  · have hv : w.1 ≠ v.1 := fun h => hw (h ▸ v.2)
    simp [regularRegionExtendVertexGauge, hw, hv]

/-- Individual vertex fixedness is equivalent to simultaneous invariance on
the whole region, without commutativity of the group. -/
theorem regularRegionalVertexAverages_fixed_iff (R : Finset V)
    (x : RegionHalfEdgeConfig (Γ := Γ) G Finset.univ → ℂ) :
    (∀ v ∈ R, regularGlobalVertexAverage (Γ := Γ) (G := G) v *ᵥ x = x) ↔
      ∀ k α, x (regularRegionGaugePhysicalLabels Finset.univ
        (regularRegionExtendVertexGauge R k) α) = x α := by
  constructor
  · intro h k
    apply Pi.mulSingle_induction_noncomm
      (fun k : {v : V // v ∈ R} → G => ∀ α,
        x (regularRegionGaugePhysicalLabels Finset.univ
          (regularRegionExtendVertexGauge R k) α) = x α) k
    · intro α
      have heq : regularRegionGaugePhysicalLabels Finset.univ
          (regularRegionExtendVertexGauge R (1 : {v : V // v ∈ R} → G)) α = α := by
        funext v e
        simp [regularRegionGaugePhysicalLabels_apply, regularRegionExtendVertexGauge]
      rw [heq]
    · intro f g hf hg α
      have heq : regularRegionGaugePhysicalLabels Finset.univ
          (regularRegionExtendVertexGauge R (f * g)) α =
        regularRegionGaugePhysicalLabels Finset.univ (regularRegionExtendVertexGauge R g)
          (regularRegionGaugePhysicalLabels Finset.univ
            (regularRegionExtendVertexGauge R f) α) := by
        funext v e
        simp only [regularRegionGaugePhysicalLabels_apply, regularRegionExtendVertexGauge]
        split_ifs <;> simp only [Pi.mul_apply, mul_inv_rev, mul_assoc, inv_one, one_mul]
      rw [heq, hg, hf]
    · intro v g α
      rw [extendGauge_mulSingle]
      exact (regularGlobalVertexAverage_mulVec_eq_self_iff v.1 x).mp (h v.1 v.2) g α
  · intro h v hv
    apply (regularGlobalVertexAverage_mulVec_eq_self_iff v x).mpr
    intro g α
    have hh := h (Pi.mulSingle (⟨v, hv⟩ : {v : V // v ∈ R}) g) α
    rwa [extendGauge_mulSingle] at hh

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G] in
private theorem internalMultiplier_mulSingle (R : Finset V) (e : Edge Γ) (g : G) :
    regularRegionInternalMultiplier R (Pi.mulSingle e g) =
      if e.1.1 ∈ R ∧ e.1.2 ∈ R then Pi.mulSingle e g else 1 := by
  funext f
  by_cases hfe : f = e
  · subst f
    split_ifs <;> simp [regularRegionInternalMultiplier, *]
  · split_ifs <;> simp [regularRegionInternalMultiplier, *]

/-- Individual internal-edge fixedness is equivalent to simultaneous shared
right invariance on all internal edges. -/
theorem regularRegionalEdgeAverages_fixed_iff (R : Finset V)
    (x : RegionHalfEdgeConfig (Γ := Γ) G Finset.univ → ℂ) :
    (∀ e : Edge Γ, e.1.1 ∈ R → e.1.2 ∈ R →
      regularRegionEdgeAverage (G := G) Finset.univ e *ᵥ x = x) ↔
      ∀ r α, x (regularRegionHalfEdgeRightMul Finset.univ
        (regularRegionInternalMultiplier R r) α) = x α := by
  constructor
  · intro h r
    apply Pi.mulSingle_induction_noncomm
      (fun r : Edge Γ → G => ∀ α, x (regularRegionHalfEdgeRightMul Finset.univ
        (regularRegionInternalMultiplier R r) α) = x α) r
    · intro α
      have heq : regularRegionHalfEdgeRightMul Finset.univ
          (regularRegionInternalMultiplier R (1 : Edge Γ → G)) α = α := by
        funext v e
        simp [regularRegionHalfEdgeRightMul, regularRegionInternalMultiplier]
      rw [heq]
    · intro f g hf hg α
      have heq : regularRegionHalfEdgeRightMul Finset.univ
          (regularRegionInternalMultiplier R (f * g)) α =
        regularRegionHalfEdgeRightMul Finset.univ (regularRegionInternalMultiplier R g)
          (regularRegionHalfEdgeRightMul Finset.univ (regularRegionInternalMultiplier R f) α) := by
        funext v e
        simp only [regularRegionHalfEdgeRightMul, regularRegionInternalMultiplier]
        split_ifs <;> simp only [Pi.mul_apply, mul_assoc, mul_one]
      rw [heq, hg, hf]
    · intro e g α
      rw [internalMultiplier_mulSingle]
      split_ifs with he
      · have hh := (regularRegionEdgeAverage_mulVec_eq_self_iff Finset.univ e x).mp
          (h e he.1 he.2) g α
        convert hh using 2
        funext v f
        simp [regularRegionHalfEdgeRightMul, Pi.mulSingle_apply]
      · have heq : regularRegionHalfEdgeRightMul Finset.univ (1 : Edge Γ → G) α = α := by
          funext v f
          simp [regularRegionHalfEdgeRightMul]
        rw [heq]
  · intro h e ht hh
    apply (regularRegionEdgeAverage_mulVec_eq_self_iff Finset.univ e x).mpr
    intro g α
    have hi := h (Pi.mulSingle e g) α
    rw [internalMultiplier_mulSingle, ite_eq_left ⟨ht, hh⟩] at hi
    convert hi using 2
    funext v f
    simp [regularRegionHalfEdgeRightMul, Pi.mulSingle_apply]

/-- The commuting virtual regional projector fixes exactly the actual
regional range condition on every complementary slice. -/
theorem regularGlobalRegionConstraint_mulVec_eq_self_iff_mem_range (R : Finset V)
    (x : RegionHalfEdgeConfig (Γ := Γ) G Finset.univ → ℂ) :
    regularGlobalRegionConstraint (Γ := Γ) (G := G) R *ᵥ x = x ↔
      x ∈ regularGlobalRegionRange R := by
  rw [regularGlobalRegionConstraint_mulVec_eq_self_iff,
    regularRegionalVertexAverages_fixed_iff, regularRegionalEdgeAverages_fixed_iff,
    regularGlobalRegionFlatProjector_mulVec_eq_self_iff,
    mem_regularGlobalRegionRange_iff_invariant_flat]

/-- The range of the explicit commuting projector is the actual extended
regional range, including arbitrary exterior half-edge coordinates. -/
theorem range_regularGlobalRegionConstraint (R : Finset V) :
    (Matrix.mulVecLin (regularGlobalRegionConstraint (Γ := Γ) (G := G) R)).range =
      regularGlobalRegionRange R := by
  ext x
  rw [← regularGlobalRegionConstraint_mulVec_eq_self_iff_mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    change regularGlobalRegionConstraint R *ᵥ (regularGlobalRegionConstraint R *ᵥ y) = _
    rw [Matrix.mulVec_mulVec,
      (regularGlobalRegionConstraint_isStarProjection R).isIdempotentElem.eq]
    rfl
  · intro h
    exact ⟨x, h⟩

end TNLean.PEPS
