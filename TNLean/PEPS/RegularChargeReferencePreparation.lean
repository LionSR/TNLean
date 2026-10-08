/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularChargePair
import TNLean.Algebra.UnitaryVectorSwap

import TNLean.Algebra.PermutationMatrixCommutation

/-!
# Symmetric preparation on the two internal reference labels

The normalized uniform vector and normalized correlated charge-pair coefficient
are invariant under simultaneous left translation. Their exchange is therefore
unitary and commutes with that translation. This is the reference-coordinate
operation needed by the actual six-site block, not yet its physical realization.
Source: SCP10, arXiv:1001.3807, charge-pair creation, lines 2505–2558.
-/
noncomputable section
open scoped BigOperators Matrix Kronecker

namespace TNLean.PEPS
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

private theorem pair_translation_invariant (χ : G → ℂ) (p x : G) :
    (leftRegularMatrix G x ⊗ₖ leftRegularMatrix G x) *ᵥ
        normalizedRegularChargePairCoefficient χ p =
      normalizedRegularChargePairCoefficient χ p := by
  ext ⟨r,s⟩
  rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  have hr (a : G) : r = x*a ↔ a = x⁻¹*r := by
    constructor
    · intro h; rw [h]; group
    · rintro rfl; group
  have hs (a : G) : s = x*a ↔ a = x⁻¹*s := by
    constructor
    · intro h; rw [h]; group
    · rintro rfl; group
  simp only [Matrix.kroneckerMap_apply, leftRegularMatrix_apply, hr, hs,
    ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  simp only [normalizedRegularChargePairCoefficient, Pi.smul_apply, smul_eq_mul,
    regularChargePairCoefficient_left_invariant]

/-- A translation-invariant unitary prepares the actual normalized correlated pair
coefficient from the uniform internal reference vector. Source: SCP10,
charge-pair creation, lines 2505–2558; auxiliary reference-coordinate statement. -/
theorem exists_unitary_regularChargeReferencePreparation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (σ : Representation ℂ G E) [σ.IsIrreducible]
    (hσ : ∀ g, LinearMap.adjoint (σ g) = σ g⁻¹) (p : G) :
    ∃ Q : Matrix (G × G) (G × G) ℂ,
      Q ∈ Matrix.unitaryGroup _ ℂ ∧
      Q *ᵥ normalizedRegularChargePairCoefficient (fun _ : G => 1) 1 =
        normalizedRegularChargePairCoefficient σ.character p ∧
      ∀ x, Commute Q (leftRegularMatrix G x ⊗ₖ leftRegularMatrix G x) := by
  let τ := Representation.trivial ℂ G ℂ
  let : τ.IsIrreducible :=
    Representation.isIrreducible_of_finrank_eq_one τ (by simp)
  have ht : τ.character = fun _ : G => 1 := by
    ext g
    simp [τ, Representation.character, Representation.trivial, LinearMap.trace_one]
  have hτ (g : G) : LinearMap.adjoint (τ g) = τ g⁻¹ := by
    simp [τ, Representation.trivial]
  have hx : star (normalizedRegularChargePairCoefficient (fun _ : G => 1) 1) ⬝ᵥ
      normalizedRegularChargePairCoefficient (fun _ : G => 1) 1 = 1 := by
    simpa only [ht, dotProduct, Pi.star_apply] using
      normalizedRegularChargePairCoefficient_normSq τ hτ 1
  have hy : star (normalizedRegularChargePairCoefficient σ.character p) ⬝ᵥ
      normalizedRegularChargePairCoefficient σ.character p = 1 :=
    normalizedRegularChargePairCoefficient_normSq σ hσ p
  by_cases hc : τ.character = σ.character
  · refine ⟨1, one_mem _, ?_, fun x => Commute.one_left _⟩
    rw [Matrix.one_mulVec]
    have hs : σ.character = fun _ : G => 1 := hc.symm.trans ht
    funext q
    simp only [hs, normalizedRegularChargePairCoefficient, Pi.smul_apply,
      regularChargePairCoefficient]
  · have hxy : star (normalizedRegularChargePairCoefficient (fun _ : G => 1) 1) ⬝ᵥ
        normalizedRegularChargePairCoefficient σ.character p = 0 := by
      simpa only [dotProduct, Pi.star_apply, normalizedRegularChargePairCoefficient,
        regularChargePairCoefficient, Pi.smul_apply, smul_eq_mul, mul_one] using
          normalizedRegularChargePairCoefficient_orthogonal_uniform σ hc p
    refine ⟨Matrix.unitaryVectorSwap _ _,
      Matrix.unitaryVectorSwap_mem_unitaryGroup _ _ hx hy hxy,
      Matrix.unitaryVectorSwap_mulVec_left _ _ hx hxy, ?_⟩
    intro x
    have hU : leftRegularMatrix G x ∈ Matrix.unitaryGroup G ℂ := by
      simpa only [leftRegularMatrix, MonoidHom.comp_apply, Matrix.permMatrixHom_apply] using
        ((MulAction.toPermHom G G x)⁻¹).permMatrix_mem_unitaryGroup
    exact Matrix.unitaryVectorSwap_commute _ _ _
      (Matrix.kronecker_mem_unitary hU hU)
      (pair_translation_invariant (fun _ : G => 1) 1 x)
      (pair_translation_invariant σ.character p x)

/-- The return projector commutes with the common translation of the two actual
charge-pair references. Source: SCP10, the accessible-register measurement,
lines 2582–2615. -/
theorem regularChargePairReturnProjection_commute (χ : G → ℂ) (p x : G) :
    Commute (regularChargePairReturnProjection χ p)
      (leftRegularMatrix G x ⊗ₖ leftRegularMatrix G x) := by
  let v := normalizedRegularChargePairCoefficient χ p
  let U := leftRegularMatrix G x ⊗ₖ leftRegularMatrix G x
  have hU : leftRegularMatrix G x ∈ Matrix.unitaryGroup G ℂ := by
    simpa only [leftRegularMatrix, MonoidHom.comp_apply, Matrix.permMatrixHom_apply] using
      ((MulAction.toPermHom G G x)⁻¹).permMatrix_mem_unitaryGroup
  have hc := Matrix.unitaryVectorSwap_commute v 0 U
    (Matrix.kronecker_mem_unitary hU hU)
    (pair_translation_invariant χ p x) (by simp)
  have hform : Matrix.unitaryVectorSwap v 0 = 1 - regularChargePairReturnProjection χ p := by
    simp only [Matrix.unitaryVectorSwap, sub_zero, v, regularChargePairReturnProjection]
  rw [hform] at hc
  simpa using (Commute.one_left U).sub_left hc

end TNLean.PEPS
