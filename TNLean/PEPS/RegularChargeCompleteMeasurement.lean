/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularChargeLabels

/-!
# Completeness of the regular charge detectors

The actual irreducible characters of the regular representation resolve every
matrix unit in the two-register group basis. Their charge projections are
therefore mutually orthogonal and sum to the identity.
Source: SCP10, arXiv:1001.3807, charge detection, lines 2464–2486.
These are accessible-register identities, before transport to original spins.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The finite charge labels of the actual regular Hilbert-space representation.
Source: SCP10, charge detection, lines 2464–2486. -/
def regularChargeLabels : Finset (G → ℂ) :=
  Representation.irreducibleCharacterFinset
    (Representation.euclideanMatrixRepresentation (leftRegularMatrix G))

private theorem regular_character_sum (k : G) :
    ∑ χ ∈ regularChargeLabels (G := G), χ 1 * χ k =
      if k = 1 then (Fintype.card G : ℂ) else 0 := by
  have hs := (Representation.isSemiRegular_leftRegular (G := G)).of_equiv
    (leftRegularEuclideanMatrixEquiv (G := G))
  simpa only [regularChargeLabels, Nat.card_eq_fintype_card] using
    Representation.sum_irreducibleCharacters_mul_of_isSemiRegular _ hs k

/-- The character-weighted actual charge matrices resolve every matrix unit.
Source: SCP10, charge detection, lines 2474–2486; finite character completeness. -/
theorem sum_regularChargeMatrix_eq_single (r s : G) :
    ∑ χ ∈ regularChargeLabels (G := G), χ 1 • regularChargeMatrix χ r⁻¹ 1 (s*r⁻¹) =
      (Fintype.card G : ℂ) • Matrix.single r s 1 := by
  classical
  ext a b
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, regularChargeMatrix,
    inv_one, one_mul]
  by_cases ht : s*r⁻¹*a = b
  · simp only [ht, ↓reduceIte]
    rw [regular_character_sum]
    have ha : r⁻¹*a = 1 ↔ a = r := by simpa only [eq_comm] using (inv_mul_eq_one (a := r) (b := a))
    by_cases har : a = r
    · subst a
      have hbs : b = s := by simpa using ht.symm
      subst b
      simp
    · simp [ha, har, Ne.symm har]
  · simp [ht, Matrix.single_apply]
    by_cases har : a = r
    · subst a
      have hsb : s ≠ b := by simpa using ht
      simp [hsb, eq_comm]
    · simp [Ne.symm har]

/-- The detector selects its own actual regular charge label and annihilates all others.
Source: SCP10, charge detection, lines 2474–2486. -/
theorem regularChargeDetectorMatrix_label_vector (χ ψ : G → ℂ)
    (hχ : χ ∈ regularChargeLabels (G := G))
    (hψ : ψ ∈ regularChargeLabels (G := G)) (p x y : G) :
    regularChargeDetectorMatrix χ *ᵥ
        (fun rs : G × G => regularChargeMatrix ψ p x y rs.1 rs.2) =
      if χ = ψ then (fun rs : G × G => regularChargeMatrix ψ p x y rs.1 rs.2) else 0 := by
  classical
  by_cases h : χ = ψ
  · subst ψ
    simpa using regularChargeDetectorMatrix_chargeVector χ p x y
  · simpa only [h, ↓reduceIte] using
      regularChargeDetectorMatrix_other_of_mem_irreducibleCharacterFinset
        χ ψ hχ hψ h p x y

private theorem matrix_ext_on_chargeVectors (M N : Matrix (G × G) (G × G) ℂ)
    (h : ∀ χ ∈ regularChargeLabels (G := G), ∀ p x y,
      M *ᵥ (fun rs : G × G => regularChargeMatrix χ p x y rs.1 rs.2) =
        N *ᵥ (fun rs : G × G => regularChargeMatrix χ p x y rs.1 rs.2)) : M = N := by
  classical
  have hG : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  ext a ⟨r,s⟩
  have hv : ∑ χ ∈ regularChargeLabels (G := G),
      χ 1 • (fun rs : G × G => regularChargeMatrix χ r⁻¹ 1 (s*r⁻¹) rs.1 rs.2) =
      (Fintype.card G : ℂ) • Pi.single (r,s) 1 := by
    funext rs
    have hh := congrArg (fun X : Matrix G G ℂ => X rs.1 rs.2)
      (sum_regularChargeMatrix_eq_single r s)
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at hh
    rcases rs with ⟨a,b⟩
    simpa [Matrix.single_apply, Pi.single_apply, Prod.mk.injEq, eq_comm] using hh
  have hx : M *ᵥ ((Fintype.card G : ℂ) • Pi.single (r,s) 1) =
      N *ᵥ ((Fintype.card G : ℂ) • Pi.single (r,s) 1) := by
    rw [← hv, Matrix.mulVec_sum, Matrix.mulVec_sum]
    apply Finset.sum_congr rfl
    intro χ hχ
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, h χ hχ]
  have ha := congrFun hx a
  simp only [Matrix.mulVec_smul, Matrix.mulVec_single_one, Pi.smul_apply,
    smul_eq_mul] at ha
  exact mul_left_cancel₀ hG ha

/-- The actual regular charge detectors form a complete orthogonal family.
Source: SCP10, charge detection, lines 2474–2486. -/
theorem regularChargeDetectorMatrix_complete :
    (∀ χ ∈ regularChargeLabels (G := G), ∀ ψ ∈ regularChargeLabels (G := G),
      regularChargeDetectorMatrix χ * regularChargeDetectorMatrix ψ =
        if χ = ψ then regularChargeDetectorMatrix χ else 0) ∧
    (∑ χ ∈ regularChargeLabels (G := G), regularChargeDetectorMatrix χ = 1) := by
  classical
  constructor
  · intro χ hχ ψ hψ
    by_cases hχψ : χ = ψ
    · subst ψ
      simpa using (regularChargeDetectorMatrix_properties χ).2.2
    · rw [ite_eq_right hχψ]
      apply matrix_ext_on_chargeVectors
      intro τ hτ p x y
      rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec,
        regularChargeDetectorMatrix_label_vector ψ τ hψ hτ]
      by_cases hψτ : ψ = τ
      · subst τ
        rw [ite_eq_left rfl, regularChargeDetectorMatrix_label_vector χ ψ hχ hψ,
          ite_eq_right hχψ]
      · rw [ite_eq_right hψτ, Matrix.mulVec_zero]
  · apply matrix_ext_on_chargeVectors
    intro χ hχ p x y
    rw [Matrix.sum_mulVec, Matrix.one_mulVec]
    calc
      _ = ∑ ψ ∈ regularChargeLabels (G := G),
          if ψ = χ then (fun rs : G × G => regularChargeMatrix χ p x y rs.1 rs.2) else 0 := by
        apply Finset.sum_congr rfl
        intro ψ hψ
        exact regularChargeDetectorMatrix_label_vector ψ χ hψ hχ p x y
      _ = _ := by simp [hχ]

end TNLean.PEPS
