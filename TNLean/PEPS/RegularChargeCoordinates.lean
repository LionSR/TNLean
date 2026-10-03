/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.TranslatedCharacterOrthogonality
import Mathlib.Data.Matrix.Basis

/-!
# Actual two-site charge coordinates

The accessible charge matrix is a sum of matrix units with character weights.
The two unknown vertex translations determine its row and column coordinates.
The relative translation fixes its support, and inequivalent irreducible
characters give orthogonal matrices for every choice of these translations.
Source: SCP10, arXiv:1001.3807, charge detection, lines 2464–2486. These are
auxiliary accessible-coordinate identities; no original-spin measurement is
asserted here.
-/

open scoped BigOperators
namespace TNLean.PEPS
variable {G : Type*} [Group G] [Fintype G]

open Classical in
/-- The actual accessible charge matrix, including both unknown translations.
Source: SCP10, charge detection, lines 2470–2486. -/
noncomputable def regularChargeMatrix (χ : G → ℂ) (p x y : G) : Matrix G G ℂ :=
  fun r s => if y * (x⁻¹ * r) = s then χ (p * (x⁻¹ * r)) else 0

open Classical in
/-- The coordinate formula is the literal character-weighted matrix-unit sum.
Source: SCP10, charge detection, lines 2470–2480. -/
theorem regularChargeMatrix_eq_sum_single (χ : G → ℂ) (p x y : G) :
    regularChargeMatrix χ p x y = ∑ g, χ (p * g) • Matrix.single (x * g) (y * g) 1 := by
  classical
  ext r s
  have hrow (g : G) : x * g = r ↔ g = x⁻¹ * r := by
    constructor
    · intro h
      rw [← h]
      group
    · rintro rfl
      group
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply]
  simp [regularChargeMatrix, hrow, ite_and]

open Classical in
/-- The relative translation determines all support overlap of two charge matrices.
Source: SCP10, charge detection, lines 2474–2486; auxiliary coordinate identity. -/
theorem regularChargeMatrix_inner (χ ψ : G → ℂ) (p x y q x' y' : G) :
    ∑ r, ∑ s, star (regularChargeMatrix χ p x y r s) *
      regularChargeMatrix ψ q x' y' r s =
      if y * x⁻¹ = y' * x'⁻¹ then
        ∑ r, star (χ (p * (x⁻¹ * r))) * ψ (q * (x'⁻¹ * r)) else 0 := by
  classical
  by_cases hz : y * x⁻¹ = y' * x'⁻¹
  · rw [ite_eq_left hz]
    apply Finset.sum_congr rfl
    intro r _
    have hc : y * (x⁻¹ * r) = y' * (x'⁻¹ * r) := by
      simp only [← mul_assoc, hz]
    simp [regularChargeMatrix, hc]
  · rw [ite_eq_right hz]
    apply Finset.sum_eq_zero
    intro r _
    have hc : y * (x⁻¹ * r) ≠ y' * (x'⁻¹ * r) := by
      intro h
      apply hz
      apply mul_right_cancel (b := r)
      simpa only [mul_assoc] using h
    apply Finset.sum_eq_zero
    intro s _
    dsimp only [regularChargeMatrix]
    split_ifs <;> simp_all

omit [Fintype G] in
/-- A change of the internal label can be absorbed into the two unknown translations.
Source: SCP10, charge detection, lines 2483–2486; exact coordinate identity. -/
theorem regularChargeMatrix_internalLabel
    (χ : G → ℂ) (p q x y : G) :
    regularChargeMatrix χ q (x * p⁻¹ * q) (y * p⁻¹ * q) =
      regularChargeMatrix χ p x y := by
  classical
  ext r s
  have hx : q * ((x * p⁻¹ * q)⁻¹ * r) = p * (x⁻¹ * r) := by group
  have hy : (y * p⁻¹ * q) * ((x * p⁻¹ * q)⁻¹ * r) = y * (x⁻¹ * r) := by group
  simp only [regularChargeMatrix, hx, hy]

omit [Fintype G] in
/-- Independent vertex translations act by the corresponding row and column permutations.
Source: SCP10, the unknown translations in charge detection, lines 2470–2486. -/
theorem regularChargeMatrix_translate_apply
    (χ : G → ℂ) (p x y z w r s : G) :
    regularChargeMatrix χ p (z * x) (w * y) r s =
      regularChargeMatrix χ p x y (z⁻¹ * r) (w⁻¹ * s) := by
  classical
  have hc : (w * y) * ((z * x)⁻¹ * r) = s ↔
      y * (x⁻¹ * (z⁻¹ * r)) = w⁻¹ * s := by
    constructor
    · intro h
      calc
        _ = w⁻¹ * ((w * y) * ((z * x)⁻¹ * r)) := by group
        _ = _ := by rw [h]
    · intro h
      calc
        _ = w * (y * (x⁻¹ * (z⁻¹ * r))) := by group
        _ = w * (w⁻¹ * s) := by rw [h]
        _ = s := by group
  simp only [regularChargeMatrix]
  rw [hc]
  simp only [mul_inv_rev, mul_assoc]

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- Distinct irreducible charge labels give orthogonal actual two-site matrices,
for arbitrary internal states and unknown vertex translations.
Source: SCP10, charge detection, lines 2470–2486. -/
theorem regularChargeMatrix_orthogonal
    (σ : Representation ℂ G E) (τ : Representation ℂ G F)
    [σ.IsIrreducible] [τ.IsIrreducible]
    (hσ : ∀ g, LinearMap.adjoint (σ g) = σ g⁻¹)
    (hne : σ.character ≠ τ.character) (p x y q x' y' : G) :
    ∑ r, ∑ s, star (regularChargeMatrix σ.character p x y r s) *
      regularChargeMatrix τ.character q x' y' r s = 0 := by
  classical
  rw [regularChargeMatrix_inner]
  split_ifs
  · simpa only [mul_assoc] using
      Representation.sum_star_character_mul_character_translate_eq_zero σ τ hσ hne
        (p * x⁻¹) (q * x'⁻¹)
  · rfl

/-- Each actual two-site charge matrix has squared norm equal to the group order.
Source: SCP10, charge detection, lines 2470–2486; explicit normalization. -/
theorem regularChargeMatrix_normSq
    (σ : Representation ℂ G E) [σ.IsIrreducible]
    (hσ : ∀ g, LinearMap.adjoint (σ g) = σ g⁻¹) (p x y : G) :
    ∑ r, ∑ s, star (regularChargeMatrix σ.character p x y r s) *
      regularChargeMatrix σ.character p x y r s = (Nat.card G : ℂ) := by
  classical
  rw [regularChargeMatrix_inner, ite_eq_left rfl]
  simpa only [mul_assoc] using
    Representation.sum_star_character_mul_character_self σ hσ (p * x⁻¹)

omit [Fintype G] in
/-- Every irreducible charge label and internal state gives a nonzero accessible matrix.
Source: SCP10, charge detection, lines 2470–2486; consequence of the explicit norm. -/
theorem regularChargeMatrix_ne_zero
    (σ : Representation ℂ G E) [σ.IsIrreducible]
    (hσ : ∀ g, LinearMap.adjoint (σ g) = σ g⁻¹) [Finite G] (p x y : G) :
    regularChargeMatrix σ.character p x y ≠ 0 := by
  classical
  let : Fintype G := Fintype.ofFinite G
  intro hz
  have hn := regularChargeMatrix_normSq σ hσ p x y
  simp only [hz, Matrix.zero_apply, star_zero, zero_mul, Finset.sum_const_zero] at hn
  exact Representation.natCard_ne_zero_complex (G := G) hn.symm

end TNLean.PEPS
