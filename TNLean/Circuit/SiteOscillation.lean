/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.LocalCircuit
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Site oscillation with a finite spectator

For an operator `B` on the physical sites and a finite spectator `Aux`, its
oscillation at the physical site `y` is
`d_y(B) = sup_U ‖(U ⊗ 1) B - B (U ⊗ 1)‖`, where `U` ranges over the unitaries
in the existing algebra `supportedOperators q {y}`. All norms in this file
are the full matrix operator norm induced by the Euclidean norm. Operators
need not be Hermitian, and the spectator has arbitrary finite dimension.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`09-amplification.tex`, lines 101–139, at revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

The defining set is nonempty and bounded by `2 * ‖B‖`. Thus its real
supremum is finite, bounds every permitted commutator, is subadditive and
absolutely homogeneous, and vanishes on operators commuting with the
algebra at `y`. These facts apply uniformly in the spectator dimension.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open Matrix
open scoped BigOperators Kronecker Matrix.Norms.L2Operator

namespace QuantumCircuit

variable {q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Aux : Type*} [Fintype Aux] [DecidableEq Aux]

/-- Oscillation at `y`, with the identity on the finite spectator `Aux`.
Source: area law, `09-amplification.tex`, lines 109–121. -/
noncomputable def siteOscillation (q : ℕ) (y : ι)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) : ℝ :=
  sSup {r | ∃ U : Matrix (ι → Fin q) (ι → Fin q) ℂ,
    U ∈ supportedOperators q ({y} : Set ι) ∧
    U ∈ unitary (Matrix (ι → Fin q) (ι → Fin q) ℂ) ∧
    ‖(U ⊗ₖ (1 : Matrix Aux Aux ℂ)) * B - B * (U ⊗ₖ 1)‖ = r}

private theorem norm_siteUnitary_commutator_le
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ)
    {U : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hU : U ∈ unitary (Matrix (ι → Fin q) (ι → Fin q) ℂ)) :
    ‖(U ⊗ₖ (1 : Matrix Aux Aux ℂ)) * B - B * (U ⊗ₖ 1)‖ ≤ 2 * ‖B‖ := by
  have hUA := Matrix.kronecker_mem_unitary hU
    (show (1 : Matrix Aux Aux ℂ) ∈ unitary _ from one_mem _)
  calc
    _ ≤ ‖(U ⊗ₖ (1 : Matrix Aux Aux ℂ)) * B‖ + ‖B * (U ⊗ₖ 1)‖ :=
      norm_sub_le _ _
    _ = ‖B‖ + ‖B‖ := by
      rw [CStarRing.norm_mem_unitary_mul B hUA, CStarRing.norm_mul_mem_unitary B hUA]
    _ = 2 * ‖B‖ := (two_mul _).symm

/-- The set defining the oscillation is bounded above, uniformly in `Aux`.
Source: area law, `09-amplification.tex`, line 127, `d_y(C) ≤ 2‖C‖`. -/
theorem siteOscillation_bddAbove (y : ι)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    BddAbove {r | ∃ U : Matrix (ι → Fin q) (ι → Fin q) ℂ,
      U ∈ supportedOperators q ({y} : Set ι) ∧
      U ∈ unitary (Matrix (ι → Fin q) (ι → Fin q) ℂ) ∧
      ‖(U ⊗ₖ (1 : Matrix Aux Aux ℂ)) * B - B * (U ⊗ₖ 1)‖ = r} := by
  refine ⟨2 * ‖B‖, ?_⟩
  rintro _ ⟨U, _, hU, rfl⟩
  exact norm_siteUnitary_commutator_le B hU

private theorem zero_mem_siteOscillation_values (y : ι)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    0 ∈ {r | ∃ U : Matrix (ι → Fin q) (ι → Fin q) ℂ,
      U ∈ supportedOperators q ({y} : Set ι) ∧
      U ∈ unitary (Matrix (ι → Fin q) (ι → Fin q) ℂ) ∧
      ‖(U ⊗ₖ (1 : Matrix Aux Aux ℂ)) * B - B * (U ⊗ₖ 1)‖ = r} := by
  exact ⟨1, one_mem_supportedOperators _, one_mem _, by simp⟩

/-- A supported physical unitary's commutator is bounded by the oscillation.
Source: area law, `09-amplification.tex`, lines 109–113. -/
theorem norm_commutator_le_siteOscillation (y : ι)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ)
    {U : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hSupport : U ∈ supportedOperators q ({y} : Set ι))
    (hUnitary : U ∈ unitary (Matrix (ι → Fin q) (ι → Fin q) ℂ)) :
    ‖(U ⊗ₖ (1 : Matrix Aux Aux ℂ)) * B - B * (U ⊗ₖ 1)‖ ≤
      siteOscillation q y B :=
  le_csSup (siteOscillation_bddAbove y B) ⟨U, hSupport, hUnitary, rfl⟩

/-- The same bound with the two arguments of the commutator exchanged. -/
theorem norm_commutator_le_siteOscillation_right (y : ι)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ)
    {U : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hSupport : U ∈ supportedOperators q ({y} : Set ι))
    (hUnitary : U ∈ unitary (Matrix (ι → Fin q) (ι → Fin q) ℂ)) :
    ‖B * (U ⊗ₖ (1 : Matrix Aux Aux ℂ)) - (U ⊗ₖ 1) * B‖ ≤
      siteOscillation q y B := by
  rw [norm_sub_rev]
  exact norm_commutator_le_siteOscillation y B hSupport hUnitary

/-- Site oscillation is nonnegative, including on an empty spectator space. -/
theorem siteOscillation_nonneg (y : ι)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    0 ≤ siteOscillation q y B :=
  le_csSup (siteOscillation_bddAbove y B) (zero_mem_siteOscillation_values y B)

/-- A common upper bound on the defining commutators bounds the oscillation. -/
theorem siteOscillation_le (y : ι)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) {r : ℝ}
    (h : ∀ U ∈ supportedOperators q ({y} : Set ι),
      U ∈ unitary (Matrix (ι → Fin q) (ι → Fin q) ℂ) →
      ‖(U ⊗ₖ (1 : Matrix Aux Aux ℂ)) * B - B * (U ⊗ₖ 1)‖ ≤ r) :
    siteOscillation q y B ≤ r := by
  refine csSup_le ⟨0, zero_mem_siteOscillation_values y B⟩ ?_
  rintro _ ⟨U, hSupport, hUnitary, rfl⟩
  exact h U hSupport hUnitary

/-- The elementary oscillation estimate, with no spectator dimension factor.
Source: area law, `09-amplification.tex`, line 127. -/
theorem siteOscillation_le_two_mul_norm (y : ι)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    siteOscillation q y B ≤ 2 * ‖B‖ := by
  exact siteOscillation_le y B fun _ _ hU => norm_siteUnitary_commutator_le B hU

/-- Oscillation is subadditive, as used when telescoping the channel shells.
Source: area law, `09-amplification.tex`, lines 126–132. -/
theorem siteOscillation_add_le (y : ι)
    (B C : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    siteOscillation q y (B + C) ≤ siteOscillation q y B + siteOscillation q y C := by
  apply siteOscillation_le
  intro U hSupport hUnitary
  calc
    _ = ‖((U ⊗ₖ (1 : Matrix Aux Aux ℂ)) * B - B * (U ⊗ₖ 1)) +
        ((U ⊗ₖ 1) * C - C * (U ⊗ₖ 1))‖ := by
      rw [mul_add, add_mul, add_sub_add_comm]
    _ ≤ ‖(U ⊗ₖ (1 : Matrix Aux Aux ℂ)) * B - B * (U ⊗ₖ 1)‖ +
        ‖(U ⊗ₖ 1) * C - C * (U ⊗ₖ 1)‖ := norm_add_le _ _
    _ ≤ _ := add_le_add (norm_commutator_le_siteOscillation y B hSupport hUnitary)
      (norm_commutator_le_siteOscillation y C hSupport hUnitary)

/-- Oscillation vanishes when the operator commutes with the physical algebra
at `y`. Source: area law, `09-amplification.tex`, lines 109–115. -/
theorem siteOscillation_eq_zero_of_commute (y : ι)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ)
    (h : ∀ U ∈ supportedOperators q ({y} : Set ι),
      Commute (U ⊗ₖ (1 : Matrix Aux Aux ℂ)) B) :
    siteOscillation q y B = 0 := by
  apply le_antisymm _ (siteOscillation_nonneg y B)
  apply siteOscillation_le
  intro U hSupport _
  simp [(h U hSupport).eq]

@[simp]
theorem siteOscillation_zero (y : ι) :
    siteOscillation q y (0 : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) = 0 :=
  siteOscillation_eq_zero_of_commute y 0 fun _ _ => Commute.zero_right _

/-- An operator acting only on the spectator has zero oscillation at every
physical site. -/
@[simp]
theorem siteOscillation_one_kronecker (y : ι) (C : Matrix Aux Aux ℂ) :
    siteOscillation q y ((1 : Matrix (ι → Fin q) (ι → Fin q) ℂ) ⊗ₖ C) = 0 := by
  apply siteOscillation_eq_zero_of_commute
  intro U _
  change (U ⊗ₖ 1) * (1 ⊗ₖ C) = (1 ⊗ₖ C) * (U ⊗ₖ 1)
  simp only [← Matrix.mul_kronecker_mul, mul_one, one_mul]

private theorem siteOscillation_smul_le (y : ι) (c : ℂ)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    siteOscillation q y (c • B) ≤ ‖c‖ * siteOscillation q y B := by
  apply siteOscillation_le
  intro U hSupport hUnitary
  rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, norm_smul]
  exact mul_le_mul_of_nonneg_left
    (norm_commutator_le_siteOscillation y B hSupport hUnitary) (norm_nonneg c)

/-- Site oscillation is absolutely homogeneous for arbitrary complex scalars. -/
@[simp]
theorem siteOscillation_smul (y : ι) (c : ℂ)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    siteOscillation q y (c • B) = ‖c‖ * siteOscillation q y B := by
  by_cases hc : c = 0
  · simp [hc]
  apply le_antisymm (siteOscillation_smul_le y c B)
  have h := siteOscillation_smul_le y c⁻¹ (c • B)
  rw [inv_smul_smul₀ hc, norm_inv] at h
  have hcNorm : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  simpa only [← mul_assoc, mul_inv_cancel₀ hcNorm, one_mul] using
    mul_le_mul_of_nonneg_left h (norm_nonneg c)

@[simp]
theorem siteOscillation_neg (y : ι)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    siteOscillation q y (-B) = siteOscillation q y B := by
  simpa using siteOscillation_smul y (-1 : ℂ) B

/-- The oscillation of a difference is bounded by the sum of the oscillations. -/
theorem siteOscillation_sub_le (y : ι)
    (B C : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    siteOscillation q y (B - C) ≤ siteOscillation q y B + siteOscillation q y C := by
  simpa only [sub_eq_add_neg, siteOscillation_neg] using siteOscillation_add_le y B (-C)

/-- Oscillation is subadditive over a finite sum of arbitrary operators. -/
theorem siteOscillation_sum_le {κ : Type*} (y : ι) (s : Finset κ)
    (B : κ → Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    siteOscillation q y (∑ k ∈ s, B k) ≤ ∑ k ∈ s, siteOscillation q y (B k) := by
  apply siteOscillation_le
  intro U hSupport hUnitary
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  exact Finset.sum_le_sum fun k _ =>
    norm_commutator_le_siteOscillation y (B k) hSupport hUnitary

end QuantumCircuit
