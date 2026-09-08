/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CZXSourceFactors
import TNLean.MPS.MPDO.CZXDaggerGauge

/-!
# Normalization of the displayed CZX comparison

For the explicit factors in arXiv:2502.20257, lines 4559–4659, the reflected
candidates of lines 5432–5441 are the negatives of the displayed first factors
when the maintained Pauli gauge is used. The raw left overlap is `-2 I`, whereas
the right overlap and the density-weighted left overlap are both `-I`.
The raw left overlap is not unitary; the weighted comparison is unitary and
recovers both first factors.

**Scope restriction (displayed-factor overlaps):** This calculation concerns
the explicit witness `displayedSourceFactors`, not choice-selected SVD factors.
Its cut factorizations, inverse identities, and weighted normalization are
certified, but this file does not certify every pleasant property assumed at
the start of the source proof. Thus the unequal overlaps diagnose only the
intermediate formula in lines 5438–5441 on these displayed factors, not a
counterexample to the full proposition. No gauge phase is changed. The weighted
comparison is consistent with the correction discussed in
`docs/paper-gaps/fbc25_inverse_compatible_tilde_omission.tex`.
-/

noncomputable section

open scoped Matrix BigOperators Kronecker

namespace MPOTensor.CZX

/-- The reflected left candidate with entrywise conjugation of the maintained
Pauli gauge. Source: arXiv:2502.20257, lines 5432–5441. -/
def displayedReflectedX₁ : Matrix (Fin 4 × Fin 2) (Fin 4) ℂ :=
  ((1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ daggerGauge.map (starRingEnd ℂ)) * displayedY₂ᴴ

/-- The reflected right candidate, with the virtual leg first in the product
column index. Source: arXiv:2502.20257, lines 5432–5441. -/
def displayedReflectedY₁ : Matrix (Fin 4) (Fin 2 × Fin 4) ℂ :=
  displayedX₂ᴴ * (daggerGauge.transpose ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℂ))

/-- The raw left overlap in arXiv:2502.20257, lines 5438–5441, evaluated on
its displayed CZX factors. -/
def displayedRawComparison : Matrix (Fin 4) (Fin 4) ℂ :=
  displayedX₁ᴴ * displayedReflectedX₁

/-- The comparison using the actual left inverse from the density-weighted
normalization, with `ρ = I₂/2`. Source: arXiv:2502.20257, lines 5432–5441,
and the displayed CZX factors in lines 4559–4659. -/
def displayedWeightedComparison : Matrix (Fin 4) (Fin 4) ℂ :=
  displayedX₁ᴴ * sourceWeight (d := 4) (D := 2) ((1 / 2 : ℂ) • 1) * displayedReflectedX₁

/-- Both reflected candidates carry a minus sign for the chosen Pauli gauge.
Source: arXiv:2502.20257, lines 4547–4659 and 5432–5441. -/
theorem displayedReflected_eq_neg :
    displayedReflectedX₁ = -displayedX₁ ∧ displayedReflectedY₁ = -displayedY₁ := by
  have ht : daggerGauge.transpose = -daggerGauge := by
    calc
      daggerGauge.transpose = daggerGaugeᴴ.transpose :=
        congrArg Matrix.transpose daggerGauge_conjTranspose.symm
      _ = daggerGauge.map (starRingEnd ℂ) := rfl
      _ = -daggerGauge := daggerGauge_map_star
  constructor
  · rw [displayedReflectedX₁, daggerGauge_map_star, displayedX₁_eq_kronecker_mul,
      ← neg_one_smul ℂ daggerGauge, Matrix.kronecker_smul, Matrix.smul_mul, neg_one_smul]
  · rw [displayedReflectedY₁, ht, displayedY₁_eq_mul_kronecker,
      ← neg_one_smul ℂ daggerGauge, Matrix.smul_kronecker, Matrix.mul_smul, neg_one_smul]

/-- The raw left, weighted left, and raw right overlaps of the displayed
factors. Source: arXiv:2502.20257, lines 5438–5441 and 4559–4659. -/
theorem displayedComparison_coordinates :
    displayedRawComparison = (-2 : ℂ) • 1 ∧
    displayedWeightedComparison = -(1 : Matrix (Fin 4) (Fin 4) ℂ) ∧
    displayedY₁ * displayedReflectedY₁ᴴ = -(1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [displayedRawComparison, displayedReflected_eq_neg.1, Matrix.mul_neg, displayed_grams.1]
    simp
  · rw [displayedWeightedComparison, displayedReflected_eq_neg.1, Matrix.mul_neg,
      displayed_normalizations.2.2]
  · rw [displayedReflected_eq_neg.2, Matrix.conjTranspose_neg, Matrix.mul_neg,
      displayed_grams.2.2.1]

/-- The raw left overlap has Gram matrix `4 I`, rather than the identity.
Source: the raw overlap in arXiv:2502.20257, lines 5438–5441. -/
theorem displayedRawComparison_gram :
    displayedRawComparisonᴴ * displayedRawComparison = (4 : ℂ) • 1 := by
  rw [displayedComparison_coordinates.1]
  norm_num [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

/-- The raw left overlap is not unitary on the displayed factor space.
Source: arXiv:2502.20257, lines 5438–5441. -/
theorem displayedRawComparison_not_isUnitaryBetween :
    ¬ displayedRawComparison.IsUnitaryBetween := by
  intro h
  have hi := h.1
  rw [Matrix.IsIsometry, displayedRawComparison_gram] at hi
  have h00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ ↦ M 0 0) hi
  norm_num at h00

/-- The two printed raw overlap formulas disagree on the displayed factors.
Source: arXiv:2502.20257, lines 5438–5441. -/
theorem displayedRawComparison_ne_rightOverlap :
    displayedRawComparison ≠ displayedY₁ * displayedReflectedY₁ᴴ := by
  rw [displayedComparison_coordinates.1, displayedComparison_coordinates.2.2]
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ ↦ M 0 0) h
  norm_num at h00

/-- The weighted overlap is unitary and gives both comparison identities for
the displayed factors. Source: arXiv:2502.20257, lines 5432–5441; the weight is
the one in the actual normalization of the first left factor. -/
theorem displayedWeightedComparison_spec :
    displayedWeightedComparison.IsUnitaryBetween ∧
    displayedX₁ = displayedReflectedX₁ * displayedWeightedComparisonᴴ ∧
    displayedY₁ = displayedWeightedComparison * displayedReflectedY₁ := by
  rw [displayedComparison_coordinates.2.1,
    displayedReflected_eq_neg.1, displayedReflected_eq_neg.2]
  constructor
  · constructor <;> simp [Matrix.IsIsometry, Matrix.IsCoisometry]
  · simp

end MPOTensor.CZX
