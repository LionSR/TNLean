/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.UnitaryKronecker

/-!
# Unitarity from an adjoint Kronecker product

For a complex matrix between two nonempty finite coordinate spaces, unitarity
of $K^\dagger \otimes K$ implies unitarity of $K$. No equality of the two
coordinate-space cardinalities is assumed.

This is the general matrix implication used in arXiv:2502.20257,
lines 5444--5487, after the gate identity
$u=\sigma(K^\dagger\otimes K)v^\dagger$. The gate identity itself is not
asserted here.
-/

open scoped Kronecker ComplexOrder

namespace Matrix

/-- A complex matrix is unitary between its coordinate spaces if its adjoint
Kronecker product is unitary. The reciprocal scalar Gram matrices have scalar
square one; Gram positivity excludes the negative root.

Source use: arXiv:2502.20257, lines 5444--5487. This implication applies to
rectangular matrices without an equal-cardinality hypothesis. -/
theorem isUnitaryBetween_of_conjTranspose_kronecker
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [Nonempty m] [Nonempty n] {K : Matrix m n ℂ}
    (hK : (Kᴴ ⊗ₖ K).IsUnitaryBetween) : K.IsUnitaryBetween := by
  have hgram : (K * Kᴴ) ⊗ₖ (Kᴴ * K) = 1 := by
    simpa only [IsIsometry, conjTranspose_kronecker,
      conjTranspose_conjTranspose, ← mul_kronecker_mul] using hK.1
  obtain ⟨c, hc, hA, hB⟩ := exists_eq_smul_one_of_kronecker_eq_one hgram
  have hsquare : (K * Kᴴ) * (K * Kᴴ) = 1 := by
    calc
      _ = K * (Kᴴ * K) * Kᴴ := by simp only [Matrix.mul_assoc]
      _ = c⁻¹ • (K * Kᴴ) := by
        rw [hB, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
      _ = 1 := by rw [hA, smul_smul, inv_mul_cancel₀ hc, one_smul]
  let i : m := Classical.choice inferInstance
  have hcc : c * c = 1 := by
    have h := congrArg (fun M : Matrix m m ℂ ↦ M i i) hsquare
    simpa [hA, Matrix.smul_mul, Matrix.mul_smul, smul_smul] using h
  have hnonneg : 0 ≤ c := by
    have h := (posSemidef_self_mul_conjTranspose K).diag_nonneg (i := i)
    simpa [hA] using h
  have hc_one : c = 1 := by
    rcases mul_self_eq_one_iff.mp hcc with h | h
    · exact h
    · have hreal := (Complex.nonneg_iff.mp hnonneg).1
      norm_num [h] at hreal
  constructor
  · simpa only [IsIsometry, hc_one, inv_one, one_smul] using hB
  · simpa only [IsCoisometry, hc_one, one_smul] using hA

end Matrix
