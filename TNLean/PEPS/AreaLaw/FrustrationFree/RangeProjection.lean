/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Sites.Twirl
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Range projections of positive local terms

For a square complex matrix `A`, the range projection is `Π_A = f(A)` with `f(x) = x x⁻¹`, the
indicator of `x ≠ 0`, in the continuous functional calculus. For a positive semidefinite
`A ≤ J`, the range projection is an orthogonal projection with `A ≤ J Π_A`, it annihilates every
vector annihilated by `A`, and it acts on the sites on which `A` acts.

The frustration-free area-law note sweeps with the factors `(1 - h_i / J)^{1/2}`. Replacing them
by `1 - Π_{h_i}` keeps the three properties the note uses: each factor fixes the ground vector,
acts on the support of its term, and the terms `Π_{h_i} ≥ h_i / J` still satisfy the gap
`∑ Π_{h_i} ≥ (Δ/J)(1 - P)`.

## Main definitions

* `Matrix.rangeProj`: the range projection.

## Main statements

* `Matrix.isStarProjection_rangeProj`: it is an orthogonal projection.
* `Matrix.rangeProj_mulVec_eq_zero`: it annihilates the kernel.
* `Matrix.le_smul_rangeProj`: `A ≤ J Π_A` when `0 ≤ A ≤ J`.
* `ManyBody.rangeProj_mem_supportedOperators`: it acts on the support of `A`.

## References

* Reading note *Entanglement across a cut in two-dimensional frustration-free ground states*,
  November 18, 2026, `docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`,
  paragraph "Contraction in one sweep".
-/

open scoped MatrixOrder ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The range projection `Π_A = f(A)`, `f(x) = x x⁻¹`, of a square complex matrix in the
continuous functional calculus. It is zero unless `A` is Hermitian. -/
noncomputable def rangeProj (A : Matrix n n ℂ) : Matrix n n ℂ :=
  cfc (fun x : ℝ ↦ x * x⁻¹) A

/-- The range projection is an orthogonal projection. -/
theorem isStarProjection_rangeProj (A : Matrix n n ℂ) : IsStarProjection (rangeProj A) := by
  by_cases hA : IsSelfAdjoint A
  · refine ⟨?_, cfc_predicate _ A⟩
    have hc := A.finite_real_spectrum.continuousOn (fun x : ℝ ↦ x * x⁻¹)
    rw [IsIdempotentElem, rangeProj, ← cfc_mul _ _ A hc hc]
    refine cfc_congr fun x _ ↦ ?_
    by_cases hx : x = 0
    · simp [hx]
    · simp [hx]
  · rw [rangeProj, cfc_apply_of_not_predicate A hA]
    exact IsStarProjection.zero _

/-- The range projection factors as `A⁻¹ A` in the functional calculus. -/
theorem rangeProj_eq_cfc_inv_mul (A : Matrix n n ℂ) :
    rangeProj A = cfc (fun x : ℝ ↦ x⁻¹) A * A := by
  by_cases hA : IsSelfAdjoint A
  · have hc := A.finite_real_spectrum.continuousOn (fun x : ℝ ↦ x⁻¹)
    have hid := A.finite_real_spectrum.continuousOn (fun x : ℝ ↦ x)
    have hm := cfc_mul (fun x : ℝ ↦ x⁻¹) (fun x : ℝ ↦ x) A hc hid
    rw [cfc_id' ℝ A] at hm
    rw [← hm, rangeProj]
    exact cfc_congr fun x _ ↦ mul_comm _ _
  · rw [rangeProj, cfc_apply_of_not_predicate A hA, cfc_apply_of_not_predicate A hA, zero_mul]

/-- The range projection annihilates every vector annihilated by `A`. -/
theorem rangeProj_mulVec_eq_zero {A : Matrix n n ℂ} {v : n → ℂ} (hv : A *ᵥ v = 0) :
    rangeProj A *ᵥ v = 0 := by
  rw [rangeProj_eq_cfc_inv_mul, ← mulVec_mulVec, hv, mulVec_zero]

/-- For `0 ≤ A ≤ J`, the range projection dominates `A / J`: `A ≤ J Π_A`. -/
theorem le_smul_rangeProj {A : Matrix n n ℂ} (hA : 0 ≤ A) {J : ℝ}
    (hAJ : A ≤ J • (1 : Matrix n n ℂ)) : A ≤ J • rangeProj A := by
  have hsa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA
  have hspec : ∀ x ∈ spectrum ℝ A, x ≤ J := by
    rw [← Algebra.algebraMap_eq_smul_one] at hAJ
    exact (le_algebraMap_iff_spectrum_le hsa).mp hAJ
  have hc := A.finite_real_spectrum.continuousOn (fun x : ℝ ↦ x * x⁻¹)
  rw [rangeProj, ← cfc_const_mul J _ A hc]
  conv_lhs => rw [← cfc_id' ℝ A]
  refine cfc_mono (fun x hx ↦ ?_) (A.finite_real_spectrum.continuousOn _)
    (A.finite_real_spectrum.continuousOn _)
  by_cases hx0 : x = 0
  · simp [hx0]
  · rw [mul_inv_cancel₀ hx0, mul_one]
    exact hspec x hx

end Matrix

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)]

/-- The range projection of an operator acting on a region acts on the same region. -/
theorem rangeProj_mem_supportedOperators {D : Finset V} {A : Matrix (Config X) (Config X) ℂ}
    (hA : A ∈ supportedOperators X D) : A.rangeProj ∈ supportedOperators X D :=
  cfc_mem_supportedOperators _ hA

end ManyBody
