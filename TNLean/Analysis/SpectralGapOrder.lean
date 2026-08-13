/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Spectral-gap monotonicity under Loewner order

This file transfers a norm-form spectral gap from a positive operator `K` to an
operator `H` above it in Loewner order, provided their kernels agree. If `K ≤ H`,
then every Rayleigh quotient of `H` is at least the corresponding Rayleigh
quotient of `K`. The spectral theorem converts a norm
lower bound for `K` on its kernel complement into the required Rayleigh lower
bound, which then transfers to `H`.

The argument does not compare `‖K v‖` and `‖H v‖` pointwise. Such a comparison
is false for noncommuting positive operators.
-/

open scoped BigOperators InnerProductSpace

namespace LinearMap.IsPositive

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- A norm-form spectral gap of a positive operator is monotone under Loewner
order when the kernels agree.

This is the finite-dimensional comparison principle underlying Nachtergaele,
arXiv:cond-mat/9410110, equation (3.14). The proof diagonalizes `K`, obtains the
Rayleigh bound `γ ‖v‖² ≤ re ⟪K v, v⟫` on `(ker K)ᗮ`, transfers it through
`K ≤ H`, and applies Cauchy--Schwarz. -/
theorem norm_gap_mono_of_le_of_ker_eq {K H : E →ₗ[ℂ] E} {γ : ℝ}
    (hK : K.IsPositive) (hKH : K ≤ H)
    (hker : LinearMap.ker K = LinearMap.ker H)
    (hgap : ∀ v ∈ (LinearMap.ker K)ᗮ, γ * ‖v‖ ≤ ‖K v‖) :
    ∀ v ∈ (LinearMap.ker H)ᗮ, γ * ‖v‖ ≤ ‖H v‖ := by
  classical
  set n := Module.finrank ℂ E with hn_def
  have hn : Module.finrank ℂ E = n := hn_def.symm
  set b := hK.isSymmetric.eigenvectorBasis hn with hb_def
  set μ := hK.isSymmetric.eigenvalues hn with hμ_def
  have hK_apply (i : Fin n) : K (b i) = (μ i : ℂ) • b i :=
    hK.isSymmetric.apply_eigenvectorBasis hn i
  have hμ_nonneg (i : Fin n) : 0 ≤ μ i := hK.nonneg_eigenvalues hn i
  have hμ_gap (i : Fin n) : μ i = 0 ∨ γ ≤ μ i := by
    by_cases hi : μ i = 0
    · exact Or.inl hi
    · right
      have hbi_ker : b i ∈ (LinearMap.ker K)ᗮ := by
        rw [Submodule.mem_orthogonal']
        intro x hx
        have hKx : K x = 0 := LinearMap.mem_ker.mp hx
        have hinner : ⟪K (b i), x⟫_ℂ = ⟪b i, K x⟫_ℂ := hK.isSymmetric (b i) x
        rw [hK_apply, inner_smul_left, hKx, inner_zero_right] at hinner
        simpa [hi] using hinner
      have h := hgap (b i) hbi_ker
      rw [hK_apply, norm_smul] at h
      simpa [RCLike.norm_ofReal, abs_of_nonneg (hμ_nonneg i), b.norm_eq_one] using h
  intro v hv
  have hvK : v ∈ (LinearMap.ker K)ᗮ := by simpa [hker] using hv
  have hzero_coeff (i : Fin n) (hi : μ i = 0) : b.repr v i = 0 := by
    rw [b.repr_apply_apply]
    apply Submodule.inner_right_of_mem_orthogonal _ hvK
    rw [LinearMap.mem_ker, hK_apply, hi]
    simp
  have hK_rayleigh : γ * ‖v‖ ^ 2 ≤ (⟪K v, v⟫_ℂ).re := by
    rw [show (⟪K v, v⟫_ℂ).re = (⟪v, K v⟫_ℂ).re from inner_re_symm (𝕜 := ℂ) (K v) v,
      ← b.sum_sq_norm_inner_right v, Finset.mul_sum,
      ← b.sum_inner_mul_inner v (K v), Complex.re_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← b.repr_apply_apply v i,
      ← b.repr_apply_apply (K v) i,
      hK.isSymmetric.eigenvectorBasis_apply_self_apply hn,
      ← inner_conj_symm, ← b.repr_apply_apply v i]
    rw [← hμ_def, ← hb_def]
    rcases hμ_gap i with hi | hi
    · rw [hzero_coeff i hi]
      simp
    · change γ * ‖b.repr v i‖ ^ 2 ≤
        ((starRingEnd ℂ) (b.repr v i) * ((μ i : ℂ) * b.repr v i)).re
      rw [← mul_assoc, mul_comm ((starRingEnd ℂ) (b.repr v i)) (μ i : ℂ),
        mul_assoc, ← Complex.normSq_eq_conj_mul_self,
        Complex.normSq_eq_norm_sq]
      norm_cast
      exact mul_le_mul_of_nonneg_right hi (sq_nonneg _)
  have horder : (⟪K v, v⟫_ℂ).re ≤ (⟪H v, v⟫_ℂ).re := by
    have := hKH.re_inner_nonneg_left v
    simpa [sub_apply, inner_sub_left] using this
  have hcs : (⟪H v, v⟫_ℂ).re ≤ ‖H v‖ * ‖v‖ := by
    calc
      (⟪H v, v⟫_ℂ).re ≤ ‖⟪H v, v⟫_ℂ‖ := Complex.re_le_norm _
      _ ≤ ‖H v‖ * ‖v‖ := norm_inner_le_norm _ _
  by_cases hvzero : v = 0
  · simp [hvzero]
  · have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hvzero
    apply le_of_mul_le_mul_right _ hvpos
    calc
      γ * ‖v‖ * ‖v‖ = γ * ‖v‖ ^ 2 := by ring
      _ ≤ (⟪K v, v⟫_ℂ).re := hK_rayleigh
      _ ≤ (⟪H v, v⟫_ℂ).re := horder
      _ ≤ ‖H v‖ * ‖v‖ := hcs

end LinearMap.IsPositive
