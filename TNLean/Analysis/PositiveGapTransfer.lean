/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Transfer of gaps through positive-operator comparison

This file packages the finite-dimensional spectral argument used to transfer a
known gap from a positive operator to a larger positive operator with the same
kernel.

## Main results

* `LinearMap.IsPositive.re_inner_ge_of_norm_gap` converts a norm gap on the
  orthogonal complement of the kernel into a quadratic-form lower bound.
* `LinearMap.IsPositive.norm_gap_of_le_of_ker_eq` transfers a norm gap through
  Loewner domination when the kernels agree.
-/

open scoped InnerProductSpace

namespace LinearMap.IsPositive

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- For a positive operator, a norm lower bound on the orthogonal complement
of its kernel implies the same quadratic-form lower bound. -/
theorem re_inner_ge_of_norm_gap {P : E →ₗ[ℂ] E} (hP : P.IsPositive)
    {γ : ℝ} (_hγ : 0 ≤ γ)
    (hGap : ∀ v ∈ (LinearMap.ker P)ᗮ, γ * ‖v‖ ≤ ‖P v‖)
    (v : E) (hv : v ∈ (LinearMap.ker P)ᗮ) :
    γ * ‖v‖ ^ 2 ≤ (⟪P v, v⟫_ℂ).re := by
  classical
  let n := Module.finrank ℂ E
  let b := hP.isSymmetric.eigenvectorBasis rfl
  let μ := hP.isSymmetric.eigenvalues rfl
  have hμ : ∀ i, 0 ≤ μ i := hP.nonneg_eigenvalues rfl
  have hμGap : ∀ i, μ i = 0 ∨ γ ≤ μ i := by
    intro i
    by_cases hi : μ i = 0
    · exact Or.inl hi
    · right
      have hbi : b i ∈ (LinearMap.ker P)ᗮ := by
        intro w hw
        rw [LinearMap.mem_ker] at hw
        have horth := hP.isSymmetric w (b i)
        rw [hw, inner_zero_left, hP.isSymmetric.apply_eigenvectorBasis rfl,
          inner_smul_right] at horth
        exact (mul_eq_zero.mp horth.symm).resolve_left (Complex.ofReal_ne_zero.mpr hi)
      have h := hGap (b i) hbi
      rw [hP.isSymmetric.apply_eigenvectorBasis rfl, norm_smul,
        OrthonormalBasis.norm_eq_one] at h
      have h' : γ ≤ |μ i| := by
        simpa only [RCLike.norm_ofReal, mul_one] using h
      rwa [abs_of_nonneg (hμ i)] at h'
  have hv_sq : ‖v‖ ^ 2 = ∑ i, ‖(b.repr v) i‖ ^ 2 := by
    rw [← b.repr.norm_map v, EuclideanSpace.norm_sq_eq]
  have hPv : P v = ∑ i, ((μ i : ℂ) * (b.repr v) i) • b i := by
    nth_rw 1 [← b.sum_repr v]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_smul, hP.isSymmetric.apply_eigenvectorBasis rfl, smul_smul]
    congr 1
    exact mul_comm _ _
  have hquad : (⟪P v, v⟫_ℂ).re =
      ∑ i, μ i * ‖(b.repr v) i‖ ^ 2 := by
    rw [hPv, sum_inner, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [inner_smul_left, b.repr_apply_apply, map_mul, Complex.conj_ofReal]
    rw [mul_assoc]
    rw [← Complex.normSq_eq_conj_mul_self]
    rw [Complex.sq_norm]
    simp
  rw [hv_sq, hquad, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rcases hμGap i with hzero | hbound
  · have hcoeff : (b.repr v) i = 0 := by
      rw [b.repr_apply_apply]
      exact Submodule.inner_right_of_mem_orthogonal
        (by
          rw [LinearMap.mem_ker, hP.isSymmetric.apply_eigenvectorBasis rfl]
          change (μ i : ℂ) • b i = 0
          simp [hzero]) hv
    simp [hcoeff]
  · exact mul_le_mul_of_nonneg_right hbound (sq_nonneg _)

/-- An operator \(Q\) inherits the norm gap of a positive operator \(P\)
when \(P \leq Q\) in Loewner order and their kernels agree. -/
theorem norm_gap_of_le_of_ker_eq {P Q : E →ₗ[ℂ] E}
    (hP : P.IsPositive) {γ : ℝ} (hγ : 0 ≤ γ)
    (hPQ : P ≤ Q) (hker : LinearMap.ker P = LinearMap.ker Q)
    (hGap : ∀ v ∈ (LinearMap.ker P)ᗮ, γ * ‖v‖ ≤ ‖P v‖) :
    ∀ v ∈ (LinearMap.ker Q)ᗮ, γ * ‖v‖ ≤ ‖Q v‖ := by
  intro v hv
  have hvP : v ∈ (LinearMap.ker P)ᗮ := by simpa [hker] using hv
  have henergyP := hP.re_inner_ge_of_norm_gap hγ hGap v hvP
  have henergyPQ : (⟪P v, v⟫_ℂ).re ≤ (⟪Q v, v⟫_ℂ).re := by
    have hnonneg := hPQ.re_inner_nonneg_left v
    simpa [sub_apply, inner_sub_left] using hnonneg
  have hinnerNorm : (⟪Q v, v⟫_ℂ).re ≤ ‖Q v‖ * ‖v‖ :=
    @re_inner_le_norm ℂ E _ _ _ (Q v) v
  by_cases hv0 : v = 0
  · simp [hv0]
  · have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
    have hmul : γ * ‖v‖ * ‖v‖ ≤ ‖Q v‖ * ‖v‖ := by
      calc
        γ * ‖v‖ * ‖v‖ = γ * ‖v‖ ^ 2 := by ring
        _ ≤ (⟪P v, v⟫_ℂ).re := henergyP
        _ ≤ (⟪Q v, v⟫_ℂ).re := henergyPQ
        _ ≤ ‖Q v‖ * ‖v‖ := hinnerNorm
    exact le_of_mul_le_mul_right hmul hvpos

end LinearMap.IsPositive
