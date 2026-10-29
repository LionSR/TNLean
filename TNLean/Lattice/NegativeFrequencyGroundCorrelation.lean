/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.GaussianFilteredTerm

/-!
# Negative frequencies and actual ground-state correlations

The sharp negative-frequency part retains exactly the matrix elements that
lower energy. It annihilates every actual ground vector. Its ground-state
commutator with a second observable is exactly the correlation with the
full ground-space projection removed.

This is the finite spectral separation in Hastings–Koma,
arXiv:math-ph/0507008, Section 3, equations (3.1)–(3.6), before the
Gaussian regularization in Lemma 3.1. No clustering, locality or correlation
bound is supplied. The sharp spectral part is not claimed to be local;
quantitative regularization and the time-integral bound remain necessary.
-/

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace TNLean.Lattice

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Retain exactly the energy-lowering matrix elements of an observable in
an orthonormal eigenbasis of the actual Hermitian Hamiltonian. The rank-one
operators are Mathlib's canonical operators. Source: Hastings–Koma,
arXiv:math-ph/0507008, equations (3.1)–(3.6). -/
def negativeFrequencyPart {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (A : Matrix n n ℂ) : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := by
  classical
  let b := hH.eigenvectorBasis
  exact ∑ i, ∑ j, if hH.eigenvalues i < hH.eigenvalues j then
    ⟪b i, toEuclideanCLM (n := n) (𝕜 := ℂ) A (b j)⟫_ℂ •
      InnerProductSpace.rankOne ℂ (b i) (b j) else 0

omit [DecidableEq n] in
private theorem inner_apply_eq_double_sum
    (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n))
    (T : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (ψ x : EuclideanSpace ℂ n) :
    ⟪ψ, T x⟫_ℂ = ∑ i, ∑ j,
      ⟪b j, x⟫_ℂ * ⟪b i, T (b j)⟫_ℂ * ⟪ψ, b i⟫_ℂ := by
  have hexpand (y : EuclideanSpace ℂ n) :
      ⟪ψ, y⟫_ℂ = ∑ i, ⟪b i, y⟫_ℂ * ⟪ψ, b i⟫_ℂ := by
    conv_lhs => rw [← b.sum_repr' y]
    simp only [inner_sum, inner_smul_right]
  calc
    ⟪ψ, T x⟫_ℂ = ∑ j, ⟪b j, x⟫_ℂ * ⟪ψ, T (b j)⟫_ℂ := by
      conv_lhs => rw [← b.sum_repr' x]
      simp only [map_sum, map_smul, inner_sum, inner_smul_right]
    _ = ∑ j, ∑ i, ⟪b j, x⟫_ℂ * ⟪b i, T (b j)⟫_ℂ * ⟪ψ, b i⟫_ℂ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hexpand (T (b j)), Finset.mul_sum]
      simp only [mul_assoc]
    _ = _ := Finset.sum_comm

/-- The actual negative-frequency part annihilates a ground vector. Only
that its energy is a least eigenvalue is needed, not a supplied filtering
or ground-orthogonality premise. Source: Hastings–Koma,
arXiv:math-ph/0507008, equations (3.2)–(3.5). -/
theorem negativeFrequencyPart_apply_ground_eq_zero {H : Matrix n n ℂ}
    (hH : H.IsHermitian) {E₀ : ℝ} (hmin : ∀ i, E₀ ≤ hH.eigenvalues i)
    (A : Matrix n n ℂ) {ψ : EuclideanSpace ℂ n}
    (hψ : ψ ∈ groundEigenspace H E₀) : negativeFrequencyPart hH A ψ = 0 := by
  classical
  unfold negativeFrequencyPart
  dsimp only
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  by_cases hij : hH.eigenvalues i < hH.eigenvalues j
  · have hj : hH.eigenvalues j ≠ E₀ := by linarith [hmin i]
    have hzero := inner_eq_zero_of_mem_groundEigenspace hH hj
      (SpectralFilter.mulVec_eigenvectorBasis_complex hH j) hψ
    simp only [if_pos hij, ContinuousLinearMap.smul_apply,
      InnerProductSpace.rankOne_apply, hzero, zero_smul, smul_zero]
  · simp only [if_neg hij, ContinuousLinearMap.zero_apply]

private theorem inner_ground_negativeFrequencyPart_apply
    {H : Matrix n n ℂ} (hH : H.IsHermitian) {E₀ : ℝ}
    (hmin : ∀ i, E₀ ≤ hH.eigenvalues i) (A : Matrix n n ℂ)
    {ψ x : EuclideanSpace ℂ n} (hψ : ψ ∈ groundEigenspace H E₀)
    (hx : x ∈ (groundEigenspace H E₀)ᗮ) :
    ⟪ψ, negativeFrequencyPart hH A x⟫_ℂ =
      ⟪ψ, toEuclideanCLM (n := n) (𝕜 := ℂ) A x⟫_ℂ := by
  classical
  let b := hH.eigenvectorBasis
  rw [inner_apply_eq_double_sum b (toEuclideanCLM (n := n) (𝕜 := ℂ) A) ψ x]
  unfold negativeFrequencyPart
  dsimp only
  simp only [ContinuousLinearMap.sum_apply, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : hH.eigenvalues i < hH.eigenvalues j
  · simp only [if_pos hij, ContinuousLinearMap.smul_apply,
      InnerProductSpace.rankOne_apply, inner_smul_right]
    ring
  · have hvanish :
        ⟪b j, x⟫_ℂ * ⟪b i, toEuclideanCLM (n := n) (𝕜 := ℂ) A (b j)⟫_ℂ *
          ⟪ψ, b i⟫_ℂ = 0 := by
      by_cases hi : hH.eigenvalues i = E₀
      · have hj : hH.eigenvalues j = E₀ := by
          have hge := hmin j
          rw [hi] at hij
          linarith
        have hmem : b j ∈ groundEigenspace H E₀ :=
          mem_groundEigenspace_iff.mpr (by
            simpa only [hj] using SpectralFilter.mulVec_eigenvectorBasis_complex hH j)
        have hz := ((groundEigenspace H E₀).mem_orthogonal x).mp hx (b j) hmem
        simp only [hz, zero_mul]
      · have hz : ⟪ψ, b i⟫_ℂ = 0 := inner_eq_zero_symm.mpr
          (inner_eq_zero_of_mem_groundEigenspace hH hi
            (SpectralFilter.mulVec_eigenvectorBasis_complex hH i) hψ)
        simp only [hz, mul_zero]
    simpa only [if_neg hij, ContinuousLinearMap.zero_apply, inner_zero_right] using hvanish.symm

/-- Ground-space-subtracted correlation is exactly a commutator involving
the actual negative-frequency part. This supplies the spectral separation
needed before estimating that commutator by a regularized time integral.
No locality or correlation-decay condition is assumed. The entire ground
space is removed, so degeneracy is allowed. Source: Hastings–Koma,
arXiv:math-ph/0507008, equations (3.1)–(3.6). -/
theorem inner_ground_projected_eq_negativeFrequency_commutator
    {H : Matrix n n ℂ} (hH : H.IsHermitian) {E₀ : ℝ}
    (hmin : ∀ i, E₀ ≤ hH.eigenvalues i) (A B : Matrix n n ℂ)
    {ψ : EuclideanSpace ℂ n} (hψ : ψ ∈ groundEigenspace H E₀) :
    ⟪ψ, toEuclideanCLM (n := n) (𝕜 := ℂ) A
      (toEuclideanCLM (n := n) (𝕜 := ℂ) B ψ -
        (groundEigenspace H E₀).starProjection
          (toEuclideanCLM (n := n) (𝕜 := ℂ) B ψ))⟫_ℂ =
      ⟪ψ, ((negativeFrequencyPart hH A).comp (toEuclideanCLM (n := n) (𝕜 := ℂ) B) -
        (toEuclideanCLM (n := n) (𝕜 := ℂ) B).comp (negativeFrequencyPart hH A)) ψ⟫_ℂ := by
  let K := groundEigenspace H E₀
  let y := toEuclideanCLM (n := n) (𝕜 := ℂ) B ψ
  have hsplit := inner_ground_negativeFrequencyPart_apply hH hmin A hψ
    (K.sub_starProjection_mem_orthogonal y)
  have hkill := negativeFrequencyPart_apply_ground_eq_zero hH hmin A hψ
  have hkillProjection := negativeFrequencyPart_apply_ground_eq_zero hH hmin A
    (K.starProjection_apply_mem y)
  rw [map_sub, hkillProjection, sub_zero] at hsplit
  simpa only [sub_apply, ContinuousLinearMap.comp_apply,
    hkill, map_zero, sub_zero] using hsplit.symm

/-- At a one-dimensional ground space, the sharp-frequency commutator is
exactly the ordinary connected correlation of the unnormalized ground
vector. The squared norm in the denominator keeps normalization explicit;
no continuous choice of a normalized vector is needed.
Source: Hastings–Koma, arXiv:math-ph/0507008, equations (3.1)–(3.6),
specialized to an exactly one-dimensional ground eigenspace. -/
theorem inner_ground_connected_eq_negativeFrequency_commutator
    {H : Matrix n n ℂ} (hH : H.IsHermitian) {E₀ : ℝ}
    (hmin : ∀ i, E₀ ≤ hH.eigenvalues i) (A B : Matrix n n ℂ)
    {ψ : EuclideanSpace ℂ n} (hψ : ψ ∈ groundEigenspace H E₀)
    (hline : groundEigenspace H E₀ = Submodule.span ℂ {ψ}) :
    ⟪ψ, toEuclideanCLM (n := n) (𝕜 := ℂ) A
        (toEuclideanCLM (n := n) (𝕜 := ℂ) B ψ)⟫_ℂ -
        ⟪ψ, toEuclideanCLM (n := n) (𝕜 := ℂ) A ψ⟫_ℂ *
          ⟪ψ, toEuclideanCLM (n := n) (𝕜 := ℂ) B ψ⟫_ℂ /
            ((‖ψ‖ ^ 2 : ℝ) : ℂ) =
      ⟪ψ, ((negativeFrequencyPart hH A).comp (toEuclideanCLM (n := n) (𝕜 := ℂ) B) -
        (toEuclideanCLM (n := n) (𝕜 := ℂ) B).comp (negativeFrequencyPart hH A)) ψ⟫_ℂ := by
  calc
    _ = ⟪ψ, toEuclideanCLM (n := n) (𝕜 := ℂ) A
        (toEuclideanCLM (n := n) (𝕜 := ℂ) B ψ -
          (groundEigenspace H E₀).starProjection
            (toEuclideanCLM (n := n) (𝕜 := ℂ) B ψ))⟫_ℂ := by
      rw [hline, Submodule.starProjection_singleton (𝕜 := ℂ)]
      simp only [map_sub, map_smul, inner_sub_right, inner_smul_right, div_eq_mul_inv]
      congr 1
      ac_rfl
    _ = _ := inner_ground_projected_eq_negativeFrequency_commutator hH hmin A B hψ

end TNLean.Lattice
