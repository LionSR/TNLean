/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.GaussianFilter.MatrixIntegral
import QICLean.Analysis.GroundProjection
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

/-!
# Gaussian filtering with an approximate ground energy

A Gaussian filter centered at an energy estimate need not fix the ground vector. Its
ground amplitude is retained explicitly. An estimate within half the spectral gap gives
dimension-independent suppression of the orthogonal complement, while a separate
variance-weighted energy accuracy bound keeps the ground amplitude at least `exp (-1/2)`.

These are spectral ingredients of Huang, arXiv:1406.6355v6, Section 5.4, equation (19)
and Lemma 18. They do not construct the energy grid, finite matrix product approximation,
or normalized viable witness. No hypothesis on the total ground energy is imposed.

The statements use only Mathlib and QICLean mathematics. Like the generic quadrature
modules, they belong upstream in QICLean's Gaussian-filter development; their present
location keeps this contribution separate without changing the companion dependency.
-/

open Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator ComplexOrder NNReal

namespace TNLean.MPS.AreaLaw

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem cfc_basis_action {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (f : ℝ → ℝ) (k : n) :
    toEuclideanLin (cfc f H) (hH.eigenvectorBasis k) =
      (f (hH.eigenvalues k) : ℂ) • hH.eigenvectorBasis k := by
  apply WithLp.ofLp_injective 2
  change cfc f H *ᵥ WithLp.ofLp (hH.eigenvectorBasis k) = _
  rw [hH.cfc_eq, hH.cfc_form]
  rw [← mulVec_mulVec, hH.star_eigenvectorUnitary_mulVec, ← mulVec_mulVec,
    diagonal_mulVec_single, mul_one, mulVec_single]
  simp

/-- The Gaussian integral centered at a real energy estimate is the corresponding
continuous functional calculus of the original Hamiltonian. Source: Huang,
arXiv:1406.6355v6, Section 5.4, equation (19). -/
theorem gaussianIntertwiner_shift_eq_cfc (h : ℝ≥0) {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (E : ℝ) :
    GaussianFilter.gaussianIntertwiner h (H - (E : ℂ) • 1) 0 1 =
      cfc (fun x : ℝ ↦ Real.exp (-(h : ℝ) * (x - E) ^ 2 / 2)) H := by
  have hshift : GaussianFilter.gaussianIntertwiner h (H - (E : ℂ) • 1) 0 1 =
      GaussianFilter.gaussianIntertwiner h H ((E : ℂ) • 1) 1 := by
    simpa only [Complex.ofReal_neg, neg_smul, add_neg_cancel, sub_eq_add_neg] using
      GaussianFilter.gaussianIntertwiner_add_smul_one h H ((E : ℂ) • 1) 1 (-E)
  rw [hshift]
  have hE : ((E : ℂ) • (1 : Matrix n n ℂ)).IsHermitian :=
    isHermitian_one.smul (by simp [IsSelfAdjoint, Complex.conj_ofReal])
  apply toEuclideanLin.injective
  apply hH.eigenvectorBasis.toBasis.ext
  intro j
  apply InnerProductSpace.ext_inner_left_basis hH.eigenvectorBasis.toBasis
  intro k
  change ⟪hH.eigenvectorBasis k, toEuclideanLin
      (GaussianFilter.gaussianIntertwiner h H ((E : ℂ) • 1) 1) (hH.eigenvectorBasis j)⟫_ℂ =
    ⟪hH.eigenvectorBasis k, toEuclideanLin
      (cfc (fun x : ℝ ↦ Real.exp (-(h : ℝ) * (x - E) ^ 2 / 2)) H)
        (hH.eigenvectorBasis j)⟫_ℂ
  rw [GaussianFilter.inner_gaussianIntertwiner h hH hE 1
    (SpectralFilter.mulVec_eigenvectorBasis_complex hH k)
    (E' := E) (by simp only [Matrix.smul_mulVec, Matrix.one_mulVec]),
    cfc_basis_action, inner_smul_right]
  simp only [toLpLin_one, LinearMap.id_apply]
  have hexp : Complex.exp (-(h : ℂ) * ((hH.eigenvalues k - E : ℝ) : ℂ) ^ 2 / 2) =
      (Real.exp (-(h : ℝ) * (hH.eigenvalues k - E) ^ 2 / 2) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hexp]
  by_cases hkj : k = j
  · subst k
    rfl
  · rw [hH.eigenvectorBasis.orthonormal.inner_eq_zero hkj]
    simp

/-- Gaussian suppression with an approximate energy estimate. The surviving ground
amplitude is explicit; the orthogonal error is at most `exp (-h Δ²/8)` when the estimate
is within half the gap. This is a spectral supporting estimate for Huang,
arXiv:1406.6355v6, Section 5.4, Lemma 18, rather than its normalized energy conclusion. -/
theorem norm_gaussianIntertwiner_shift_sub_rankOne_le (h : ℝ≥0)
    {H : Matrix n n ℂ} (hH : H.IsHermitian) {E₀ Δ E : ℝ}
    {Γ : EuclideanSpace ℂ n} (hΓ : ‖Γ‖ = 1)
    (hHΓ : H *ᵥ WithLp.ofLp Γ = (E₀ : ℂ) • WithLp.ofLp Γ)
    (hgap : (H - (E₀ : ℂ) • 1 - (Δ : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ)))).PosSemidef)
    (hΔ : 0 < Δ) (hE : |E - E₀| ≤ Δ / 2) :
    ‖GaussianFilter.gaussianIntertwiner h (H - (E : ℂ) • 1) 0 1 -
        Real.exp (-(h : ℝ) * (E₀ - E) ^ 2 / 2) •
          vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ))‖ ≤
      Real.exp (-(h : ℝ) * Δ ^ 2 / 8) := by
  let f : ℝ → ℝ := fun x ↦ Real.exp (-(h : ℝ) * (x - E) ^ 2 / 2)
  let g : ℝ → ℝ := fun x ↦ 1 - if E₀ + Δ ≤ x then 1 else 0
  let z : ℝ := Real.exp (-(h : ℝ) * (E₀ - E) ^ 2 / 2)
  have hcont (φ : ℝ → ℝ) : ContinuousOn φ (spectrum ℝ H) :=
    H.finite_real_spectrum.continuousOn φ
  have hPg : cfc g H = vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ)) := by
    calc
      cfc g H = cfc (fun _ : ℝ ↦ 1) H -
          cfc (fun x : ℝ ↦ if E₀ + Δ ≤ x then 1 else 0) H :=
        _root_.cfc_sub _ _ H (hcont _) (hcont _)
      _ = _ := by
        rw [_root_.cfc_const 1 H hH.isSelfAdjoint]
        simpa only [map_one, Matrix.spectralProjectionGE] using
          hH.complement_spectralProjectionGE_eq_rankOne hΓ hHΓ hgap hΔ
  have hscaled : cfc (fun x ↦ z * g x) H =
      z • vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ)) := by
    rw [_root_.cfc_const_mul z g H (hcont _), hPg]
  rw [gaussianIntertwiner_shift_eq_cfc h hH E]
  change ‖cfc f H - z • vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ))‖ ≤ _
  rw [← hscaled, ← _root_.cfc_sub _ _ H (hcont _) (hcont _)]
  apply norm_cfc_le (Real.exp_pos _).le
  intro x hx
  obtain ⟨k, rfl⟩ := hH.spectrum_real_eq_range_eigenvalues ▸ hx
  rcases GaussianFilter.eigenvector_ground_or_gap hH hΓ hHΓ hgap hΔ k with
    ⟨hground, -⟩ | ⟨henergy, -⟩
  · simp only [hground, f, g, z, show ¬ E₀ + Δ ≤ E₀ by linarith,
      ite_false, sub_zero, mul_one, sub_self, norm_zero]
    exact (Real.exp_pos _).le
  · have hthreshold : E₀ + Δ ≤ hH.eigenvalues k := by linarith
    have hdist : Δ / 2 ≤ hH.eigenvalues k - E := by
      have := (le_abs_self (E - E₀)).trans hE
      linarith
    have hsq : (Δ / 2) ^ 2 ≤ (hH.eigenvalues k - E) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hdist 2
    have hmul := mul_le_mul_of_nonneg_left hsq h.property
    simp only [f, g, hthreshold, ite_true, sub_self, mul_zero, sub_zero,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ -(h : ℝ) * (Δ / 2) ^ 2 / 2 := by
        convert! div_le_div_of_nonneg_right (neg_le_neg hmul)
          (by norm_num : 0 ≤ (2 : ℝ)) using 1 <;> ring!
      _ = _ := by ring

/-- A variance-weighted energy error at most one retains ground amplitude between
`exp (-1/2)` and one. Source: Huang, arXiv:1406.6355v6, Section 5.4, equation (19)
and Lemma 18. -/
theorem gaussian_ground_amplitude_bounds (h : ℝ≥0) {E₀ E : ℝ}
    (hE : (h : ℝ) * (E₀ - E) ^ 2 ≤ 1) :
    Real.exp (-(1 : ℝ) / 2) ≤ Real.exp (-(h : ℝ) * (E₀ - E) ^ 2 / 2) ∧
      Real.exp (-(h : ℝ) * (E₀ - E) ^ 2 / 2) ≤ 1 := by
  constructor
  · apply Real.exp_le_exp.mpr
    linarith
  · apply Real.exp_le_one_iff.mpr
    have hnonneg : 0 ≤ (h : ℝ) * (E₀ - E) ^ 2 := by positivity
    linarith

end TNLean.MPS.AreaLaw
