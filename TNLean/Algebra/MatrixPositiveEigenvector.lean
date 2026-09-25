/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
# Spectral radius from a positive left eigenvector

A nonnegative real matrix `M` with a positive left eigenvector `δ ᵥ* M = r • δ` has spectral
radius `r` over `ℂ`. The argument pairs `δ` with the entrywise moduli of an arbitrary complex
eigenvector, so it uses neither irreducibility of `M` nor the existence part of the
Perron–Frobenius theorem. The file also records that transposition preserves the spectrum of a
square matrix over a commutative ring.

## Main results

* `Matrix.norm_le_of_mem_spectrum_of_pos_vecMul_eq`: every complex eigenvalue has modulus at
  most `r`.
* `Matrix.ofReal_mem_spectrum_of_pos_vecMul_eq`: `r` is a complex eigenvalue.
* `Matrix.spectralRadius_map_ofReal_eq_of_pos_vecMul_eq`: the spectral radius equals `r`.
* `Matrix.spectrum_transpose`: `spectrum R Aᵀ = spectrum R A`.
-/

open scoped Matrix ENNReal NNReal

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every complex eigenvalue `μ` of a nonnegative real matrix `M` with a positive left
eigenvector `δ ᵥ* M = r • δ` satisfies `‖μ‖ ≤ r`: pairing `δ` with the entrywise moduli of an
eigenvector `v` gives `‖μ‖ ∑ δ_i ‖v_i‖ ≤ ∑_{i,j} δ_i M_{ij} ‖v_j‖ = r ∑ δ_j ‖v_j‖`. -/
theorem norm_le_of_mem_spectrum_of_pos_vecMul_eq {M : Matrix ι ι ℝ} (hM : ∀ i j, 0 ≤ M i j)
    {δ : ι → ℝ} (hδ : ∀ i, 0 < δ i) {r : ℝ} (h : δ ᵥ* M = r • δ) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (M.map ((↑) : ℝ → ℂ))) : ‖μ‖ ≤ r := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at hμ
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hμ
  have hev : ∀ i, ∑ j, (M i j : ℂ) * v j = μ * v i := by
    intro i
    have := congrFun hv i
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      sub_eq_zero] at this
    simpa [Matrix.mulVec, dotProduct] using this.symm
  -- entrywise bound `‖μ‖ ‖v_i‖ ≤ ∑_j M_{ij} ‖v_j‖`
  have hrow : ∀ i, ‖μ‖ * ‖v i‖ ≤ ∑ j, M i j * ‖v j‖ := by
    intro i
    calc ‖μ‖ * ‖v i‖ = ‖∑ j, (M i j : ℂ) * v j‖ := by rw [hev i, norm_mul]
      _ ≤ ∑ j, ‖(M i j : ℂ) * v j‖ := norm_sum_le _ _
      _ = ∑ j, M i j * ‖v j‖ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hM i j)]
  have hcol : ∀ j, ∑ i, δ i * M i j = r * δ j := by
    intro j
    simpa [Matrix.vecMul, dotProduct] using congrFun h j
  set S := ∑ i, δ i * ‖v i‖ with hS
  have hSpos : 0 < S := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hv0
    exact Finset.sum_pos' (fun j _ => mul_nonneg (hδ j).le (norm_nonneg _))
      ⟨i, Finset.mem_univ _, mul_pos (hδ i) (norm_pos_iff.2 hi)⟩
  have hbound : ‖μ‖ * S ≤ r * S := by
    calc ‖μ‖ * S = ∑ i, δ i * (‖μ‖ * ‖v i‖) := by
          rw [hS, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ∑ i, δ i * ∑ j, M i j * ‖v j‖ :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hrow i) (hδ i).le
      _ = ∑ j, (∑ i, δ i * M i j) * ‖v j‖ := by
          simp_rw [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
      _ = r * S := by
          simp_rw [hcol, hS, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
  exact le_of_mul_le_mul_right hbound hSpos

/-- A positive left eigenvector `δ ᵥ* M = r • δ` of a real matrix makes `r` an eigenvalue of `M`
over `ℂ`. -/
theorem ofReal_mem_spectrum_of_pos_vecMul_eq [Nonempty ι] {M : Matrix ι ι ℝ} {δ : ι → ℝ}
    (hδ : ∀ i, 0 < δ i) {r : ℝ} (h : δ ᵥ* M = r • δ) :
    (r : ℂ) ∈ spectrum ℂ (M.map ((↑) : ℝ → ℂ)) := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not]
  refine Matrix.exists_vecMul_eq_zero_iff.1 ⟨fun i => (δ i : ℂ), ?_, ?_⟩
  · intro h0
    obtain ⟨i⟩ := ‹Nonempty ι›
    have := congrFun h0 i
    simp only [Pi.zero_apply, Complex.ofReal_eq_zero] at this
    exact (hδ i).ne' this
  · ext j
    have hj := congrFun h j
    simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul] at hj
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.vecMul_sub, Matrix.vecMul_smul,
      Matrix.vecMul_one, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_eq_zero]
    simp only [Matrix.vecMul, dotProduct, Matrix.map_apply]
    exact_mod_cast hj.symm

/-- **Spectral radius from a positive left eigenvector.** A nonnegative real matrix `M` with a
positive left eigenvector `δ ᵥ* M = r • δ` has spectral radius `r` over `ℂ`. -/
theorem spectralRadius_map_ofReal_eq_of_pos_vecMul_eq [Nonempty ι] {M : Matrix ι ι ℝ}
    (hM : ∀ i j, 0 ≤ M i j) {δ : ι → ℝ} (hδ : ∀ i, 0 < δ i) {r : ℝ} (h : δ ᵥ* M = r • δ) :
    spectralRadius ℂ (M.map ((↑) : ℝ → ℂ)) = ENNReal.ofReal r := by
  have hr := ofReal_mem_spectrum_of_pos_vecMul_eq hδ h
  have hr0 : 0 ≤ r := by
    have := norm_le_of_mem_spectrum_of_pos_vecMul_eq hM hδ h hr
    rw [Complex.norm_real, Real.norm_eq_abs] at this
    exact (abs_nonneg r).trans this
  refine le_antisymm (iSup₂_le fun μ hμ => ?_) (le_iSup₂_of_le (r : ℂ) hr ?_)
  · rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
    exact ENNReal.ofReal_le_ofReal (norm_le_of_mem_spectrum_of_pos_vecMul_eq hM hδ h hμ)
  · rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, Complex.norm_real, Real.norm_of_nonneg hr0]

/-- The spectrum of a square matrix over a commutative ring is that of its transpose. -/
theorem spectrum_transpose {R : Type*} [CommRing R] (A : Matrix ι ι R) :
    spectrum R Aᵀ = spectrum R A := by
  ext μ
  rw [Matrix.mem_spectrum_iff_not_isUnit_eval_charpoly,
    Matrix.mem_spectrum_iff_not_isUnit_eval_charpoly, Matrix.charpoly_transpose]

end Matrix
