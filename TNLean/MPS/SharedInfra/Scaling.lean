/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.Reduction
import TNLean.MPS.Periodic.Defs

/-!
# Shared scaling lemmas for MPS tensors

This module collects the tensor-scaling identities that are used both by the
canonical-form construction and by transfer-normalization arguments.
-/

open scoped Matrix ComplexOrder BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- Scaling an MPS tensor by `c` scales the transfer map by `c * star c`. -/
theorem transferMap_smul (c : ℂ) (A : MPSTensor d D) (X : Matrix (Fin D) (Fin D) ℂ) :
    transferMap (fun i => c • A i) X = (c * starRingEnd ℂ c) • transferMap A X := by
  simp only [transferMap_apply, Matrix.conjTranspose_smul]
  simp_rw [smul_mul_assoc, mul_smul_comm, smul_smul, ← Finset.smul_sum]
  rfl

/-- Unit-norm scaling preserves left-canonical normalization. -/
theorem leftCanonical_smul_of_norm_one (c : ℂ) (hc : ‖c‖ = 1)
    (A : MPSTensor d D) (hA : ∑ i : Fin d, (A i)ᴴ * (A i) = 1) :
    ∑ i : Fin d, (c • A i)ᴴ * (c • A i) = 1 := by
  simp only [Matrix.conjTranspose_smul]
  simp_rw [smul_mul_smul_comm]
  rw [← Finset.smul_sum, hA]
  have hsc : (star c : ℂ) * c = 1 := by
    simpa [Complex.normSq_eq_norm_sq, hc] using
      (Complex.normSq_eq_conj_mul_self (z := c)).symm
  rw [hsc, one_smul]

/-- If both `A` and its scalar multiple are left-canonical, then the scalar has
unit norm.

This is the scalar normalization used in arXiv:1708.00029, Appendix A,
lines 1082--1084: once sectorwise proportionality has been extracted, the
left-canonical equations force the proportionality scalar to be a phase. -/
theorem norm_eq_one_of_leftCanonical_smul [NeZero D] (c : ℂ) (A : MPSTensor d D)
    (hA : IsLeftCanonical A) (hcA : IsLeftCanonical (fun i => c • A i)) :
    ‖c‖ = 1 := by
  unfold IsLeftCanonical at hA hcA
  have hscaled : (star c * c) • (1 : Matrix (Fin D) (Fin D) ℂ) = 1 := by
    calc
      (star c * c) • (1 : Matrix (Fin D) (Fin D) ℂ)
          = (star c * c) • ∑ i : Fin d, (A i)ᴴ * A i := by rw [hA]
      _ = ∑ i : Fin d, (c • A i)ᴴ * (c • A i) := by
        simp only [Matrix.conjTranspose_smul]
        simp_rw [smul_mul_smul_comm]
        rw [← Finset.smul_sum]
      _ = 1 := hcA
  have hentry :=
    congrArg (fun M : Matrix (Fin D) (Fin D) ℂ => M 0 0) hscaled
  have hstar_mul : star c * c = 1 := by
    simpa [Matrix.smul_apply] using hentry
  have hnormSq : star c * c = (↑(‖c‖ ^ 2) : ℂ) := by
    simpa [Complex.normSq_eq_norm_sq] using
      (Complex.normSq_eq_conj_mul_self (z := c)).symm
  have hsq_complex : ((‖c‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← hnormSq, hstar_mul]
  have hsq_real : ‖c‖ ^ 2 = 1 := by
    exact Complex.ofReal_injective hsq_complex
  nlinarith [norm_nonneg c]

/-- Appendix-A scalar normalization in the form used after product-one phase
extraction.

If \(A^i=(\kappa\xi)B^i\), both tensor families are left-canonical, and
\(\xi\) already has unit norm, then \(\kappa\) has unit norm.  This isolates
the normalization step in arXiv:1708.00029, Appendix A, lines 1082--1084, after
the \(\Omega_u\)-contraction and scalar extraction have produced the sector
relation. -/
theorem kappa_norm_eq_one_of_leftCanonical_smul [NeZero D]
    {κ ξ : ℂ} (hξ : ‖ξ‖ = 1) (A B : MPSTensor d D)
    (hA : IsLeftCanonical A) (hB : IsLeftCanonical B)
    (hAB : ∀ i : Fin d, A i = (κ * ξ) • B i) :
    ‖κ‖ = 1 := by
  have hscaled : IsLeftCanonical (fun i : Fin d => (κ * ξ) • B i) := by
    unfold IsLeftCanonical at hA ⊢
    simpa [hAB] using hA
  have hκξ : ‖κ * ξ‖ = 1 :=
    norm_eq_one_of_leftCanonical_smul (κ * ξ) B hB hscaled
  simpa [norm_mul, hξ] using hκξ

/-- Unit-norm scaling preserves periodicity data. -/
theorem isPeriodic_smul_of_norm_one
    {m : ℕ} {c : ℂ} (hc : ‖c‖ = 1)
    (A : MPSTensor d D) (hA : IsPeriodic m A) :
    IsPeriodic m (fun i => c • A i) := by
  have hc_ne : c ≠ 0 := by
    intro hc0
    have hc' := hc
    simp [hc0] at hc'
  have hTransfer : transferMap (fun i => c • A i) = transferMap A := by
    ext X : 1
    rw [transferMap_smul]
    have hsc : c * starRingEnd ℂ c = 1 := by
      simpa [Complex.normSq_eq_norm_sq, hc] using Complex.mul_conj c
    simp [hsc]
  refine ⟨isIrreducibleTensor_smul hc_ne A hA.irreducible,
    leftCanonical_smul_of_norm_one c hc A hA.leftCanonical,
    hA.period_pos, ?_, hA.primitiveRoot⟩
  simpa [hTransfer] using hA.peripheral_eq

/-- Scaling a tensor by `c` scales MPVs by `c^N`. -/
theorem mpv_smul (c : ℂ) (A : MPSTensor d D) {N : ℕ} (σ : Fin N → Fin d) :
    mpv (fun i => c • A i) σ = c ^ N * mpv A σ := by
  simp only [mpv, coeff]
  rw [evalWord_smul]
  simp [List.length_ofFn, Matrix.trace_smul]

/-- The phase `μ / ‖μ‖` of a nonzero scalar has unit norm. -/
theorem phase_norm_one {μ : ℂ} (hμ : μ ≠ 0) :
    ‖μ / ↑‖μ‖‖ = 1 := by
  rw [norm_div, Complex.norm_real, norm_norm]
  exact div_self (norm_ne_zero_iff.mpr hμ)

/-- Multiplying every block weight by the same scalar multiplies length-`N`
MPV coefficients by `c ^ N`. -/
theorem mpv_toTensorFromBlocks_weight_mul_left {r : ℕ} {dim : Fin r → ℕ}
    (c : ℂ) (μ : Fin r → ℂ)
    (A : (k : Fin r) → MPSTensor d (dim k))
    {N : ℕ} (σ : Fin N → Fin d) :
    mpv (toTensorFromBlocks (d := d) (μ := fun k => c * μ k) A) σ =
      c ^ N * mpv (toTensorFromBlocks (d := d) (μ := μ) A) σ := by
  rw [mpv_toTensorFromBlocks_eq_sum, mpv_toTensorFromBlocks_eq_sum]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [mul_pow, smul_eq_mul, mul_assoc]

end MPSTensor
