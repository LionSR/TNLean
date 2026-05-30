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
    rw [← starRingEnd_apply, Complex.conj_mul', hc]; simp
  rw [hsc, one_smul]

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
      rw [Complex.mul_conj', hc]; simp
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
