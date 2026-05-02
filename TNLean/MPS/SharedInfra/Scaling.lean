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
    change starRingEnd ℂ c * c = 1
    have h1 : starRingEnd ℂ c * c = ↑(Complex.normSq c) := by
      rw [mul_comm, Complex.mul_conj]
    rw [h1, Complex.normSq_eq_norm_sq, hc, one_pow, Complex.ofReal_one]
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
      have h1 : c * starRingEnd ℂ c = ↑(Complex.normSq c) := by
        rw [Complex.mul_conj]
      rw [h1, Complex.normSq_eq_norm_sq, hc, one_pow, Complex.ofReal_one]
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

/-- Nonzero scalar rescaling preserves injectivity. -/
theorem isInjective_smul (c : ℂ) (hc : c ≠ 0) (A : MPSTensor d D) (hA : IsInjective A) :
    IsInjective (fun i => c • A i) := by
  unfold IsInjective at hA ⊢
  have hrange : Set.range (fun i => c • A i) = (c • ·) '' Set.range A := by
    ext M
    simp only [Set.mem_range, Set.mem_image]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨A i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨N, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  rw [hrange]
  rw [show (c • · : Matrix (Fin D) (Fin D) ℂ → Matrix (Fin D) (Fin D) ℂ) =
      (c • LinearMap.id : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) from by
    ext M
    simp]
  rw [Submodule.span_image, hA, Submodule.map_smul _ _ c hc, Submodule.map_id]

/-- The phase `μ / ‖μ‖` of a nonzero scalar has unit norm. -/
theorem phase_norm_one {μ : ℂ} (hμ : μ ≠ 0) :
    ‖μ / ↑‖μ‖‖ = 1 := by
  rw [norm_div, Complex.norm_real, norm_norm]
  exact div_self (norm_ne_zero_iff.mpr hμ)

/-- Split `μ • M` into a modulus part and a phase part. -/
theorem smul_eq_norm_smul_phase (μ : ℂ) (hμ : μ ≠ 0) (M : Matrix (Fin D) (Fin D) ℂ) :
    μ • M = (↑‖μ‖ : ℂ) • ((μ / ↑‖μ‖) • M) := by
  rw [smul_smul]
  congr 1
  rw [mul_comm, div_mul_cancel₀]
  exact_mod_cast norm_ne_zero_iff.mpr hμ

/-- Scaling by the modulus `‖μ‖` scales the transfer map by `‖μ‖²`. -/
theorem transferMap_norm_smul (μ : ℂ) {D' : ℕ} (A : MPSTensor d D')
    (X : Matrix (Fin D') (Fin D') ℂ) :
    transferMap (fun i => (↑‖μ‖ : ℂ) • A i) X =
      (↑(‖μ‖ ^ 2) : ℂ) • transferMap A X := by
  rw [transferMap_smul]
  congr 1
  rw [Complex.conj_ofReal, ← Complex.ofReal_mul, sq]

/-- Phase scaling preserves left-canonical normalization. -/
theorem leftCanonical_phase_smul {D' : ℕ} (μ : ℂ) (hμ : μ ≠ 0)
    (A : MPSTensor d D') (hA : ∑ i : Fin d, (A i)ᴴ * (A i) = 1) :
    ∑ i : Fin d, ((μ / ↑‖μ‖) • A i)ᴴ * ((μ / ↑‖μ‖) • A i) = 1 := by
  have hn := phase_norm_one (μ := μ) hμ
  exact leftCanonical_smul_of_norm_one _ hn A hA

/-- MPV under block normalization: every block weight may be split into its
modulus and a unit-modulus phase by absorbing the modulus into the block tensor.
With $\eta_k := \mu_k / \|\mu_k\|$ and $B_k := \|\mu_k\| \cdot A_k$, the
block-diagonal tensors $\bigoplus_k \mu_k A_k$ and $\bigoplus_k \eta_k B_k$
generate the same MPV family.  See arXiv:2011.12127 Section IV.A. -/
theorem mpv_toTensorFromBlocks_normalize {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (hμ : ∀ k, μ k ≠ 0)
    (A : (k : Fin r) → MPSTensor d (dim k))
    {N : ℕ} (σ : Fin N → Fin d) :
    mpv (toTensorFromBlocks μ A) σ =
      mpv (toTensorFromBlocks (fun k => μ k / ↑‖μ k‖)
        (fun k i => (↑‖μ k‖ : ℂ) • A k i)) σ := by
  rw [mpv_toTensorFromBlocks_eq_sum, mpv_toTensorFromBlocks_eq_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hne : (↑‖μ k‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr (hμ k)
  rw [mpv_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_pow,
    div_mul_cancel₀ (μ k) hne]

end MPSTensor
