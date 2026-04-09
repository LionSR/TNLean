/-
# Transfer Map Normalization (PF/μ normalization)

This file proves that scaling an MPS tensor by a scalar `c` scales the transfer map
quadratically by `c * star c = ‖c‖²`, and that various structural properties
(left-canonical / trace-preserving normalization, injectivity) are preserved or transform
predictably under scaling. These are the key ingredients for the "μ-normalization" step in the
canonical form.
-/
import TNLean.MPS.SharedInfra.Scaling
import TNLean.MPS.FundamentalTheorem.Multi
import Mathlib.Analysis.Complex.Basic

open scoped Matrix ComplexOrder BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-! ## Theorem 5: Normalization of μ-scaled block -/

-- TODO: This file is trending toward thin wrappers around `TNLean.MPS.SharedInfra.Scaling`;
-- revisit whether these aliases should be consolidated once the CF/FT dependency cleanup settles.

/-- For a block tensor `μ • A`, the MPV decomposes as `μ^N * mpv(A)`.
This is the key factorization used in μ-normalization. -/
theorem mpv_smul_block (μ : ℂ) {D' : ℕ} (A : MPSTensor d D') {N : ℕ}
    (σ : Fin N → Fin d) :
    mpv (fun i => μ • A i) σ = μ ^ N * mpv A σ :=
  mpv_smul μ A σ

/-- The transfer map of `μ • A` is `(μ * star μ)` times the transfer map of `A`.
Since `μ * star μ = ‖μ‖²`, this means that if `A` has spectral radius `ρ`,
then `μ • A` has spectral radius `‖μ‖² * ρ`. -/
theorem transferMap_smul_block (μ : ℂ) {D' : ℕ} (A : MPSTensor d D')
    (X : Matrix (Fin D') (Fin D') ℂ) :
    transferMap (fun i => μ • A i) X = (μ * starRingEnd ℂ μ) • transferMap A X :=
  transferMap_smul μ A X

/-! ## Theorem 6: Full normalization theorem -/

/-- **PF/μ normalization**: Given a block-diagonal CF tensor `toTensorFromBlocks μ A`,
one can normalize each block so that the scaling `μ_k` becomes `μ_k / ‖μ_k‖`
(unit modulus) while absorbing `‖μ_k‖` into the block tensor. The MPV is preserved exactly.

More precisely: `toTensorFromBlocks μ A` and `toTensorFromBlocks μ' A'` generate
the same MPV when `μ'_k = μ_k / ‖μ_k‖` and `A'_k = ‖μ_k‖ • A_k`. -/
theorem mpv_normalize_blocks {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (hμ : ∀ k, μ k ≠ 0)
    (A : (k : Fin r) → MPSTensor d (dim k))
    {N : ℕ} (σ : Fin N → Fin d) :
    mpv (toTensorFromBlocks μ A) σ =
      mpv (toTensorFromBlocks (fun k => μ k / ↑‖μ k‖) (fun k i => (↑‖μ k‖ : ℂ) • A k i)) σ := by
  rw [mpv_toTensorFromBlocks_eq_sum, mpv_toTensorFromBlocks_eq_sum]
  congr 1
  ext k
  -- LHS: μ k ^ N • mpv (A k) σ
  -- RHS: (μ k / ↑‖μ k‖) ^ N • mpv (fun i => ↑‖μ k‖ • A k i) σ
  -- Use mpv_smul on the RHS to unfold the scaling
  rw [mpv_smul]
  -- RHS: (μ k / ↑‖μ k‖) ^ N • (↑‖μ k‖ ^ N * mpv (A k) σ)
  rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_pow, div_mul_cancel₀]
  exact_mod_cast norm_ne_zero_iff.mpr (hμ k)

/-- **Modulus-phase factorization of the transfer map**: After normalizing,
the transfer map of `(μ_k / ‖μ_k‖) • (‖μ_k‖ • A_k)` equals the transfer map of `μ_k • A_k`.
This means the spectral properties of the transfer map are unchanged by the normalization. -/
theorem transferMap_normalize_block {D' : ℕ}
    (μ : ℂ) (hμ : μ ≠ 0) (A : MPSTensor d D')
    (X : Matrix (Fin D') (Fin D') ℂ) :
    transferMap (fun i => (μ / ↑‖μ‖) • ((↑‖μ‖ : ℂ) • A i)) X =
      transferMap (fun i => μ • A i) X := by
  have h_eq : (fun i : Fin d => (μ / ↑‖μ‖) • ((↑‖μ‖ : ℂ) • A i)) =
      (fun i => μ • A i) := by
    ext i
    rw [smul_smul, div_mul_cancel₀]
    exact_mod_cast norm_ne_zero_iff.mpr hμ
  rw [h_eq]

end MPSTensor
