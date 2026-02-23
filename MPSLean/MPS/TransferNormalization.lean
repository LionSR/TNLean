/-
# Transfer Map Normalization (PF/μ normalization)

This file proves that scaling an MPS tensor by a scalar `c` scales the transfer map
quadratically by `c * star c = ‖c‖²`, and that various structural properties
(DS gauge, injectivity) are preserved or transform predictably under scaling.
These are the key ingredients for the "μ-normalization" step in the canonical form.
-/
import MPSLean.MPS.Transfer
import MPSLean.MPS.FundamentalTheoremMulti
import Mathlib.Analysis.Complex.Basic

open scoped Matrix ComplexOrder BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-! ## Lemma 1: Transfer map scales quadratically -/

/-- Scaling an MPS tensor by `c` scales the transfer map by `c * star c`.
Specifically, `transferMap (c • A) X = (c * starRingEnd ℂ c) • transferMap A X`
(since `c * star c = ‖c‖²` for complex scalars). -/
theorem transferMap_smul (c : ℂ) (A : MPSTensor d D) (X : Matrix (Fin D) (Fin D) ℂ) :
    transferMap (fun i => c • A i) X = (c * starRingEnd ℂ c) • transferMap A X := by
  simp only [transferMap_apply, Matrix.conjTranspose_smul]
  -- Each summand: (c • A i) * X * (star c • (A i)ᴴ) = (c * star c) • (A i * X * (A i)ᴴ)
  simp_rw [smul_mul_assoc, mul_smul_comm, smul_smul, ← Finset.smul_sum]
  rfl

/-! ## Lemma 2: DS gauge preserved under unit-norm scaling -/

/-- If `∑ i, (A i)ᴴ * (A i) = 1` and `‖c‖ = 1`, then `∑ i, (c • A i)ᴴ * (c • A i) = 1`. -/
theorem dsGauge_smul_of_norm_one (c : ℂ) (hc : ‖c‖ = 1)
    (A : MPSTensor d D) (hA : ∑ i : Fin d, (A i)ᴴ * (A i) = 1) :
    ∑ i : Fin d, (c • A i)ᴴ * (c • A i) = 1 := by
  simp only [Matrix.conjTranspose_smul]
  -- (star c • (A i)ᴴ) * (c • A i) = (star c * c) • ((A i)ᴴ * A i)
  simp_rw [smul_mul_smul_comm]
  rw [← Finset.smul_sum, hA]
  -- Goal: (star c * c) • 1 = 1
  have hsc : (star c : ℂ) * c = 1 := by
    change starRingEnd ℂ c * c = 1
    have h1 : starRingEnd ℂ c * c = ↑(Complex.normSq c) := by
      rw [mul_comm, Complex.mul_conj]
    rw [h1, Complex.normSq_eq_norm_sq, hc, one_pow, Complex.ofReal_one]
  rw [hsc, one_smul]

/-! ## Lemma 3: MPV scales by c^N under tensor scaling -/

/-- Scaling a tensor by `c` scales mpv by `c^N`. -/
theorem mpv_smul (c : ℂ) (A : MPSTensor d D) {N : ℕ} (σ : Fin N → Fin d) :
    mpv (fun i => c • A i) σ = c ^ N * mpv A σ := by
  simp only [mpv, coeff]
  rw [evalWord_smul]
  simp [List.length_ofFn, Matrix.trace_smul]

/-! ## Lemma 4: Injectivity preserved under nonzero scaling -/

/-- If `A` is injective and `c ≠ 0`, then `c • A` is injective. -/
theorem isInjective_smul (c : ℂ) (hc : c ≠ 0) (A : MPSTensor d D) (hA : IsInjective A) :
    IsInjective (fun i => c • A i) := by
  unfold IsInjective at hA ⊢
  have hrange : Set.range (fun i => c • A i) = (c • ·) '' Set.range A := by
    ext M
    simp only [Set.mem_range, Set.mem_image]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨A i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨N, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
  rw [hrange]
  rw [show (c • · : Matrix (Fin D) (Fin D) ℂ → Matrix (Fin D) (Fin D) ℂ) =
    (c • LinearMap.id : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) from by
    ext M; simp]
  rw [Submodule.span_image, hA, Submodule.map_smul _ _ c hc, Submodule.map_id]

/-! ## Theorem 5: Normalization of μ-scaled block -/

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

/-- Rescaling a tensor by `μ / ‖μ‖` (the phase of `μ`) gives a unit-norm scalar
that preserves the DS gauge condition. -/
theorem phase_norm_one {μ : ℂ} (hμ : μ ≠ 0) :
    ‖μ / ↑‖μ‖‖ = 1 := by
  rw [norm_div, Complex.norm_real, norm_norm]
  exact div_self (norm_ne_zero_iff.mpr hμ)

/-- For nonzero `μ`, writing `μ = ‖μ‖ * (μ / ‖μ‖)`, we can split a scaled tensor
`μ • A` into a modulus part `‖μ‖` and a phase part `(μ/‖μ‖) • A`. -/
theorem smul_eq_norm_smul_phase (μ : ℂ) (hμ : μ ≠ 0) (M : Matrix (Fin D) (Fin D) ℂ) :
    μ • M = (↑‖μ‖ : ℂ) • ((μ / ↑‖μ‖) • M) := by
  rw [smul_smul]
  congr 1
  rw [mul_comm, div_mul_cancel₀]
  exact_mod_cast norm_ne_zero_iff.mpr hμ

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

/-- After absorbing the modulus into the tensor, the transfer map of the
normalized tensor `‖μ‖ • A` has spectral radius scaled by `‖μ‖²`.
That is, `E_{‖μ‖ • A}(X) = ‖μ‖² • E_A(X)`. -/
theorem transferMap_norm_smul (μ : ℂ) {D' : ℕ} (A : MPSTensor d D')
    (X : Matrix (Fin D') (Fin D') ℂ) :
    transferMap (fun i => (↑‖μ‖ : ℂ) • A i) X =
      (↑(‖μ‖ ^ 2) : ℂ) • transferMap A X := by
  rw [transferMap_smul]
  congr 1
  rw [Complex.conj_ofReal, ← Complex.ofReal_mul, sq]

/-- The DS gauge condition for the normalized block:
if `∑ (A i)ᴴ * (A i) = 1` and `μ ≠ 0`, then the phase-scaled tensor
`(μ / ‖μ‖) • A` also satisfies `∑ ((μ/‖μ‖) • A i)ᴴ * ((μ/‖μ‖) • A i) = 1`. -/
theorem dsGauge_phase_smul {D' : ℕ} (μ : ℂ) (hμ : μ ≠ 0)
    (A : MPSTensor d D') (hA : ∑ i : Fin d, (A i)ᴴ * (A i) = 1) :
    ∑ i : Fin d, ((μ / ↑‖μ‖) • A i)ᴴ * ((μ / ↑‖μ‖) • A i) = 1 := by
  have hn := phase_norm_one (μ := μ) hμ
  exact dsGauge_smul_of_norm_one _ hn A hA

end MPSTensor
