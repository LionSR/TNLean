/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.RepeatedOverlappingBlockWeights

/-!
# The approximating state with the pairs on one copy

Malz, Styliaris, Wei, and Cirac (arXiv:2307.01696, Supplemental Material, eqs. (S2)–(S7)) write a
tensor that is not normal as `Aⁱ = ⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_jⁱ` with complex weights
`|μ_{j,k}| ≤ 1`, and approximate its state on `N = qM` sites by `V^{⊗M} ∑ⱼ βⱼ |Ω_j⟩` with
`βⱼ = ∑ₖ μ_{j,k}^N` (eq. (S4)), where `B = V P` is the polar decomposition of the `q`-site blocked
tensor and `|Ω_j⟩` is the product of the pairs of the fixed point of `A_j`. The source does not say
on which copy of block `j` the pairs sit; here they sit on a chosen copy `k_j`.

With these coefficients the state fails twice: for `m_j ≥ 2` already for positive weights
(`MPSTensor.nonNormalApproxOverlap_repeatedBlockTensor`), and for `m_j = 1` already for two
blocks with the weights `1` and `μ ≠ 1` with `|μ| = 1`
(`MPSTensor.nonNormalApproxOverlap_phaseBlockTensor`). This file
shows that both failures concern only the coefficients. Write `cⱼ = (∑ₖ |μ_{j,k}|^{2q})^{1/2}` and
`L_j = ∑ₖ (conj(μ_{j,k}^q) / cⱼ) K_{j,k}` for the copy isometry of
`TNLean.MPS.Preparation.RepeatedBlockSum`, with `K_{j,k}` the isometry placing the bond pairs of
copy `k` of block `j`. The blocked tensor is `B = ∑ⱼ cⱼ B_j L_jᴴ`, so
`B K_{j,k} = μ_{j,k}^q B_j = (μ_{j,k}^q / cⱼ) B L_j`. The partial isometry `V` vanishes on the
kernel of `B` (`Matrix.polarIso_mul_eq_zero`), hence

  `V K_{j,k} = (μ_{j,k}^q / cⱼ) V L_j`

(`polarIso_blockTensor_repeatedBlockSum_mul_pairEmbedding`). No orthogonality of the blocks is
needed. Applying `V^{⊗M}`, the state with the pairs on copy `k_j` and the coefficients

  `β'ⱼ = βⱼ (cⱼ / μ_{j,k_j}^q)^M`

(`oneCopyWeight`) is the corrected state `V^{⊗M} ∑ⱼ βⱼ L_j^{⊗M} |Ω_j⟩`
(`nonNormalApproxVector_repeatedBlockSum_oneCopy`), and the two have the same overlap with the
target (`nonNormalApproxOverlap_repeatedBlockSum_oneCopy`). For `m_j = 1`, `β'ⱼ = |μⱼ|^N`
(`oneCopyWeight_of_subsingleton`), the coefficient of the complex-weight corollaries in
`TNLean.MPS.Preparation.BlockSumError`. The error
bounds for the corrected state therefore hold for the source's construction with these
coefficients, for any phases of the weights
(`exists_approximationError_le_repeatedOverlappingBlockSum_oneCopy`,
`exists_approximationError_le_mul_repeatedOverlappingBlockSum_oneCopy`), with a constant that does
not depend on the weights.

**False source (eq. (S7), coefficients):** the coefficients `βⱼ = ∑ₖ μ_{j,k}^N` that eq. (S7) takes
from eq. (S4) are replaced by `β'ⱼ = βⱼ (cⱼ / μ_{j,k_j}^q)^M`. With the printed coefficients the
bound is false, for `m_j ≥ 2` (`docs/paper-gaps/mswc24_multiplicity_fixed_point.tex`) and for
`m_j = 1` with a weight of modulus one that is not one
(`docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`).
The correction is documented in `docs/paper-gaps/mswc24_repeated_block_corrected_state.tex`.

**Local fix (rate of the overlapping blocks):** in
`exists_approximationError_le_repeatedOverlappingBlockSum_oneCopy` and
`exists_approximationError_le_mul_repeatedOverlappingBlockSum_oneCopy` the rate
`e^{-γ q/ξ_diag}` of the source is replaced by `e^{-γ q/ξ}` with `ξ ≥ max(ξ_diag, ξ_off-diag)`.
Documented in `docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`.

## Main declarations

* `MPSTensor.oneCopyWeight` — the coefficients `β'ⱼ = βⱼ (cⱼ / μ_{j,k_j}^q)^M`.
* `MPSTensor.polarIso_blockTensor_repeatedBlockSum_mul_pairEmbedding` —
  `V K_{j,k} = (μ_{j,k}^q / cⱼ) V L_j`.
* `MPSTensor.nonNormalApproxVector_repeatedBlockSum_oneCopy`,
  `MPSTensor.nonNormalApproxOverlap_repeatedBlockSum_oneCopy` — the state with the pairs on one
  copy and the coefficients `β'ⱼ` is the corrected state.
* `MPSTensor.exists_approximationError_le_repeatedOverlappingBlockSum_oneCopy` — Lemma 1'(ii)
  for the source's construction with the coefficients `β'ⱼ`.

## References

* [MSWC23] D. Malz, G. Styliaris, Z.-Y. Wei, J. I. Cirac,
  *Preparation of matrix product states with log-depth quantum circuits*,
  arXiv:2307.01696, Supplemental Material, eqs. (S2)–(S12) and Lemma 1'(ii)
  (`eq:fid_err_gen_non_normal`).
-/

open scoped BigOperators Matrix ComplexOrder
open Matrix

namespace MPSTensor

variable {d D b : ℕ} {m : Fin b → ℕ} {Dj : Fin b → ℕ}
  {Aj : (j : Fin b) → MPSTensor d (Dj j)} {ι : (j : Fin b) → Fin (m j) → Fin (Dj j) → Fin D}

/-! ### The coefficients -/

/-- The coefficient `β'ⱼ = βⱼ (cⱼ / μ_{j,k_j}^q)^M` of block `j` in the approximating state of
arXiv:2307.01696, Supplemental Material, eq. (S7), when the pairs of block `j` sit on its copy
`k_j`, with `βⱼ = ∑ₖ μ_{j,k}^N` (eq. (S4)), `N = qM`, and `cⱼ = (∑ₖ |μ_{j,k}|^{2q})^{1/2}`; it
replaces the coefficient `βⱼ` of eq. (S7). -/
noncomputable def oneCopyWeight (μ : (j : Fin b) → Fin (m j) → ℂ) (k : (j : Fin b) → Fin (m j))
    (q M : ℕ) (j : Fin b) : ℂ :=
  bntWeight μ (M * q) j * ((copyNorm μ q j : ℂ) / μ j (k j) ^ q) ^ M

/-- **The coefficient for a block of multiplicity one.** If block `j` has the single copy `k_j`,
then `β'ⱼ = |μ_{j,k_j}|^N`, the coefficient of
`MPSTensor.exists_approximationError_le_overlappingBlockSum_complexWeight`. -/
theorem oneCopyWeight_of_subsingleton (μ : CopyWeights b m) (k : (j : Fin b) → Fin (m j))
    {j : Fin b} (hk : ∀ k' : Fin (m j), k' = k j) (q M : ℕ) :
    oneCopyWeight μ k q M j = ((‖μ j (k j)‖ ^ (M * q) : ℝ) : ℂ) := by
  have hμ := μ.weight_ne_zero j (k j)
  have hsum : ∀ f : Fin (m j) → ℂ, ∑ k', f k' = f (k j) := fun f =>
    Finset.sum_eq_single (k j) (fun k' _ h => absurd (hk k') h) (by simp)
  have hsumR : ∑ k', ‖μ j k'‖ ^ (2 * q) = ‖μ j (k j)‖ ^ (2 * q) :=
    Finset.sum_eq_single (k j) (fun k' _ h => absurd (hk k') h) (by simp)
  have hc : copyNorm μ q j = ‖μ j (k j)‖ ^ q := by
    rw [copyNorm, hsumR, pow_mul', Real.sqrt_sq (by positivity)]
  rw [oneCopyWeight, bntWeight, hsum, hc]
  have hq : μ j (k j) ^ q ≠ 0 := pow_ne_zero q hμ
  push_cast
  rw [div_pow, mul_div_assoc', ← pow_mul, mul_comm q M, ← pow_mul, mul_comm q M]
  field_simp

/-- The coefficients `β'ⱼ` and `βⱼ` vanish together: `β' ≠ 0` when `β ≠ 0`. -/
theorem oneCopyWeight_ne_zero {μ : CopyWeights b m} (k : (j : Fin b) → Fin (m j)) {q M : ℕ}
    (hβ : bntWeight μ (M * q) ≠ 0) : oneCopyWeight μ k q M ≠ 0 := by
  obtain ⟨l, hl⟩ := Function.ne_iff.1 hβ
  refine Function.ne_iff.2 ⟨l, mul_ne_zero hl (pow_ne_zero _ (div_ne_zero ?_ ?_))⟩
  · exact Complex.ofReal_ne_zero.2 (copyNorm_pos (μ.weight_fun_ne_zero l) q).ne'
  · exact pow_ne_zero _ (μ.weight_ne_zero l (k l))

/-! ### The partial isometry on one copy -/

/-- `L_jᴴ K_{j,k} = (μ_{j,k}^q / cⱼ) 1`: the copy isometry restricted to one copy. -/
theorem conjTranspose_copyIsometry_mul_pairEmbedding (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    (μ : (j : Fin b) → Fin (m j) → ℂ) (q : ℕ) (j : Fin b) (k : Fin (m j)) :
    (copyIsometry ι μ q j)ᴴ * pairEmbedding (ι j k) =
      (μ j k ^ q / (copyNorm μ q j : ℂ)) • (1 : Matrix _ _ ℂ) := by
  rw [conjTranspose_copyIsometry, Matrix.sum_mul, Finset.sum_eq_single k]
  · rw [Matrix.smul_mul, conjTranspose_pairEmbedding_mul_self (hι j k)]
  · intro k' _ hk'
    rw [Matrix.smul_mul, conjTranspose_pairEmbedding_mul_copy hdisj k' k
      (fun h => hk' (eq_of_heq (Sigma.mk.inj h).2)), smul_zero]
  · simp

/-- `L_{j'}ᴴ K_{j,k} = 0` for distinct blocks `j' ≠ j`. -/
theorem conjTranspose_copyIsometry_mul_pairEmbedding_eq_zero
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    (μ : (j : Fin b) → Fin (m j) → ℂ) (q : ℕ) {j j' : Fin b} (h : j' ≠ j) (k : Fin (m j)) :
    (copyIsometry ι μ q j')ᴴ * pairEmbedding (ι j k) = 0 := by
  rw [conjTranspose_copyIsometry, Matrix.sum_mul]
  refine Finset.sum_eq_zero fun k' _ => ?_
  rw [Matrix.smul_mul, conjTranspose_pairEmbedding_mul_copy hdisj k' k
    (fun h' => h (Sigma.mk.inj h').1), smul_zero]

/-- **The partial isometry on one copy.** For the direct sum with multiplicities and nonzero
weights and `q ≥ 1`, the partial isometry `V` of the `q`-site blocked tensor satisfies
`V K_{j,k} = (μ_{j,k}^q / cⱼ) V L_j`: since `B = ∑ⱼ cⱼ B_j L_jᴴ`, the matrix
`K_{j,k} - (μ_{j,k}^q / cⱼ) L_j` lies in the kernel of `B`, on which `V` vanishes. The `q`-site
states of distinct blocks need not be orthogonal (arXiv:2307.01696, Supplemental Material,
eqs. (S5)–(S7)). -/
theorem polarIso_blockTensor_repeatedBlockSum_mul_pairEmbedding
    (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    (μ : CopyWeights b m) {q : ℕ} (hq : q ≠ 0) (j : Fin b) (k : Fin (m j)) :
    polarIso (physicalMatrix (blockTensor (repeatedBlockSum Aj ι μ) q)) * pairEmbedding (ι j k) =
      (μ j k ^ q / (copyNorm μ q j : ℂ)) •
        (polarIso (physicalMatrix (blockTensor (repeatedBlockSum Aj ι μ) q)) *
          copyIsometry ι μ q j) := by
  have hc0 : (copyNorm μ q j : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (copyNorm_pos (μ.weight_fun_ne_zero j) q).ne'
  have hB := physicalMatrix_blockTensor_repeatedBlockSum_eq_copyIsometry (Aj := Aj) hι hdisj
    (μ := μ) hq
  have hBK : physicalMatrix (blockTensor (repeatedBlockSum Aj ι μ) q) * pairEmbedding (ι j k) =
      μ j k ^ q • physicalMatrix (blockTensor (Aj j) q) := by
    rw [hB, Matrix.sum_mul, Finset.sum_eq_single j]
    · rw [Matrix.smul_mul, Matrix.mul_assoc,
        conjTranspose_copyIsometry_mul_pairEmbedding hι hdisj, Matrix.mul_smul, Matrix.mul_one,
        smul_smul, mul_div_cancel₀ _ hc0]
    · intro j' _ hj'
      rw [Matrix.smul_mul, Matrix.mul_assoc,
        conjTranspose_copyIsometry_mul_pairEmbedding_eq_zero hdisj _ q hj', Matrix.mul_zero,
        smul_zero]
    · simp
  have hBL : physicalMatrix (blockTensor (repeatedBlockSum Aj ι μ) q) * copyIsometry ι μ q j =
      (copyNorm μ q j : ℂ) • physicalMatrix (blockTensor (Aj j) q) := by
    rw [hB, Matrix.sum_mul, Finset.sum_eq_single j]
    · rw [Matrix.smul_mul, Matrix.mul_assoc,
        conjTranspose_copyIsometry_mul_self hι hdisj (μ.weight_fun_ne_zero j), Matrix.mul_one]
    · intro j' _ hj'
      rw [Matrix.smul_mul, Matrix.mul_assoc, conjTranspose_copyIsometry_mul_eq_zero hdisj _ q hj',
        Matrix.mul_zero, smul_zero]
    · simp
  have h0 : physicalMatrix (blockTensor (repeatedBlockSum Aj ι μ) q) *
      (pairEmbedding (ι j k) - (μ j k ^ q / (copyNorm μ q j : ℂ)) • copyIsometry ι μ q j) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_smul, hBK, hBL, smul_smul, div_mul_cancel₀ _ hc0, sub_self]
  have h := Matrix.polarIso_mul_eq_zero h0
  rwa [Matrix.mul_sub, Matrix.mul_smul, sub_eq_zero] at h

/-! ### The approximating state -/

/-- **The state with the pairs on one copy is the corrected state.** For the direct sum with
multiplicities and nonzero weights and `q ≥ 1`, the unnormalized state `V^{⊗M} ∑ⱼ αⱼ |Ω_j⟩` of
arXiv:2307.01696, Supplemental Material, eq. (S7), with the pairs of `σ_j` on the copy `k_j` of
block `j`, is the corrected state `V^{⊗M} ∑ⱼ α'ⱼ L_j^{⊗M} |Ω_j⟩` with
`α'ⱼ = αⱼ (μ_{j,k_j}^q / cⱼ)^M`. The `q`-site states of distinct blocks need not be orthogonal. -/
theorem nonNormalApproxVector_repeatedBlockSum_oneCopy (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    (μ : CopyWeights b m) {q : ℕ} (hq : q ≠ 0) (k : (j : Fin b) → Fin (m j))
    (σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) (M : ℕ) (α : Fin b → ℂ) :
    nonNormalApproxVector (repeatedBlockSum Aj ι μ) q M α
        (fun j => embedPair (ι j (k j)) (fixedPointPair (σ j))) =
      copyApproxVector (repeatedBlockSum Aj ι μ) q M
        (fun j => α j * (μ j (k j) ^ q / (copyNorm μ q j : ℂ)) ^ M) (copyIsometry ι μ q) σ := by
  set V := polarIso (physicalMatrix (blockTensor (repeatedBlockSum Aj ι μ) q))
  have hstate : nonNormalFixedPointState (M := M) α
      (fun j => embedPair (ι j (k j)) (fixedPointPair (σ j))) =
      ∑ j, α j • pairProductState (embedPair (ι j (k j)) (fixedPointPair (σ j))) := by
    funext c
    simp [nonNormalFixedPointState, Finset.sum_apply]
  rw [nonNormalApproxVector, copyApproxVector, copyFixedPointState, hstate, mulVec_sum,
    mulVec_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mulVec_smul, mulVec_smul, pairProductState_embedPair_eq_mulVec (hι j (k j)), mulVec_mulVec,
    tensorPower_mul, polarIso_blockTensor_repeatedBlockSum_mul_pairEmbedding hι hdisj μ hq,
    tensorPower_smul, smul_mulVec, ← tensorPower_mul, ← mulVec_mulVec, smul_smul]

/-- Rescaling the coefficients by `t > 0` does not change the overlap of the normalized corrected
state with the target. -/
theorem copyApproxOverlap_ofReal_mul (A : MPSTensor d D) (q M : ℕ) {t : ℝ} (ht : 0 < t)
    (α : Fin b → ℂ) (L : (j : Fin b) → Matrix (Fin D × Fin D) (Fin (Dj j) × Fin (Dj j)) ℂ)
    (σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) :
    copyApproxOverlap A q M (fun j => (t : ℂ) * α j) L σ = copyApproxOverlap A q M α L σ := by
  have hv : copyApproxVector A q M (fun j => (t : ℂ) * α j) L σ =
      (t : ℂ) • copyApproxVector A q M α L σ := by
    rw [copyApproxVector, copyApproxVector, ← mulVec_smul]
    congr 1
    simp only [copyFixedPointState, Finset.smul_sum, smul_smul]
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
  rw [copyApproxOverlap_eq, copyApproxOverlap_eq, hv]
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos ht, mul_pow, ← Finset.mul_sum, star_mul', Complex.star_def, Complex.conj_ofReal]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq ht.le, Complex.ofReal_mul, mul_inv]
  simp_rw [mul_assoc (t : ℂ)]
  rw [← Finset.mul_sum]
  field_simp

/-- The normalized weights are the weights times a positive number. -/
private theorem ghzAmplitude_eq_ofReal_mul (β : Fin b → ℂ) :
    ghzAmplitude β = fun j => ((Real.sqrt (∑ l, ‖β l‖ ^ 2))⁻¹ : ℝ) * β j := by
  funext j
  rw [ghzAmplitude, div_eq_mul_inv, mul_comm, Complex.ofReal_inv]

/-- **The overlap with the pairs on one copy.** For the direct sum with multiplicities and nonzero
weights and `q ≥ 1`, the overlap with the target of the normalized approximating state of
arXiv:2307.01696, Supplemental Material, eq. (S7), with the pairs of `σ_j` on the copy `k_j` of
block `j` and the coefficients `β'ⱼ = βⱼ (cⱼ / μ_{j,k_j}^q)^M` in place of `βⱼ = ∑ₖ μ_{j,k}^N`, is
the overlap of the corrected state `V^{⊗M} ∑ⱼ αⱼ L_j^{⊗M} |Ω_j⟩` with the coefficients `βⱼ`. -/
theorem nonNormalApproxOverlap_repeatedBlockSum_oneCopy (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    (μ : CopyWeights b m) {q : ℕ} (hq : q ≠ 0) (k : (j : Fin b) → Fin (m j))
    (σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) (M : ℕ) :
    nonNormalApproxOverlap (repeatedBlockSum Aj ι μ) q M (ghzAmplitude (oneCopyWeight μ k q M))
        (fun j => embedPair (ι j (k j)) (fixedPointPair (σ j))) =
      copyApproxOverlap (repeatedBlockSum Aj ι μ) q M (ghzAmplitude (bntWeight μ (M * q)))
        (copyIsometry ι μ q) σ := by
  rw [nonNormalApproxOverlap_eq, nonNormalApproxVector_repeatedBlockSum_oneCopy hι hdisj μ hq,
    ← copyApproxOverlap_eq]
  set β := bntWeight μ (M * q)
  set β' := oneCopyWeight μ k q M
  have hα' : (fun j => ghzAmplitude β' j * (μ j (k j) ^ q / (copyNorm μ q j : ℂ)) ^ M) =
      fun j => ((Real.sqrt (∑ l, ‖β' l‖ ^ 2))⁻¹ : ℝ) * β j := by
    funext j
    have hc0 : (copyNorm μ q j : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (copyNorm_pos (μ.weight_fun_ne_zero j) q).ne'
    have hμ0 : μ j (k j) ^ q ≠ 0 := pow_ne_zero q (μ.weight_ne_zero j (k j))
    rw [ghzAmplitude_eq_ofReal_mul]
    simp only [β', oneCopyWeight]
    have hone : ((copyNorm μ q j : ℂ) / μ j (k j) ^ q) ^ M *
        (μ j (k j) ^ q / (copyNorm μ q j : ℂ)) ^ M = 1 := by
      rw [← mul_pow, div_mul_div_comm, mul_comm (copyNorm μ q j : ℂ),
        div_self (mul_ne_zero hμ0 hc0), one_pow]
    rw [mul_assoc, mul_assoc, hone, mul_one]
  rw [hα', ghzAmplitude_eq_ofReal_mul]
  by_cases hβ : β = 0
  · simp [hβ]
  · rw [copyApproxOverlap_ofReal_mul _ _ _ (inv_pos.2 (Real.sqrt_pos.2
        (sum_norm_sq_pos_of_ne_zero (oneCopyWeight_ne_zero k hβ)))),
      copyApproxOverlap_ofReal_mul _ _ _
        (inv_pos.2 (Real.sqrt_pos.2 (sum_norm_sq_pos_of_ne_zero hβ)))]

/-! ### The error bounds -/

/-- **Approximation error with the pairs on one copy, for overlapping blocks** (arXiv:2307.01696,
Supplemental Material, Lemma 1'(ii), eq. (S12), at the corrected rate, with the coefficients `β'ⱼ`
in place of the coefficients `βⱼ` of eq. (S7)). In the setting of
`MPSTensor.exists_approximationError_le_repeatedOverlappingBlockSum`, there is `C > 0`, independent
of the weights, such that for all nonzero complex weights, every choice of copies `k_j`, every
block length `q ≥ 1` and every number of blocks `M ≥ 1` with `βⱼ = ∑ₖ μ_{j,k}^N` not all zero, the
error of the approximating state with the pairs of `σ_j` on the copy `k_j` and the coefficients
`β'ⱼ = βⱼ (cⱼ / μ_{j,k_j}^q)^M` satisfies `ε ≤ C y e^{C y}` with `y = M e^{-γ q/ξ}`. -/
theorem exists_approximationError_le_repeatedOverlappingBlockSum_oneCopy
    (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ}
    (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    (hmix : ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
      ‖μ'‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : CopyWeights b m) (k : (j : Fin b) → Fin (m j)) (q M : ℕ) [NeZero M],
      q ≠ 0 → bntWeight μ (M * q) ≠ 0 →
      1 - ‖nonNormalApproxOverlap (repeatedBlockSum Aj ι μ) q M
          (ghzAmplitude (oneCopyWeight μ k q M))
          (fun j => embedPair (ι j (k j)) (fixedPointPair (σ j)))‖ ≤
        C * (M * Real.exp (-γ * q / correlationLength lam₂)) *
            Real.exp (C * (M * Real.exp (-γ * q / correlationLength lam₂))) := by
  obtain ⟨C, hC, h⟩ := exists_approximationError_le_repeatedOverlappingBlockSum hι hdisj hN hA
    hσ htr hfix hlam hmix hγ0 hγ
  refine ⟨C, hC, fun μ k q M _ hq hβ => ?_⟩
  rw [nonNormalApproxOverlap_repeatedBlockSum_oneCopy hι hdisj μ hq]
  exact h μ q M hβ

/-- **Approximation error with the pairs on one copy, for overlapping blocks, `O`-form**
(arXiv:2307.01696, Supplemental Material, Lemma 1'(ii), eq. (S12), at the corrected rate, with the
coefficients `β'ⱼ`): in the setting of
`exists_approximationError_le_repeatedOverlappingBlockSum_oneCopy`, there is `C` with
`ε ≤ C M e^{-γ q/ξ}`, which is `C (N/q) e^{-γ q/ξ}`, for all nonzero complex weights. -/
theorem exists_approximationError_le_mul_repeatedOverlappingBlockSum_oneCopy
    (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ}
    (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    (hmix : ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
      ‖μ'‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : CopyWeights b m) (k : (j : Fin b) → Fin (m j)) (q M : ℕ) [NeZero M],
      q ≠ 0 → bntWeight μ (M * q) ≠ 0 →
      1 - ‖nonNormalApproxOverlap (repeatedBlockSum Aj ι μ) q M
          (ghzAmplitude (oneCopyWeight μ k q M))
          (fun j => embedPair (ι j (k j)) (fixedPointPair (σ j)))‖ ≤
        C * (M * Real.exp (-γ * q / correlationLength lam₂)) := by
  obtain ⟨C, hC, h⟩ := exists_approximationError_le_mul_repeatedOverlappingBlockSum hι hdisj hN hA
    hσ htr hfix hlam hmix hγ0 hγ
  refine ⟨C, hC, fun μ k q M _ hq hβ => ?_⟩
  rw [nonNormalApproxOverlap_repeatedBlockSum_oneCopy hι hdisj μ hq]
  exact h μ q M hβ

end MPSTensor
