/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ComplexSqrt
import TNLean.MPS.Preparation.DiagonalPolar

/-!
# The approximating state fails for blocks of multiplicity one

Malz, Styliaris, Wei, and Cirac (arXiv:2307.01696, Supplemental Material, "Proof of Lemma 1 and
extension to non-normal tensors") assert that the positive part of the blocked tensor
inherits the block structure of `Aⁱ = ⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_jⁱ` (eq. (S5)), and
bound the error of the approximating state `V^{⊗M} ∑ⱼ βⱼ |Ω_j⟩` of eq. (S7) by
`O((N/q) e^{-γ q/ξ_diag})` for `q = o(N)` (Lemma 1'(ii)), where `ξ_diag` is the largest
correlation length of the blocks.

The block form fails even when every block has multiplicity one: the Gram matrix `Bᴴ B` of the
blocked tensor couples distinct blocks through the overlaps of their `q`-site states, so its
square root `P` is not block diagonal. This file evaluates the construction for the two
one-dimensional normal blocks `A_1 = (1, 0)` and `A_2 = (3/5, 4/5)`, each of multiplicity one
with weight one, so that `A⁰ = diag(1, 3/5)` and `A¹ = diag(0, 4/5)`. With
`s = (3/5)^q`, the overlap of the `q`-site states of the blocks,
`u = (√(1+s) + √(1-s))/2`, and `v = (√(1+s) - √(1-s))/2`, the overlap of the approximating
state with the target is `(u^M + v^M) / (1 + s^M)^{1/2}` for all `q, M ≥ 1`
(`nonNormalApproxOverlap_overlappingBlockTensor`). For `M ≥ 3` the error is at least
`s²/16 = (9/25)^q/16` (`le_one_sub_norm_nonNormalApproxOverlap_overlappingBlockTensor`).

The transfer maps of one-dimensional blocks are the identity, so the hypothesis on the
subleading eigenvalue that defines `ξ_diag` holds for every `λ₂`, and `e^{-γ/ξ_diag}` can be
any number in `(0, 1)`. When it is below `9/25`, the printed rate decays faster than the error:
along `q = M`, `N = q²`, which satisfies `q = o(N)`, the error exceeds
`C (N/q) e^{-γ q/ξ_diag} exp(C (N/q) e^{-γ q/ξ_diag})` for every `C`
(`not_approximationError_le_overlappingBlockTensor`). The error is governed by the overlap
`(3/5)^q` of the blocks, which the source's estimate relegates to the term
`O(e^{-N/ξ_offdiag})` that `q = o(N)` removes.

**False source (Lemma 1'(ii), overlapping blocks):** the block form of eq. (S5) fails when the
`q`-site states of distinct blocks are not orthogonal, and the bound of Lemma 1'(ii) fails for
the approximating state of eq. (S7) even when every multiplicity is one. Documented in
`docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`.

## Main declarations

* `MPSTensor.overlappingBlockTensor` — the tensor `A⁰ = diag(1, 3/5)`, `A¹ = diag(0, 4/5)`.
* `MPSTensor.nonNormalApproxOverlap_overlappingBlockTensor` — the overlap, for all `q, M ≥ 1`.
* `MPSTensor.not_approximationError_le_overlappingBlockTensor` — the bound of Lemma 1'(ii)
  fails.

## References

* [MSWC23] D. Malz, G. Styliaris, Z.-Y. Wei, J. I. Cirac,
  *Preparation of matrix product states with log-depth quantum circuits*,
  arXiv:2307.01696, Supplemental Material, eqs. (S2)–(S7) and Lemma 1'(ii).
-/

open scoped BigOperators Matrix ComplexOrder
open Matrix Filter Topology Complex

namespace MPSTensor

/-- The diagonal entries of `A⁰ = diag(1, 3/5)` and `A¹ = diag(0, 4/5)`. -/
noncomputable def overlappingBlockDiag : Fin 2 → Fin 2 → ℂ := ![![1, 3 / 5], ![0, 4 / 5]]

/-- The tensor `A⁰ = diag(1, 3/5)`, `A¹ = diag(0, 4/5)`: the canonical form of
arXiv:2307.01696, eq. (S2), with the two one-dimensional normal blocks `A_1 = (1, 0)` and
`A_2 = (3/5, 4/5)`, each of multiplicity one and weight one. -/
noncomputable abbrev overlappingBlockTensor : MPSTensor 2 2 :=
  fun i => diagonal (overlappingBlockDiag i)

/-- The multiplicities `m = (1, 1)`. -/
def overlappingBlockMult : Fin 2 → ℕ := ![1, 1]

/-- The weights `μ_{j,1} = 1`. -/
def overlappingBlockWeight : (j : Fin 2) → Fin (overlappingBlockMult j) → ℂ := fun _ _ => 1

/-- The two one-dimensional normal blocks `A_1 = (1, 0)` and `A_2 = (3/5, 4/5)`, each in the
gauge `∑ᵢ |aᵢ|² = 1` of arXiv:2307.01696, eq. `eq:Ek_decomp`. -/
noncomputable def overlappingBlockBasis (j : Fin 2) : MPSTensor 2 1 :=
  fun i => of fun _ _ => overlappingBlockDiag i j

/-- The transfer maps of the blocks have no eigenvalue other than `1`, so the hypothesis on the
subleading eigenvalue that defines the correlation length `ξ_diag` of arXiv:2307.01696,
Lemma 1'(ii), holds for every `λ₂`. -/
theorem norm_le_of_hasEigenvalue_transferMap_overlappingBlockBasis (j : Fin 2) (lam₂ μ : ℂ)
    (h : Module.End.HasEigenvalue (Kraus.transferMap (overlappingBlockBasis j)) μ)
    (hμ : μ ≠ 1) : ‖μ‖ ≤ ‖lam₂‖ := by
  refine norm_le_of_hasEigenvalue_transferMap_of_dim_one _ ?_ lam₂ μ h hμ
  fin_cases j <;>
    simp [overlappingBlockBasis, overlappingBlockDiag, Fin.sum_univ_two, map_ofNat]
  norm_num

/-- The normalized weights `α^{(N)} = (1, 1)/√2`. -/
theorem ghzAmplitude_overlappingBlock (N : ℕ) :
    ghzAmplitude (bntWeight overlappingBlockWeight N) = ![invSqrtTwo, invSqrtTwo] := by
  have hβ : bntWeight overlappingBlockWeight N = ![1, 1] := by
    funext j
    fin_cases j <;> simp [bntWeight, overlappingBlockWeight] <;> rfl
  rw [hβ]
  have h : (∑ l, ‖(![1, 1] : Fin 2 → ℂ) l‖ ^ 2) = 2 := by
    simp [Fin.sum_univ_two]; norm_num
  funext j
  rw [ghzAmplitude, h]
  fin_cases j <;> simp [invSqrtTwo]

/-- The overlap `s = (3/5)^q` of the `q`-site states of the two blocks. -/
noncomputable def overlappingBlockOverlap (q : ℕ) : ℝ := (3 / 5) ^ q

/-- The Gram matrix of the blocked tensor: `[[1, s], [s, 1]]`. -/
theorem diagGram_overlappingBlockDiag (q : ℕ) :
    diagGram overlappingBlockDiag q =
      !![1, (overlappingBlockOverlap q : ℂ); (overlappingBlockOverlap q : ℂ), 1] := by
  ext e e'
  fin_cases e <;> fin_cases e' <;>
    simp [diagGram, overlappingBlockDiag, Fin.sum_univ_two, overlappingBlockOverlap, map_ofNat]
  all_goals norm_num

private lemma overlap_nonneg (q : ℕ) : 0 ≤ overlappingBlockOverlap q := by
  unfold overlappingBlockOverlap; positivity

private lemma overlap_le_one (q : ℕ) : overlappingBlockOverlap q ≤ 1 := by
  unfold overlappingBlockOverlap; exact pow_le_one₀ (by norm_num) (by norm_num)

private lemma overlap_lt_one {q : ℕ} (hq : q ≠ 0) : overlappingBlockOverlap q < 1 := by
  unfold overlappingBlockOverlap; exact pow_lt_one₀ (by norm_num) (by norm_num) hq

/-- `u = (√(1+s) + √(1-s))/2`. -/
noncomputable def overlappingBlockU (q : ℕ) : ℝ :=
  (Real.sqrt (1 + overlappingBlockOverlap q) + Real.sqrt (1 - overlappingBlockOverlap q)) / 2

/-- `v = (√(1+s) - √(1-s))/2`. -/
noncomputable def overlappingBlockV (q : ℕ) : ℝ :=
  (Real.sqrt (1 + overlappingBlockOverlap q) - Real.sqrt (1 - overlappingBlockOverlap q)) / 2

/-- The square root `[[u, v], [v, u]]` of the Gram matrix. -/
noncomputable def overlappingBlockSqrt (q : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(overlappingBlockU q : ℂ), (overlappingBlockV q : ℂ);
    (overlappingBlockV q : ℂ), (overlappingBlockU q : ℂ)]

private lemma sq_sqrt_add (q : ℕ) :
    Real.sqrt (1 + overlappingBlockOverlap q) ^ 2 = 1 + overlappingBlockOverlap q :=
  Real.sq_sqrt (by linarith [overlap_nonneg q])

private lemma sq_sqrt_sub (q : ℕ) :
    Real.sqrt (1 - overlappingBlockOverlap q) ^ 2 = 1 - overlappingBlockOverlap q :=
  Real.sq_sqrt (by linarith [overlap_le_one q])

theorem overlappingBlockU_sq_add_overlappingBlockV_sq (q : ℕ) :
    overlappingBlockU q ^ 2 + overlappingBlockV q ^ 2 = 1 := by
  unfold overlappingBlockU overlappingBlockV
  nlinarith [sq_sqrt_add q, sq_sqrt_sub q]

theorem two_mul_overlappingBlockU_mul_overlappingBlockV (q : ℕ) :
    2 * (overlappingBlockU q * overlappingBlockV q) = overlappingBlockOverlap q := by
  unfold overlappingBlockU overlappingBlockV
  nlinarith [sq_sqrt_add q, sq_sqrt_sub q]

theorem posSemidef_overlappingBlockSqrt (q : ℕ) : (overlappingBlockSqrt q).PosSemidef := by
  have h : overlappingBlockSqrt q =
      ((Real.sqrt (1 + overlappingBlockOverlap q) / 2 : ℝ) : ℂ) •
          vecMulVec ![1, 1] (star ![1, 1]) +
        ((Real.sqrt (1 - overlappingBlockOverlap q) / 2 : ℝ) : ℂ) •
          vecMulVec ![1, -1] (star ![1, -1]) := by
    ext e e'
    fin_cases e <;> fin_cases e' <;>
      simp [overlappingBlockSqrt, vecMulVec, overlappingBlockU, overlappingBlockV] <;> ring
  rw [h]
  exact ((posSemidef_vecMulVec_self_star _).smul
      (Complex.zero_le_real.mpr (by positivity))).add
    ((posSemidef_vecMulVec_self_star _).smul (Complex.zero_le_real.mpr (by positivity)))

theorem overlappingBlockSqrt_mul_self (q : ℕ) :
    overlappingBlockSqrt q * overlappingBlockSqrt q = diagGram overlappingBlockDiag q := by
  rw [diagGram_overlappingBlockDiag]
  have h1 : (overlappingBlockU q : ℂ) ^ 2 + (overlappingBlockV q : ℂ) ^ 2 = 1 := by
    exact_mod_cast overlappingBlockU_sq_add_overlappingBlockV_sq q
  have h2 : 2 * ((overlappingBlockU q : ℂ) * overlappingBlockV q) = overlappingBlockOverlap q := by
    exact_mod_cast two_mul_overlappingBlockU_mul_overlappingBlockV q
  ext e e'
  fin_cases e <;> fin_cases e' <;>
    simp [overlappingBlockSqrt, mul_apply, Fin.sum_univ_two] <;>
    first | linear_combination h1 | linear_combination h2

/-- For `q ≥ 1` the square root is invertible: its determinant is `u² - v² = √(1 - s²) > 0`. -/
theorem isUnit_det_overlappingBlockSqrt {q : ℕ} (hq : q ≠ 0) :
    IsUnit (overlappingBlockSqrt q).det := by
  rw [isUnit_iff_ne_zero, det_fin_two]
  have hb : 0 < Real.sqrt (1 - overlappingBlockOverlap q) :=
    Real.sqrt_pos.mpr (by linarith [overlap_lt_one hq])
  have ha : 0 < Real.sqrt (1 + overlappingBlockOverlap q) :=
    Real.sqrt_pos.mpr (by linarith [overlap_nonneg q])
  have h : overlappingBlockU q * overlappingBlockU q - overlappingBlockV q * overlappingBlockV q =
      Real.sqrt (1 + overlappingBlockOverlap q) * Real.sqrt (1 - overlappingBlockOverlap q) := by
    unfold overlappingBlockU overlappingBlockV; ring
  have hc : (overlappingBlockU q : ℂ) * overlappingBlockU q -
      (overlappingBlockV q : ℂ) * overlappingBlockV q ≠ 0 := by
    have : overlappingBlockU q * overlappingBlockU q -
        overlappingBlockV q * overlappingBlockV q ≠ 0 := by rw [h]; positivity
    exact_mod_cast this
  simpa [overlappingBlockSqrt] using hc

/-- The support projector of the `q`-site blocked tensor is `J Jᴴ`, for `q ≥ 1`. -/
theorem polarSupport_overlappingBlockTensor {q : ℕ} (hq : q ≠ 0) :
    polarSupport (physicalMatrix (blockTensor overlappingBlockTensor q)) =
      diagPairEmbedding (Fin 2) * (1 : Matrix (Fin 2) (Fin 2) ℂ) * (diagPairEmbedding (Fin 2))ᴴ :=
  polarSupport_physicalMatrix_blockTensor_diagonal overlappingBlockDiag q
    (posSemidef_overlappingBlockSqrt q) (overlappingBlockSqrt_mul_self q) isHermitian_one
    (Matrix.one_mul 1) (Matrix.one_mul _) (R := (overlappingBlockSqrt q)⁻¹)
    (mul_nonsing_inv _ (isUnit_det_overlappingBlockSqrt hq))

/-- **The overlap for overlapping blocks** (arXiv:2307.01696, eq. (S7)). For the tensor
`A⁰ = diag(1, 3/5)`, `A¹ = diag(0, 4/5)`, the fixed-point pairs of its two one-dimensional
blocks, the coefficients `α^{(N)}` of the weights `β = (1, 1)`, every block length `q ≥ 1`, and
every number of blocks `M ≥ 1`, `⟨φ̃_N|φ_N⟩ = (u^M + v^M) / (1 + s^M)^{1/2}`. -/
theorem nonNormalApproxOverlap_overlappingBlockTensor {q M : ℕ} (hq : q ≠ 0) (hM : M ≠ 0) :
    nonNormalApproxOverlap overlappingBlockTensor q M
        (ghzAmplitude (bntWeight overlappingBlockWeight (M * q)))
        (fun j => embedPair (fun _ : Fin 1 => j)
          (fixedPointPair (1 : Matrix (Fin 1) (Fin 1) ℂ))) =
      (((overlappingBlockU q ^ M + overlappingBlockV q ^ M) /
        Real.sqrt (1 + overlappingBlockOverlap q ^ M) : ℝ) : ℂ) := by
  simp only [embedPair_fixedPointPair_one]
  rw [show overlappingBlockTensor = fun i => diagonal (overlappingBlockDiag i) from rfl]
  rw [nonNormalApproxOverlap_diagonal overlappingBlockDiag q M _ (fun j => j) (X := 1)
    (Y := 2 * (1 + overlappingBlockOverlap q ^ M))]
  · rw [polarPos_physicalMatrix_blockTensor_diagonal overlappingBlockDiag q
      (posSemidef_overlappingBlockSqrt q) (overlappingBlockSqrt_mul_self q),
      ghzAmplitude_overlappingBlock]
    simp only [diagPairEmbedding_mul_mul_conjTranspose_apply, Fin.sum_univ_two,
      overlappingBlockSqrt]
    simp [invSqrtTwo]
    have hs2 : Real.sqrt 2 ≠ 0 := by positivity
    have hs : Real.sqrt (1 + overlappingBlockOverlap q ^ M) ≠ 0 := by
      have := overlap_nonneg q; positivity
    have hsq : ((Real.sqrt 2 : ℝ) : ℂ) * (Real.sqrt 2 : ℝ) = 2 := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
    field_simp
    linear_combination (-1) * (↑(overlappingBlockU q) ^ M + ↑(overlappingBlockV q) ^ M) * hsq
  · rw [polarSupport_overlappingBlockTensor hq, ghzAmplitude_overlappingBlock]
    simp only [diagPairEmbedding_mul_mul_conjTranspose_apply, Fin.sum_univ_two]
    simp [zero_pow hM, invSqrtTwo_mul_self]
    norm_num
  · rw [diagGram_overlappingBlockDiag]
    simp [Fin.sum_univ_two]
    ring

/-- **The error for overlapping blocks is at least `(9/25)^q / 16`** once `M ≥ 3`: the
approximating state of arXiv:2307.01696, eq. (S7) misses the target by an amount governed by
the overlap `s = (3/5)^q` of the blocks. -/
theorem le_one_sub_norm_nonNormalApproxOverlap_overlappingBlockTensor {q M : ℕ} (hq : q ≠ 0)
    (hM : 3 ≤ M) :
    (9 / 25 : ℝ) ^ q / 16 ≤
      1 - ‖nonNormalApproxOverlap overlappingBlockTensor q M
        (ghzAmplitude (bntWeight overlappingBlockWeight (M * q)))
        (fun j => embedPair (fun _ : Fin 1 => j)
          (fixedPointPair (1 : Matrix (Fin 1) (Fin 1) ℂ)))‖ := by
  rw [nonNormalApproxOverlap_overlappingBlockTensor hq (by omega), Complex.norm_real]
  set s := overlappingBlockOverlap q
  set u := overlappingBlockU q
  set v := overlappingBlockV q
  have hs0 : 0 ≤ s := overlap_nonneg q
  have hs1 : s ≤ 1 := overlap_le_one q
  have ha := sq_sqrt_add q
  have hb := sq_sqrt_sub q
  have ha0 := Real.sqrt_nonneg (1 + s)
  have hb0 := Real.sqrt_nonneg (1 - s)
  have huv := overlappingBlockU_sq_add_overlappingBlockV_sq q
  have hv0 : 0 ≤ v := by
    have : Real.sqrt (1 - s) ≤ Real.sqrt (1 + s) := Real.sqrt_le_sqrt (by linarith)
    simp only [v, overlappingBlockV]; linarith
  have hu0 : 0 ≤ u := by simp only [u, overlappingBlockU]; positivity
  have hu1 : u ≤ 1 := by nlinarith [sq_nonneg v]
  have hv1 : v ≤ 1 := by nlinarith [sq_nonneg u]
  have hab : Real.sqrt (1 + s) * Real.sqrt (1 - s) ≤ 1 - s ^ 2 / 2 := by
    rw [← Real.sqrt_mul (by linarith), Real.sqrt_le_iff]
    constructor <;> nlinarith
  have hu2 : u ^ 2 = (1 + Real.sqrt (1 + s) * Real.sqrt (1 - s)) / 2 := by
    rw [show u = (Real.sqrt (1 + s) + Real.sqrt (1 - s)) / 2 from rfl]
    linear_combination (ha + hb) / 4
  have hkey : u ^ 3 + v ^ 2 ≤ 1 - s ^ 2 / 16 := by
    have hu2' : 1 / 2 ≤ u ^ 2 := by nlinarith [mul_nonneg ha0 hb0]
    have h1u2 : s ^ 2 / 4 ≤ 1 - u ^ 2 := by nlinarith
    have h1u : s ^ 2 / 8 ≤ 1 - u := by nlinarith
    nlinarith [mul_le_mul hu2' h1u (by positivity) (by positivity)]
  have huM : u ^ M ≤ u ^ 3 := pow_le_pow_of_le_one hu0 hu1 hM
  have hvM : v ^ M ≤ v ^ 2 := pow_le_pow_of_le_one hv0 hv1 (by omega)
  have hden : 1 ≤ Real.sqrt (1 + s ^ M) := by
    have := pow_nonneg hs0 M
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ _ := Real.sqrt_le_sqrt (by linarith)
  have hnum : 0 ≤ u ^ M + v ^ M := by positivity
  have hdiv : |(u ^ M + v ^ M) / Real.sqrt (1 + s ^ M)| ≤ u ^ M + v ^ M := by
    rw [abs_of_nonneg (by positivity)]
    exact div_le_self hnum hden
  have hs2 : (9 / 25 : ℝ) ^ q = s ^ 2 := by
    rw [show s = (3 / 5 : ℝ) ^ q from rfl, ← pow_mul, mul_comm, pow_mul]; norm_num
  rw [Real.norm_eq_abs, hs2]
  linarith

/-- **Lemma 1'(ii) fails for overlapping blocks** (arXiv:2307.01696, Supplemental Material,
Lemma 1'(ii), eq. (S12)). The transfer maps of the one-dimensional blocks of
`overlappingBlockTensor` have no eigenvalue other than `1`, so every `λ₂` bounds their
subleading eigenvalues and `r = e^{-γ/ξ_diag}` can be any number in `(0, 1)`. When `r < 9/25`,
for every constant `C` there is a block length `q ≥ 3` such that, with `M = q` blocks
(`N = q²`, so `q = o(N)` along this sequence) and `y = (N/q) e^{-γ q/ξ_diag}`, the error of the
approximating state of eq. (S7) exceeds `C y e^{C y}`, and in particular exceeds `C y`. -/
theorem not_approximationError_le_overlappingBlockTensor {lam₂ : ℂ} {γ : ℝ}
    (hr : Real.exp (-γ / correlationLength lam₂) < 9 / 25) (C : ℝ) :
    ∃ q : ℕ, 3 ≤ q ∧
      C * (q * Real.exp (-γ * q / correlationLength lam₂)) *
          Real.exp (C * (q * Real.exp (-γ * q / correlationLength lam₂))) <
        1 - ‖nonNormalApproxOverlap overlappingBlockTensor q q
          (ghzAmplitude (bntWeight overlappingBlockWeight (q * q)))
          (fun j => embedPair (fun _ : Fin 1 => j)
            (fixedPointPair (1 : Matrix (Fin 1) (Fin 1) ℂ)))‖ := by
  set r := Real.exp (-γ / correlationLength lam₂)
  have hxq : ∀ q : ℕ, Real.exp (-γ * q / correlationLength lam₂) = r ^ q := fun q => by
    rw [← Real.exp_nat_mul]; congr 1; ring
  obtain ⟨q, hlt, hq⟩ := ((eventually_mul_pow_mul_exp_lt (Real.exp_pos _).le hr
    (by norm_num) C (1 / 16) (by norm_num)).and (Filter.eventually_ge_atTop 3)).exists
  refine ⟨q, hq, ?_⟩
  rw [hxq]
  have hlow := le_one_sub_norm_nonNormalApproxOverlap_overlappingBlockTensor (q := q) (M := q)
    (by omega) hq
  linarith

end MPSTensor
