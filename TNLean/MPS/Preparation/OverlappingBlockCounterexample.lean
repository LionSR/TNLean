/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ComplexSqrt
import TNLean.MPS.FundamentalTheorem.SectorBNT.Api
import TNLean.MPS.Preparation.OneDimensionalBlocks

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
`s²/16 = (9/25)^q/16` (`le_one_sub_norm_nonNormalApproxOverlap_overlappingBlockTensor`), and
for every `M ≥ 1` it is at most `M s²`
(`one_sub_norm_nonNormalApproxOverlap_overlappingBlockTensor_le`): the construction converges,
at the rate `M s²` set by the square of the overlap of the blocks.

The tensor lies in the domain of Lemma 1'(ii): after ordering its bond coordinates it is the
canonical form of eq. (S2) of a basis of normal tensors in canonical form II, with both weights
equal to one (`isBNTCanonicalForm_overlappingBlockSector`,
`reindex_toTensor_overlappingBlockSector`), and the pairs and weights of the approximating
state are those of this canonical form (`embeddedFixedPointPair_overlappingBlockSector`).

The transfer maps of one-dimensional blocks are the identity, so the hypothesis on the
subleading eigenvalue that defines `ξ_diag` holds for every `λ₂`, and `e^{-γ/ξ_diag}` can be
any number in `(0, 1)`. When it is below `9/25`, the printed rate decays faster than the error:
along `q = M`, `N = q²`, which satisfies `q = o(N)`, the error exceeds
`C (N/q) e^{-γ q/ξ_diag} exp(C (N/q) e^{-γ q/ξ_diag})` for every `C`
(`not_approximationError_le_overlappingBlockTensor`). The error is set by the overlap
`s = (3/5)^q` of the blocks, through `s²`, which the source's estimate relegates to the term
`O(e^{-N/ξ_offdiag})` that `q = o(N)` removes.

**False source (Lemma 1'(ii), overlapping blocks):** the block form of eq. (S5) fails when the
`q`-site states of distinct blocks are not orthogonal, and the bound of Lemma 1'(ii) fails for
the approximating state of eq. (S7) even when every multiplicity is one. Documented in
`docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`.

## Main declarations

* `MPSTensor.overlappingBlockTensor` — the tensor `A⁰ = diag(1, 3/5)`, `A¹ = diag(0, 4/5)`.
* `MPSTensor.nonNormalApproxOverlap_overlappingBlockTensor` — the overlap, for all `q, M ≥ 1`.
* `MPSTensor.le_one_sub_norm_nonNormalApproxOverlap_overlappingBlockTensor`,
  `MPSTensor.one_sub_norm_nonNormalApproxOverlap_overlappingBlockTensor_le` — the error lies
  between `(9/25)^q / 16` and `M (9/25)^q`.
* `MPSTensor.not_approximationError_le_overlappingBlockTensor` — the bound of Lemma 1'(ii)
  fails.
* `MPSTensor.overlappingBlockSector`, `MPSTensor.isBNTCanonicalForm_overlappingBlockSector`,
  `MPSTensor.reindex_toTensor_overlappingBlockSector` — the tensor is, after ordering its bond
  coordinates, the canonical form of eq. (S2) of a basis of normal tensors.
* `MPSTensor.isBNTCanonicalForm_and_not_approximationError_le_overlappingBlock` — the tensor
  satisfies every hypothesis of Lemma 1'(ii), and the bound fails for it.

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

/-- The blocks are in the gauge `∑ᵢ |aᵢ|² = 1` of arXiv:2307.01696, eq. `eq:Ek_decomp`. -/
theorem overlappingBlockBasis_norm (j : Fin 2) :
    ∑ i, star (overlappingBlockBasis j i 0 0) * overlappingBlockBasis j i 0 0 = 1 := by
  fin_cases j <;>
    simp [overlappingBlockBasis, overlappingBlockDiag, Fin.sum_univ_two, map_ofNat]
  norm_num

/-- The transfer maps of the blocks have no eigenvalue other than `1`, so the hypothesis on the
subleading eigenvalue that defines the correlation length `ξ_diag` of arXiv:2307.01696,
Lemma 1'(ii), holds for every `λ₂`. -/
theorem norm_le_of_hasEigenvalue_transferMap_overlappingBlockBasis (j : Fin 2) (lam₂ μ : ℂ)
    (h : Module.End.HasEigenvalue (Kraus.transferMap (overlappingBlockBasis j)) μ)
    (hμ : μ ≠ 1) : ‖μ‖ ≤ ‖lam₂‖ :=
  norm_le_of_hasEigenvalue_transferMap_of_dim_one _ (overlappingBlockBasis_norm j) lam₂ μ h hμ

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
    simp only [overlappingBlockSqrt, Fin.zero_eta, Fin.isValue, Fin.mk_one, mul_apply, of_apply,
      cons_val', cons_val_fin_one, cons_val_zero, cons_val_one, Fin.sum_univ_two] <;>
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
every number of blocks `M ≥ 1`, `⟨φ~_N|φ_N⟩ = (u^M + v^M) / (1 + s^M)^{1/2}`. -/
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
    simp only [Real.sqrt_one, ofReal_one, inv_one, Nat.ofNat_nonneg, Real.sqrt_mul, ofReal_mul,
      _root_.mul_inv_rev, one_mul, Nat.succ_eq_add_one, Nat.reduceAdd, invSqrtTwo, Fin.isValue,
      cons_val_zero, star_inv₀, RCLike.star_def, conj_ofReal, of_apply, cons_val', cons_val_fin_one,
      cons_val_one, ofReal_div, ofReal_add, ofReal_pow]
    have hs2 : Real.sqrt 2 ≠ 0 := by positivity
    have hs : Real.sqrt (1 + overlappingBlockOverlap q ^ M) ≠ 0 := by
      have := overlap_nonneg q; positivity
    have hsq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
      exact_mod_cast Complex.ofReal_sqrt_sq 2 (by norm_num)
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

/-- **The error for overlapping blocks is at most `M (9/25)^q`**: together with
`le_one_sub_norm_nonNormalApproxOverlap_overlappingBlockTensor`, the error of the approximating
state of arXiv:2307.01696, eq. (S7), for `overlappingBlockTensor` lies between `(9/25)^q / 16`
(for `M ≥ 3`) and `M (9/25)^q`, so it tends to zero whenever `(N/q) τ^{2q} → 0`, with
`τ = 3/5` the eigenvalue of the mixed transfer map of the two blocks. The construction of the
source converges; the rate `e^{-γ q/ξ_diag}` of Lemma 1'(ii) does not describe it. -/
theorem one_sub_norm_nonNormalApproxOverlap_overlappingBlockTensor_le {q M : ℕ} (hq : q ≠ 0)
    (hM : M ≠ 0) :
    1 - ‖nonNormalApproxOverlap overlappingBlockTensor q M
        (ghzAmplitude (bntWeight overlappingBlockWeight (M * q)))
        (fun j => embedPair (fun _ : Fin 1 => j)
          (fixedPointPair (1 : Matrix (Fin 1) (Fin 1) ℂ)))‖ ≤ M * (9 / 25 : ℝ) ^ q := by
  rw [nonNormalApproxOverlap_overlappingBlockTensor hq hM, Complex.norm_real]
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
  have hs2 : (9 / 25 : ℝ) ^ q = s ^ 2 := by
    rw [show s = (3 / 5 : ℝ) ^ q from rfl, ← pow_mul, mul_comm, pow_mul]; norm_num
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hM
  rw [Real.norm_eq_abs, hs2]
  have hden0 : 0 < Real.sqrt (1 + s ^ M) := Real.sqrt_pos.2 (by positivity)
  rcases Nat.lt_or_ge M 2 with hM1 | hM2
  · -- One block: `u + v = √(1 + s)`, and the overlap is one.
    obtain rfl : M = 1 := by omega
    have huv1 : u + v = Real.sqrt (1 + s) := by
      simp only [u, v, overlappingBlockU, overlappingBlockV]; ring
    rw [pow_one, pow_one, pow_one, huv1, div_self (Real.sqrt_pos.2 (by linarith)).ne', abs_one]
    push_cast
    nlinarith [sq_nonneg s]
  · -- `u ≥ 1 - s²/2`, so `u^M ≥ 1 - M s²/2`, and `√(1 + s^M) ≤ 1 + s²/2`.
    have hab : 1 - s ^ 2 ≤ Real.sqrt (1 + s) * Real.sqrt (1 - s) := by
      rw [← Real.sqrt_mul (by linarith)]
      refine Real.le_sqrt_of_sq_le ?_
      have ht0 : 0 ≤ 1 - s ^ 2 := by nlinarith
      have ht1 : 1 - s ^ 2 ≤ 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left ht1 ht0]
    have hu2 : u ^ 2 = (1 + Real.sqrt (1 + s) * Real.sqrt (1 - s)) / 2 := by
      rw [show u = (Real.sqrt (1 + s) + Real.sqrt (1 - s)) / 2 from rfl]
      linear_combination (ha + hb) / 4
    have hu2' : 1 - s ^ 2 / 2 ≤ u ^ 2 := by rw [hu2]; linarith
    have hu : 1 - s ^ 2 / 2 ≤ u := by nlinarith
    have hbern : 1 + (M : ℝ) * (u - 1) ≤ u ^ M := by
      have := one_add_mul_le_pow (a := u - 1) (by linarith) M
      simpa using this
    have hsM : s ^ M ≤ s ^ 2 := pow_le_pow_of_le_one hs0 hs1 hM2
    have hden : Real.sqrt (1 + s ^ M) ≤ 1 + s ^ 2 / 2 := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [pow_nonneg hs0 M, sq_nonneg (s ^ 2)]
    have hnum : u ^ M ≤ u ^ M + v ^ M := le_add_of_nonneg_right (pow_nonneg hv0 M)
    have hq' : 0 ≤ (u ^ M + v ^ M) / Real.sqrt (1 + s ^ M) := by positivity
    rw [abs_of_nonneg hq']
    rcases le_or_gt 1 ((M : ℝ) * s ^ 2) with hbig | hsmall
    · have : 0 ≤ (u ^ M + v ^ M) / Real.sqrt (1 + s ^ M) := hq'
      linarith
    · have hpos : 0 ≤ 1 + (M : ℝ) * (u - 1) := by nlinarith
      have hlow : (1 + (M : ℝ) * (u - 1)) / (1 + s ^ 2 / 2) ≤
          (u ^ M + v ^ M) / Real.sqrt (1 + s ^ M) :=
        div_le_div₀ (by positivity) (hbern.trans hnum) hden0 hden
      have hfrac : 1 - (M : ℝ) * s ^ 2 ≤ (1 + (M : ℝ) * (u - 1)) / (1 + s ^ 2 / 2) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left hu (by positivity : (0 : ℝ) ≤ M),
          sq_nonneg s, mul_nonneg (by positivity : (0 : ℝ) ≤ M) (sq_nonneg s)]
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

/-! ## The tensor satisfies the hypotheses of Lemma 1'(ii) -/

/-- The canonical form of arXiv:2307.01696, eq. (S2), of `overlappingBlockTensor`: the basis of
the two one-dimensional normal blocks `A_1 = (1, 0)` and `A_2 = (3/5, 4/5)`, each of
multiplicity one with weight `μ_{j,1} = 1`. -/
noncomputable abbrev overlappingBlockSector : SectorDecomposition 2 where
  basisCount := 2
  basisDim := fun _ => 1
  basis := overlappingBlockBasis
  sectors :=
    { copies := overlappingBlockMult
      copies_pos := fun j => by fin_cases j <;> simp [overlappingBlockMult]
      weight := overlappingBlockWeight
      weight_ne_zero := fun _ _ => one_ne_zero }

/-- The coefficients `βⱼ = ∑ₖ μ_{j,k}^N` of the canonical form (arXiv:2307.01696, eq. (S4)). -/
theorem coeff_overlappingBlockSector (N : ℕ) :
    overlappingBlockSector.coeff N = bntWeight overlappingBlockWeight N :=
  rfl

/-- The states `|0⋯0⟩` and `(3/5 |0⟩ + 4/5 |1⟩)^{⊗N}` of the two blocks are linearly independent
on every ring of `N ≥ 1` sites, although not orthogonal. This is the basis-of-normal-tensors
property of arXiv:2307.01696, eq. (S2). -/
theorem hasBNTSectorData_overlappingBlockSector : HasBNTSectorData overlappingBlockSector := by
  refine ⟨0, fun N hN => ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hval : ∀ i : Fin 2, ∑ j : Fin 2, g j * overlappingBlockBasis j i 0 0 ^ N = 0 := fun i => by
    have := congrArg (fun v => v (fun _ : Fin N => i)) hg
    simpa [-mpv_eq, mpv_of_dim_one, Fin.sum_univ_two] using this
  have h1 : g 1 = 0 := by
    simpa [Fin.sum_univ_two, overlappingBlockBasis, overlappingBlockDiag, zero_pow hN.ne']
      using hval 1
  have h0 : g 0 = 0 := by
    simpa [Fin.sum_univ_two, overlappingBlockBasis, overlappingBlockDiag, h1] using hval 0
  intro j
  fin_cases j
  · exact h0
  · exact h1

/-- **The canonical form of `overlappingBlockTensor` is a basis of normal tensors**
(arXiv:2307.01696, eq. (S2)): the blocks are irreducible, left-canonical, with normalized
self-overlap, their states are linearly independent, they are not related by a gauge
transformation and a phase, and every weight is `μ_{j,1} = 1`. -/
theorem isBNTCanonicalForm_overlappingBlockSector : IsBNTCanonicalForm overlappingBlockSector where
  basis_dim_pos := fun _ => Nat.one_pos
  basis_irreducible := fun j => isIrreducibleTensor_of_bondDim_one (overlappingBlockBasis j)
  basis_left_canonical := fun j => isLeftCanonical_of_dim_one _ (overlappingBlockBasis_norm j)
  basis_normalized_self_overlap := fun j =>
    tendsto_mpvOverlap_self_of_dim_one _ (overlappingBlockBasis_norm j)
  bnt_data := hasBNTSectorData_overlappingBlockSector
  basis_distinct := fun j k hjk h => by
    have hc : cast (congr_arg (MPSTensor 2) h) (overlappingBlockSector.basis j) =
        overlappingBlockBasis j :=
      cast_eq _ _
    rw [hc]
    refine not_gaugePhaseEquiv_of_dim_one 1 ?_
    fin_cases j <;> fin_cases k <;> simp_all [overlappingBlockBasis, overlappingBlockDiag]
  weight_norm_le_one := fun _ _ => by
    change ‖(1 : ℂ)‖ ≤ 1
    simp
  weight_unit_exists := ⟨(0 : Fin 2), ⟨0, by decide⟩, by change ‖(1 : ℂ)‖ = 1; simp⟩

/-- The bond coordinates of the two blocks in the canonical form. -/
noncomputable def overlappingBlockCopyCoord : Fin 2 → Fin overlappingBlockSector.totalDim :=
  ![overlappingBlockSector.copyCoord 0 ⟨0, by decide⟩ ⟨0, Nat.one_pos⟩,
    overlappingBlockSector.copyCoord 1 ⟨0, by decide⟩ ⟨0, Nat.one_pos⟩]

/-- The canonical form has bond dimension two, the sum `∑ⱼ m_j D_j` of the bond dimensions of
the copies of the blocks in arXiv:2307.01696, eq. (S2). -/
theorem totalDim_overlappingBlockSector : overlappingBlockSector.totalDim = 2 := by
  have h : overlappingBlockSector.totalCopies = 2 := by
    simp [SectorDecomposition.totalCopies, SectorDecomposition.copies, overlappingBlockMult,
      Fin.sum_univ_two]
  simp only [SectorDecomposition.totalDim, SectorDecomposition.flatDim, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, h]

/-- The bond coordinates of the copies of the blocks exhaust the bond coordinates of the
canonical form of arXiv:2307.01696, eq. (S2), each exactly once. -/
theorem bijective_overlappingBlockCopyCoord : Function.Bijective overlappingBlockCopyCoord := by
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨fun x y hxy => ?_, by
    simp [totalDim_overlappingBlockSector]⟩
  fin_cases x <;> fin_cases y <;>
    first
    | rfl
    | (exfalso
       exact absurd (congrArg Sigma.fst (overlappingBlockSector.sigma_eq_of_copyCoord_eq hxy))
         (by decide))

/-- The ordering of the bond coordinates of the canonical form under which its assembled tensor
is `overlappingBlockTensor`: a permutation of the bond basis, which is a gauge
transformation. -/
noncomputable def overlappingBlockEquiv : Fin overlappingBlockSector.totalDim ≃ Fin 2 :=
  (Equiv.ofBijective _ bijective_overlappingBlockCopyCoord).symm

/-- The ordering of the bond coordinates of the canonical form of arXiv:2307.01696, eq. (S2),
sends the coordinate `x` to the bond coordinate of the `x`-th copy. -/
theorem overlappingBlockEquiv_symm_apply (x : Fin 2) :
    overlappingBlockEquiv.symm x = overlappingBlockCopyCoord x :=
  rfl

/-- **`overlappingBlockTensor` is the canonical form** `⊕ⱼ μ_{j,1} A_j` of arXiv:2307.01696,
eq. (S2), of `overlappingBlockSector`, after ordering the bond coordinates. -/
theorem reindex_toTensor_overlappingBlockSector (i : Fin 2) :
    reindex overlappingBlockEquiv overlappingBlockEquiv (overlappingBlockSector.toTensor i) =
      overlappingBlockTensor i := by
  ext x y
  rw [reindex_apply, submatrix_apply, overlappingBlockEquiv_symm_apply,
    overlappingBlockEquiv_symm_apply]
  fin_cases x <;> fin_cases y <;>
    simp only [overlappingBlockCopyCoord, Fin.zero_eta, Fin.mk_one, cons_val_zero,
      cons_val_one] <;>
    first
    | (rw [SectorDecomposition.toTensor_copyCoord]
       fin_cases i <;> simp [SectorDecomposition.weight, overlappingBlockWeight,
         overlappingBlockBasis, overlappingBlockDiag])
    | (rw [SectorDecomposition.toTensor_copyCoord_of_ne _ _ (by simp)]
       fin_cases i <;> simp)

/-- The fixed-point pairs of the blocks of the canonical form
(`SectorDecomposition.embeddedFixedPointPair`, with the fixed point `σ_j = 1` of the
one-dimensional block) are the pairs placed on the coordinate `j`. -/
theorem embeddedFixedPointPair_overlappingBlockSector (j : Fin 2) (p : Fin 2 × Fin 2) :
    overlappingBlockSector.embeddedFixedPointPair (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℂ))
        (fun j => ⟨0, overlappingBlockSector.copies_pos j⟩) j
        (overlappingBlockEquiv.symm p.1, overlappingBlockEquiv.symm p.2) =
      embedPair (fun _ : Fin 1 => j) (fixedPointPair (1 : Matrix (Fin 1) (Fin 1) ℂ)) p := by
  have hc : overlappingBlockSector.copyCoord j ⟨0, overlappingBlockSector.copies_pos j⟩ =
      fun _ : Fin 1 => overlappingBlockEquiv.symm j := by
    funext a
    obtain rfl : a = 0 := Subsingleton.elim _ _
    rw [overlappingBlockEquiv_symm_apply]
    fin_cases j <;> rfl
  rw [SectorDecomposition.embeddedFixedPointPair, hc, embedPair_symm_comp]
  simp

/-- **Lemma 1'(ii) of arXiv:2307.01696 fails for a tensor satisfying all its hypotheses, with
every multiplicity one.** The tensor `A⁰ = diag(1, 3/5)`, `A¹ = diag(0, 4/5)` is, after
ordering its bond coordinates, the canonical form `⊕ⱼ μ_{j,1} A_j` of eq. (S2) of a basis of two
normal blocks in canonical form II, with weights `μ_{j,1} = 1` (`IsBNTCanonicalForm`,
normality, and the diagonal positive-definite fixed point `1` of each block), whose states
"produce orthogonal vectors in the thermodynamic limit" (arXiv:2307.01696, line 973). The
transfer maps of the blocks have no eigenvalue other than `1`, so every `λ₂` bounds their
subleading eigenvalues. When `e^{-γ/ξ_diag} < 9/25`, for the approximating state of eq. (S7),
built from the coefficients `βⱼ = ∑ₖ μ_{j,k}^N` and the pairs of that same fixed point `1`, and
for every constant `C`, there is `q ≥ 3` such that, with `M = q` and `N = q²` (so `q = o(N)`
along this sequence) and `y = (N/q) e^{-γ q/ξ_diag}`, the error exceeds `C y e^{C y}`. -/
theorem isBNTCanonicalForm_and_not_approximationError_le_overlappingBlock :
    IsBNTCanonicalForm overlappingBlockSector ∧
      (∀ j k, j ≠ k → Tendsto (fun N : ℕ =>
        mpvOverlap (overlappingBlockSector.basis j) (overlappingBlockSector.basis k) N)
          atTop (𝓝 0)) ∧
      (∀ j, IsNormalTensor (overlappingBlockSector.basis j)) ∧
      (∀ j, (1 : Matrix (Fin 1) (Fin 1) ℂ).PosDef ∧ (1 : Matrix (Fin 1) (Fin 1) ℂ).IsDiag ∧
        Kraus.transferMap (overlappingBlockSector.basis j) 1 = 1) ∧
      (∀ i, reindex overlappingBlockEquiv overlappingBlockEquiv
        (overlappingBlockSector.toTensor i) = overlappingBlockTensor i) ∧
      (∀ j (lam₂ μ : ℂ),
        Module.End.HasEigenvalue (Kraus.transferMap (overlappingBlockSector.basis j)) μ →
          μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖) ∧
      ∀ {lam₂ : ℂ} {γ : ℝ}, Real.exp (-γ / correlationLength lam₂) < 9 / 25 → ∀ C : ℝ,
        ∃ q : ℕ, 3 ≤ q ∧
          C * (q * Real.exp (-γ * q / correlationLength lam₂)) *
              Real.exp (C * (q * Real.exp (-γ * q / correlationLength lam₂))) <
            1 - ‖nonNormalApproxOverlap overlappingBlockTensor q q
              (ghzAmplitude (overlappingBlockSector.coeff (q * q)))
              (fun j p => overlappingBlockSector.embeddedFixedPointPair
                (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℂ))
                (fun j => ⟨0, overlappingBlockSector.copies_pos j⟩) j
                (overlappingBlockEquiv.symm p.1, overlappingBlockEquiv.symm p.2))‖ := by
  refine ⟨isBNTCanonicalForm_overlappingBlockSector,
    fun _ _ hjk => isBNTCanonicalForm_overlappingBlockSector.cross_overlap_basis_tendsto_zero hjk,
    fun j => isNormalTensor_of_dim_one _ (overlappingBlockBasis_norm j),
    fun j => posDef_isDiag_transferMap_one_of_dim_one _ (overlappingBlockBasis_norm j),
    reindex_toTensor_overlappingBlockSector,
    norm_le_of_hasEigenvalue_transferMap_overlappingBlockBasis, fun hr C => ?_⟩
  simp only [embeddedFixedPointPair_overlappingBlockSector, coeff_overlappingBlockSector]
  exact not_approximationError_le_overlappingBlockTensor hr C

end MPSTensor
