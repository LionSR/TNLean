/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ComplexSqrt
import TNLean.MPS.Preparation.DiagonalPolar

/-!
# The approximating state fails for a block of multiplicity two

Malz, Styliaris, Wei, and Cirac (arXiv:2307.01696, Supplemental Material, "Proof of Lemma 1 and
extension to non-normal tensors") write a tensor as `Aⁱ = ⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_jⁱ`
(eq. (S2)), assert that the positive part of the blocked tensor has the block form
`P = ⊕ⱼ diag(μ_{j,1}^q, …, μ_{j,m_j}^q) ⊗ P_j` (eq. (S5)), and approximate the state on
`N = qM` sites by `V^{⊗M} ∑ⱼ βⱼ |Ω_j⟩` (eq. (S7)), with `βⱼ = ∑ₖ μ_{j,k}^N`. Lemma 1'(ii)
bounds the error of this state by `O((N/q) e^{-γ q/ξ_diag})` for `q = o(N)`.

This file evaluates the construction for the tensor with two one-dimensional normal blocks,
`A_1 = (1, 0)` with multiplicity `m_1 = 2` and weights `μ_1 = (1, 1)`, and `A_2 = (0, 1)` with
`m_2 = 1`, so that `A⁰ = diag(1, 1, 0)` and `A¹ = diag(0, 0, 1)`. The target is proportional to
`2|0⋯0⟩ + |1⋯1⟩`. The positive part restricted to the two copies of the first block is the
rank-one matrix `(1/√2) [[1, 1], [1, 1]]` rather than `diag(1, 1)` times a positive part, and
`V` maps the pair of the first block, placed on one copy, to `|0⋯0⟩/√2`. For every block length
`q ≥ 1` and every number of blocks `M ≥ 1` the overlap is
`(4 · 2^{-M/2} + 1) / (√5 (4 · 2^{-M} + 1)^{1/2})`
(`nonNormalApproxOverlap_repeatedBlockTensor`), which tends to `1/√5` as `M → ∞`
(`tendsto_norm_nonNormalApproxOverlap_repeatedBlockTensor`) and does not depend on `q`.

Both blocks are one-dimensional, so their transfer maps are the identity and have no eigenvalue
other than `1` (`hasEigenvalue_transferMap_repeatedBlock`): the hypothesis on the subleading
eigenvalue that defines `ξ_diag` holds for every `λ₂`, and `e^{-γ/ξ_diag}` can be any number in
`(0, 1)`. Along `q = M`, `N = M²`, which satisfies `q = o(N)`, the error stays above `1/2` while
`(N/q) e^{-γ q/ξ_diag}` tends to zero (`not_approximationError_le_repeatedBlockTensor`).

**False source (Lemma 1'(ii), multiplicity):** the approximating state of eq. (S7) does not
approximate `|φ_N⟩` when a block has multiplicity `m_j ≥ 2`, and the bound of Lemma 1'(ii)
fails. Documented in `docs/paper-gaps/mswc24_multiplicity_fixed_point.tex`.

## Main declarations

* `MPSTensor.repeatedBlockTensor` — the tensor `A⁰ = diag(1, 1, 0)`, `A¹ = diag(0, 0, 1)`.
* `MPSTensor.nonNormalApproxOverlap_repeatedBlockTensor` — the overlap, for all `q, M ≥ 1`.
* `MPSTensor.tendsto_norm_nonNormalApproxOverlap_repeatedBlockTensor` — it tends to `1/√5`.
* `MPSTensor.not_approximationError_le_repeatedBlockTensor` — the bound of Lemma 1'(ii) fails.

## References

* [MSWC23] D. Malz, G. Styliaris, Z.-Y. Wei, J. I. Cirac,
  *Preparation of matrix product states with log-depth quantum circuits*,
  arXiv:2307.01696, Supplemental Material, eqs. (S2)–(S7) and Lemma 1'(ii).
-/

open scoped BigOperators Matrix ComplexOrder
open Matrix Filter Topology Complex

namespace MPSTensor

/-- The diagonal entries of `A⁰ = diag(1, 1, 0)` and `A¹ = diag(0, 0, 1)`. -/
def repeatedBlockDiag : Fin 2 → Fin 3 → ℂ := ![![1, 1, 0], ![0, 0, 1]]

/-- The tensor `A⁰ = diag(1, 1, 0)`, `A¹ = diag(0, 0, 1)`: the canonical form of
arXiv:2307.01696, eq. (S2), with the normal block `A_1 = (1, 0)` of multiplicity two and
weights `(1, 1)`, and the normal block `A_2 = (0, 1)` of multiplicity one. -/
abbrev repeatedBlockTensor : MPSTensor 2 3 := fun i => diagonal (repeatedBlockDiag i)

/-- The two one-dimensional normal blocks `A_1 = (1, 0)` and `A_2 = (0, 1)`, each in the gauge
`∑ᵢ |aᵢ|² = 1` of arXiv:2307.01696, eq. `eq:Ek_decomp`. -/
def repeatedBlockBasis (j : Fin 2) : MPSTensor 2 1 :=
  fun i => of fun _ _ => (![![1, 0], ![0, 1]] : Fin 2 → Fin 2 → ℂ) j i

/-- The transfer maps of the blocks have no eigenvalue other than `1`, so the hypothesis on the
subleading eigenvalue that defines the correlation length `ξ_diag` of arXiv:2307.01696,
Lemma 1'(ii), holds for every `λ₂`. -/
theorem norm_le_of_hasEigenvalue_transferMap_repeatedBlockBasis (j : Fin 2) (lam₂ μ : ℂ)
    (h : Module.End.HasEigenvalue (Kraus.transferMap (repeatedBlockBasis j)) μ)
    (hμ : μ ≠ 1) : ‖μ‖ ≤ ‖lam₂‖ := by
  refine norm_le_of_hasEigenvalue_transferMap_of_dim_one _ ?_ lam₂ μ h hμ
  fin_cases j <;> simp [repeatedBlockBasis, Fin.sum_univ_two]

/-- The multiplicities `m = (2, 1)` of the two blocks. -/
def repeatedBlockMult : Fin 2 → ℕ := ![2, 1]

/-- The weights `μ_{j,k} = 1` of every copy. -/
def repeatedBlockWeight : (j : Fin 2) → Fin (repeatedBlockMult j) → ℂ := fun _ _ => 1

/-- The bond coordinates of the pairs: the first copy of the first block and the second block. -/
def repeatedBlockCoord : Fin 2 → Fin 3 := ![0, 2]

/-- The weights `βⱼ = ∑ₖ μ_{j,k}^N = m_j` of arXiv:2307.01696, eq. (S4). -/
theorem bntWeight_repeatedBlockWeight (N : ℕ) :
    bntWeight repeatedBlockWeight N = ![2, 1] := by
  funext j
  fin_cases j <;> simp [bntWeight, repeatedBlockWeight, repeatedBlockMult] <;> norm_num

/-- The normalized weights `α^{(N)} = (2, 1)/√5`. -/
theorem ghzAmplitude_repeatedBlock (N : ℕ) :
    ghzAmplitude (bntWeight repeatedBlockWeight N) =
      ![2 / (Real.sqrt 5 : ℂ), 1 / (Real.sqrt 5 : ℂ)] := by
  rw [bntWeight_repeatedBlockWeight]
  have h : (∑ l, ‖(![2, 1] : Fin 2 → ℂ) l‖ ^ 2) = 5 := by
    simp [Fin.sum_univ_two]; norm_num
  funext j
  rw [ghzAmplitude, h]
  fin_cases j <;> simp

/-- The Gram matrix of the blocked tensor, for `q ≥ 1`. -/
theorem diagGram_repeatedBlockDiag {q : ℕ} (hq : q ≠ 0) :
    diagGram repeatedBlockDiag q = !![1, 1, 0; 1, 1, 0; 0, 0, 1] := by
  ext e e'
  fin_cases e <;> fin_cases e' <;>
    simp [diagGram, repeatedBlockDiag, Fin.sum_univ_two, zero_pow hq]

/-- The square root of the Gram matrix: `(1/√2) [[1, 1], [1, 1]] ⊕ [1]`. -/
noncomputable def repeatedBlockSqrt : Matrix (Fin 3) (Fin 3) ℂ :=
  !![invSqrtTwo, invSqrtTwo, 0; invSqrtTwo, invSqrtTwo, 0; 0, 0, 1]

/-- The projector onto its range. -/
noncomputable def repeatedBlockProj : Matrix (Fin 3) (Fin 3) ℂ :=
  !![2⁻¹, 2⁻¹, 0; 2⁻¹, 2⁻¹, 0; 0, 0, 1]

private lemma invSqrtTwo_nonneg : (0 : ℂ) ≤ invSqrtTwo := by
  rw [invSqrtTwo, ← Complex.ofReal_inv]
  exact Complex.zero_le_real.mpr (by positivity)

private lemma two_inv_add_two_inv : (2⁻¹ : ℂ) + 2⁻¹ = 1 := by norm_num

theorem posSemidef_repeatedBlockSqrt : repeatedBlockSqrt.PosSemidef := by
  have h : repeatedBlockSqrt = invSqrtTwo • vecMulVec ![1, 1, 0] (star ![1, 1, 0]) +
      vecMulVec ![0, 0, 1] (star ![0, 0, 1]) := by
    ext e e'
    fin_cases e <;> fin_cases e' <;> simp [repeatedBlockSqrt, vecMulVec]
  rw [h]
  exact ((posSemidef_vecMulVec_self_star _).smul invSqrtTwo_nonneg).add
    (posSemidef_vecMulVec_self_star _)

theorem repeatedBlockSqrt_mul_self {q : ℕ} (hq : q ≠ 0) :
    repeatedBlockSqrt * repeatedBlockSqrt = diagGram repeatedBlockDiag q := by
  rw [diagGram_repeatedBlockDiag hq]
  ext e e'
  fin_cases e <;> fin_cases e' <;>
    simp [repeatedBlockSqrt, mul_apply, Fin.sum_univ_three, invSqrtTwo_mul_self,
      two_inv_add_two_inv]

/-- The positive part of the `q`-site blocked tensor, `P = J Q Jᴴ`. -/
theorem polarPos_repeatedBlockTensor {q : ℕ} (hq : q ≠ 0) :
    polarPos (physicalMatrix (blockTensor repeatedBlockTensor q)) =
      diagPairEmbedding (Fin 3) * repeatedBlockSqrt * (diagPairEmbedding (Fin 3))ᴴ :=
  polarPos_physicalMatrix_blockTensor_diagonal repeatedBlockDiag q
    posSemidef_repeatedBlockSqrt (repeatedBlockSqrt_mul_self hq)

/-- The support projector of the `q`-site blocked tensor, `Π = J E Jᴴ`. -/
theorem polarSupport_repeatedBlockTensor {q : ℕ} (hq : q ≠ 0) :
    polarSupport (physicalMatrix (blockTensor repeatedBlockTensor q)) =
      diagPairEmbedding (Fin 3) * repeatedBlockProj * (diagPairEmbedding (Fin 3))ᴴ := by
  refine polarSupport_physicalMatrix_blockTensor_diagonal repeatedBlockDiag q
    posSemidef_repeatedBlockSqrt (repeatedBlockSqrt_mul_self hq) (R :=
      !![invSqrtTwo, 0, 0; 0, invSqrtTwo, 0; 0, 0, 1]) ?_ ?_ ?_ ?_
  · refine Matrix.IsHermitian.ext fun e e' => ?_
    fin_cases e <;> fin_cases e' <;> simp [repeatedBlockProj]
  all_goals
    ext e e'
    fin_cases e <;> fin_cases e' <;>
      simp [repeatedBlockProj, repeatedBlockSqrt, mul_apply, Fin.sum_univ_three,
        invSqrtTwo_mul_self, two_inv_add_two_inv]
  all_goals ring

/-- **The overlap for a repeated block** (arXiv:2307.01696, eq. (S7)). For the tensor
`A⁰ = diag(1, 1, 0)`, `A¹ = diag(0, 0, 1)`, the fixed-point pairs of the two one-dimensional
blocks placed on the first copy of the first block and on the second block, the coefficients
`α^{(N)}` of the weights `β = (2, 1)`, every block length `q ≥ 1` and every number of blocks
`M ≥ 1`,
`⟨φ̃_N|φ_N⟩ = (4 · 2^{-M/2} + 1) / (√5 (4 · 2^{-M} + 1)^{1/2})`, independently of `q`. -/
theorem nonNormalApproxOverlap_repeatedBlockTensor {q M : ℕ} (hq : q ≠ 0) (hM : M ≠ 0) :
    nonNormalApproxOverlap repeatedBlockTensor q M
        (ghzAmplitude (bntWeight repeatedBlockWeight (M * q)))
        (fun j => embedPair (fun _ : Fin 1 => repeatedBlockCoord j)
          (fixedPointPair (1 : Matrix (Fin 1) (Fin 1) ℂ))) =
      (((4 * (Real.sqrt 2)⁻¹ ^ M + 1) /
        (Real.sqrt 5 * Real.sqrt (4 * (2⁻¹ : ℝ) ^ M + 1)) : ℝ) : ℂ) := by
  simp only [embedPair_fixedPointPair_one]
  rw [show repeatedBlockTensor = fun i => diagonal (repeatedBlockDiag i) from rfl]
  set X : ℝ := (4 * (2⁻¹ : ℝ) ^ M + 1) / 5
  rw [nonNormalApproxOverlap_diagonal repeatedBlockDiag q M _ repeatedBlockCoord (X := X)
    (Y := 5)]
  · rw [polarPos_repeatedBlockTensor hq, ghzAmplitude_repeatedBlock]
    simp only [diagPairEmbedding_mul_mul_conjTranspose_apply, Fin.sum_univ_two,
      Fin.sum_univ_three, repeatedBlockCoord, repeatedBlockSqrt]
    simp [zero_pow hM, invSqrtTwo]
    have h5 : Real.sqrt 5 ≠ 0 := by positivity
    have hX : Real.sqrt X = Real.sqrt (4 * (2⁻¹ : ℝ) ^ M + 1) / Real.sqrt 5 := by
      rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 5)]
    have hs : Real.sqrt (4 * (2⁻¹ : ℝ) ^ M + 1) ≠ 0 := by positivity
    rw [hX]
    push_cast
    field_simp
    ring
  · rw [polarSupport_repeatedBlockTensor hq, ghzAmplitude_repeatedBlock]
    simp only [diagPairEmbedding_mul_mul_conjTranspose_apply, Fin.sum_univ_two,
      repeatedBlockCoord, repeatedBlockProj]
    simp [zero_pow hM, X]
    have h5 : ((Real.sqrt 5 : ℝ) : ℂ) * (Real.sqrt 5 : ℝ) = 5 := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
    field_simp
    ring_nf
    rw [show ((Real.sqrt 5 : ℝ) : ℂ) ^ 2 = 5 by rw [sq, h5]]
    ring
  · rw [diagGram_repeatedBlockDiag hq]
    simp [Fin.sum_univ_three, zero_pow hM]
    norm_num

/-- The closed form of the overlap in `nonNormalApproxOverlap_repeatedBlockTensor`. -/
noncomputable def repeatedBlockOverlap (M : ℕ) : ℝ :=
  (4 * (Real.sqrt 2)⁻¹ ^ M + 1) / (Real.sqrt 5 * Real.sqrt (4 * (2⁻¹ : ℝ) ^ M + 1))

theorem tendsto_repeatedBlockOverlap :
    Tendsto repeatedBlockOverlap atTop (𝓝 (1 / Real.sqrt 5)) := by
  have h1 : Tendsto (fun M : ℕ => (Real.sqrt 2)⁻¹ ^ M) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      (inv_lt_one_of_one_lt₀ (by rw [Real.lt_sqrt] <;> norm_num))
  have h2 : Tendsto (fun M : ℕ => (2⁻¹ : ℝ) ^ M) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hnum := (h1.const_mul 4).add_const 1
  have hden := tendsto_const_nhds (x := Real.sqrt 5) |>.mul
    ((Real.continuous_sqrt.tendsto _).comp ((h2.const_mul 4).add_const 1))
  have := hnum.div hden (by positivity)
  simpa [repeatedBlockOverlap, Function.comp_def] using this

/-- **The overlap tends to `1/√5`** as the number of blocks grows, for every block length
`q ≥ 1`: the approximating state of arXiv:2307.01696, eq. (S7) does not approximate the
target for a block of multiplicity two. -/
theorem tendsto_norm_nonNormalApproxOverlap_repeatedBlockTensor {q : ℕ} (hq : q ≠ 0) :
    Tendsto (fun M : ℕ => ‖nonNormalApproxOverlap repeatedBlockTensor q M
        (ghzAmplitude (bntWeight repeatedBlockWeight (M * q)))
        (fun j => embedPair (fun _ : Fin 1 => repeatedBlockCoord j)
          (fixedPointPair (1 : Matrix (Fin 1) (Fin 1) ℂ)))‖) atTop (𝓝 (1 / Real.sqrt 5)) := by
  refine Tendsto.congr' ?_ tendsto_repeatedBlockOverlap
  filter_upwards [eventually_ge_atTop 1] with M hM
  rw [nonNormalApproxOverlap_repeatedBlockTensor hq (by omega), Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rfl

/-- **Lemma 1'(ii) fails for a repeated block** (arXiv:2307.01696, Supplemental Material,
Lemma 1'(ii), eq. (S12)). The transfer maps of the one-dimensional blocks of
`repeatedBlockTensor` have no eigenvalue other than `1`
(`norm_le_of_hasEigenvalue_transferMap_repeatedBlockBasis`), so every `λ₂` with
`0 < |λ₂| < 1` bounds their subleading eigenvalues. For every such `λ₂`, every `γ > 0`, and
every constant `C` there is `M ≥ 1` such that, with block length `q = M` (`N = M²`, so
`q = o(N)` along this sequence) and `y = (N/q) e^{-γ q/ξ_diag}`, the error of the approximating
state of eq. (S7) exceeds `C y e^{C y}`, and in particular exceeds `C y`. -/
theorem not_approximationError_le_repeatedBlockTensor {lam₂ : ℂ} (h0 : 0 < ‖lam₂‖)
    (h1 : ‖lam₂‖ < 1) {γ : ℝ} (hγ : 0 < γ) (C : ℝ) :
    ∃ M : ℕ, 1 ≤ M ∧
      C * (M * Real.exp (-γ * M / correlationLength lam₂)) *
          Real.exp (C * (M * Real.exp (-γ * M / correlationLength lam₂))) <
        1 - ‖nonNormalApproxOverlap repeatedBlockTensor M M
          (ghzAmplitude (bntWeight repeatedBlockWeight (M * M)))
          (fun j => embedPair (fun _ : Fin 1 => repeatedBlockCoord j)
            (fixedPointPair (1 : Matrix (Fin 1) (Fin 1) ℂ)))‖ := by
  set r := Real.exp (-γ / correlationLength lam₂)
  have hξ := correlationLength_pos h0 h1
  have hr1 : r < 1 := Real.exp_lt_one.mpr (div_neg_of_neg_of_pos (by linarith) hξ)
  have hxq : ∀ M : ℕ, Real.exp (-γ * M / correlationLength lam₂) = r ^ M := fun M => by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have h5 : 1 / Real.sqrt 5 < 1 / 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num), one_mul, one_mul, Real.lt_sqrt] <;>
      norm_num
  obtain ⟨M, ⟨hlt, hov⟩, hM⟩ := (((eventually_mul_pow_mul_exp_lt (Real.exp_pos _).le hr1
    le_rfl C (1 / 2) (by norm_num)).and
    (tendsto_repeatedBlockOverlap.eventually (gt_mem_nhds h5))).and
    (eventually_ge_atTop 1)).exists
  refine ⟨M, hM, ?_⟩
  rw [hxq, nonNormalApproxOverlap_repeatedBlockTensor (by omega) (by omega), Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [one_pow, mul_one] at hlt
  exact hlt.trans (by change _ < 1 - repeatedBlockOverlap M; linarith)

end MPSTensor
