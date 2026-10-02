/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ComplexSqrt
import TNLean.MPS.FundamentalTheorem.SectorBNT.Api
import TNLean.MPS.Preparation.OneDimensionalBlocks

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

The tensor lies in the domain of Lemma 1'(ii): after ordering its bond coordinates it is the
canonical form of eq. (S2) of a basis of normal tensors in canonical form II, with weights
`|μ_{j,k}| ≤ 1`, one of modulus one (`isBNTCanonicalForm_repeatedBlockSector`,
`reindex_toTensor_repeatedBlockSector`), and the pairs and weights of the approximating state
are those of this canonical form (`embeddedFixedPointPair_repeatedBlockSector`).

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
* `MPSTensor.repeatedBlockSector`, `MPSTensor.isBNTCanonicalForm_repeatedBlockSector`,
  `MPSTensor.reindex_toTensor_repeatedBlockSector` — the tensor is, after ordering its bond
  coordinates, the canonical form of eq. (S2) of a basis of normal tensors.
* `MPSTensor.isBNTCanonicalForm_and_not_approximationError_le_repeatedBlock` — the tensor
  satisfies every hypothesis of Lemma 1'(ii), and the bound fails for it.

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

/-- The blocks are in the gauge `∑ᵢ |aᵢ|² = 1` of arXiv:2307.01696, eq. `eq:Ek_decomp`. -/
theorem repeatedBlockBasis_norm (j : Fin 2) :
    ∑ i, star (repeatedBlockBasis j i 0 0) * repeatedBlockBasis j i 0 0 = 1 := by
  fin_cases j <;> simp [repeatedBlockBasis, Fin.sum_univ_two]

/-- The transfer maps of the blocks have no eigenvalue other than `1`, so the hypothesis on the
subleading eigenvalue that defines the correlation length `ξ_diag` of arXiv:2307.01696,
Lemma 1'(ii), holds for every `λ₂`. -/
theorem norm_le_of_hasEigenvalue_transferMap_repeatedBlockBasis (j : Fin 2) (lam₂ μ : ℂ)
    (h : Module.End.HasEigenvalue (Kraus.transferMap (repeatedBlockBasis j)) μ)
    (hμ : μ ≠ 1) : ‖μ‖ ≤ ‖lam₂‖ :=
  norm_le_of_hasEigenvalue_transferMap_of_dim_one _ (repeatedBlockBasis_norm j) lam₂ μ h hμ

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
  fin_cases j <;>
    simp [bntWeight, repeatedBlockWeight] <;> norm_cast

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
        invSqrtTwo_mul_self]
  all_goals ring

/-- **The overlap for a repeated block** (arXiv:2307.01696, eq. (S7)). For the tensor
`A⁰ = diag(1, 1, 0)`, `A¹ = diag(0, 0, 1)`, the fixed-point pairs of the two one-dimensional
blocks placed on the first copy of the first block and on the second block, the coefficients
`α^{(N)}` of the weights `β = (2, 1)`, every block length `q ≥ 1` and every number of blocks
`M ≥ 1`,
`⟨φ~_N|φ_N⟩ = (4 · 2^{-M/2} + 1) / (√5 (4 · 2^{-M} + 1)^{1/2})`, independently of `q`. -/
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
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, one_div, Fin.isValue, cons_val_zero,
      star_div₀, star_ofNat, RCLike.star_def, conj_ofReal, invSqrtTwo, of_apply, cons_val',
      cons_val_fin_one, inv_pow, cons_val_one, cons_val, zero_pow hM, mul_zero, add_zero,
      star_inv₀, one_pow, mul_one, zero_add, ofReal_div, ofReal_add, ofReal_mul, ofReal_ofNat,
      ofReal_inv, ofReal_pow, ofReal_one]
    have h5 : Real.sqrt 5 ≠ 0 := by positivity
    have hX : Real.sqrt X = Real.sqrt (4 * (2⁻¹ : ℝ) ^ M + 1) / Real.sqrt 5 := by
      rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 5)]
    have hs : Real.sqrt (4 * (2⁻¹ : ℝ) ^ M + 1) ≠ 0 := by positivity
    rw [hX]
    push_cast
    rw [← inv_pow (2 : ℝ) M]
    have hT : ((Real.sqrt (4 * (2⁻¹ : ℝ) ^ M + 1) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
    have h5' : ((Real.sqrt 5 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h5
    have h2' : ((Real.sqrt 2 : ℝ) : ℂ) ^ M ≠ 0 :=
      pow_ne_zero _ (by exact_mod_cast (by positivity : Real.sqrt 2 ≠ 0))
    generalize ((Real.sqrt (4 * (2⁻¹ : ℝ) ^ M + 1) : ℝ) : ℂ) = T at hT ⊢
    generalize ((Real.sqrt 5 : ℝ) : ℂ) = F at h5' ⊢
    generalize ((Real.sqrt 2 : ℝ) : ℂ) ^ M = W at h2' ⊢
    field_simp
    ring
  · rw [polarSupport_repeatedBlockTensor hq, ghzAmplitude_repeatedBlock]
    simp only [diagPairEmbedding_mul_mul_conjTranspose_apply, Fin.sum_univ_two,
      repeatedBlockCoord, repeatedBlockProj]
    simp only [inv_pow, ofReal_div, ofReal_add, ofReal_mul, ofReal_ofNat, ofReal_inv,
      ofReal_pow, ofReal_one, Nat.succ_eq_add_one, Nat.reduceAdd, one_div, Fin.isValue,
      cons_val_zero, star_div₀, star_ofNat, RCLike.star_def, conj_ofReal, of_apply, cons_val',
      cons_val_fin_one, cons_val_one, cons_val, zero_pow hM, mul_zero, add_zero, star_inv₀,
      one_pow, mul_one, zero_add, X]
    have h5 : ((Real.sqrt 5 : ℝ) : ℂ) ^ 2 = 5 := by
      exact_mod_cast Complex.ofReal_sqrt_sq 5 (by norm_num)
    field_simp
    ring_nf
    rw [h5]
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
  rw [show (4 * 0 + 1 : ℝ) / (Real.sqrt 5 * Real.sqrt (4 * 0 + 1)) = 1 / Real.sqrt 5 by
    norm_num] at this
  exact this

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
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by linarith) hξ)
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

/-! ## The tensor satisfies the hypotheses of Lemma 1'(ii) -/

/-- The canonical form of arXiv:2307.01696, eq. (S2), with the basis of the two one-dimensional
normal blocks `A_1 = (1, 0)` and `A_2 = (0, 1)`, multiplicities `m_j ≥ 1`, and nonzero weights
`μ_{j,k}`. -/
abbrev repeatedBlockBasisSector (m : Fin 2 → ℕ) (hm : ∀ j, 0 < m j)
    (μ : (j : Fin 2) → Fin (m j) → ℂ) (hμ : ∀ j k, μ j k ≠ 0) : SectorDecomposition 2 where
  basisCount := 2
  basisDim := fun _ => 1
  basis := repeatedBlockBasis
  sectors :=
    { copies := m
      copies_pos := hm
      weight := μ
      weight_ne_zero := hμ }

/-- The states of the two blocks are linearly independent on every ring of `N ≥ 1` sites: they
are `|0⋯0⟩` and `|1⋯1⟩`. This is the basis-of-normal-tensors property of arXiv:2307.01696,
eq. (S2), for every choice of multiplicities and weights. -/
theorem hasBNTSectorData_repeatedBlockBasisSector (m : Fin 2 → ℕ) (hm : ∀ j, 0 < m j)
    (μ : (j : Fin 2) → Fin (m j) → ℂ) (hμ : ∀ j k, μ j k ≠ 0) :
    HasBNTSectorData (repeatedBlockBasisSector m hm μ hμ) := by
  refine ⟨0, fun N hN => ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hval : ∀ i : Fin 2, ∑ j : Fin 2, g j * repeatedBlockBasis j i 0 0 ^ N = 0 := fun i => by
    have := congrArg (fun v => v (fun _ : Fin N => i)) hg
    simpa [-mpv_eq, mpv_of_dim_one, Fin.sum_univ_two] using this
  have h0 : g 0 = 0 := by
    simpa [Fin.sum_univ_two, repeatedBlockBasis, zero_pow hN.ne'] using hval 0
  have h1 : g 1 = 0 := by
    simpa [Fin.sum_univ_two, repeatedBlockBasis, zero_pow hN.ne'] using hval 1
  intro j
  fin_cases j
  · exact h0
  · exact h1

/-- **The canonical form with the blocks `(1, 0)` and `(0, 1)` is a basis of normal tensors**
(arXiv:2307.01696, eq. (S2)) whenever every weight has `|μ_{j,k}| ≤ 1` and one has
`|μ_{j,k}| = 1`: the blocks are irreducible, left-canonical, with normalized self-overlap, their
states are linearly independent, and they are not related by a gauge transformation and a
phase. -/
theorem isBNTCanonicalForm_repeatedBlockBasisSector (m : Fin 2 → ℕ) (hm : ∀ j, 0 < m j)
    (μ : (j : Fin 2) → Fin (m j) → ℂ) (hμ : ∀ j k, μ j k ≠ 0) (hle : ∀ j k, ‖μ j k‖ ≤ 1)
    (hone : ∃ j k, ‖μ j k‖ = 1) :
    IsBNTCanonicalForm (repeatedBlockBasisSector m hm μ hμ) where
  basis_dim_pos := fun _ => Nat.one_pos
  basis_irreducible := fun j => isIrreducibleTensor_of_bondDim_one (repeatedBlockBasis j)
  basis_left_canonical := fun j => isLeftCanonical_of_dim_one _ (repeatedBlockBasis_norm j)
  basis_normalized_self_overlap := fun j =>
    tendsto_mpvOverlap_self_of_dim_one _ (repeatedBlockBasis_norm j)
  bnt_data := hasBNTSectorData_repeatedBlockBasisSector m hm μ hμ
  basis_distinct := fun j k hjk h => by
    have hc : cast (congr_arg (MPSTensor 2) h) ((repeatedBlockBasisSector m hm μ hμ).basis j) =
        repeatedBlockBasis j :=
      cast_eq _ _
    rw [hc]
    refine not_gaugePhaseEquiv_of_dim_one 1 ?_
    fin_cases j <;> fin_cases k <;> simp_all [repeatedBlockBasis]
  weight_norm_le_one := hle
  weight_unit_exists := hone

/-- The canonical form of arXiv:2307.01696, eq. (S2), of `repeatedBlockTensor`: the basis of
the two one-dimensional normal blocks `A_1 = (1, 0)` and `A_2 = (0, 1)`, with multiplicities
`m = (2, 1)` and every weight `μ_{j,k} = 1`. -/
abbrev repeatedBlockSector : SectorDecomposition 2 :=
  repeatedBlockBasisSector repeatedBlockMult
    (fun j => by fin_cases j <;> simp [repeatedBlockMult]) repeatedBlockWeight
    (fun _ _ => one_ne_zero)

/-- The coefficients `βⱼ = ∑ₖ μ_{j,k}^N` of the canonical form (arXiv:2307.01696, eq. (S4)). -/
theorem coeff_repeatedBlockSector (N : ℕ) :
    repeatedBlockSector.coeff N = bntWeight repeatedBlockWeight N :=
  rfl

/-- **The canonical form of `repeatedBlockTensor` is a basis of normal tensors**
(arXiv:2307.01696, eq. (S2)): the blocks are irreducible, left-canonical, with normalized
self-overlap, their states are linearly independent, they are not related by a gauge
transformation and a phase, every weight has `|μ_{j,k}| ≤ 1`, and one has `|μ_{j,k}| = 1`. -/
theorem isBNTCanonicalForm_repeatedBlockSector : IsBNTCanonicalForm repeatedBlockSector :=
  isBNTCanonicalForm_repeatedBlockBasisSector _ _ _ _
    (fun _ _ => by change ‖(1 : ℂ)‖ ≤ 1; simp)
    ⟨(0 : Fin 2), ⟨0, by decide⟩, by change ‖(1 : ℂ)‖ = 1; simp⟩

/-- The bond coordinates of the three copies in the canonical form: the two copies of the first
block, then the copy of the second. -/
noncomputable def repeatedBlockCopyCoord : Fin 3 → Fin repeatedBlockSector.totalDim :=
  ![repeatedBlockSector.copyCoord 0 ⟨0, by decide⟩ ⟨0, Nat.one_pos⟩,
    repeatedBlockSector.copyCoord 0 ⟨1, by decide⟩ ⟨0, Nat.one_pos⟩,
    repeatedBlockSector.copyCoord 1 ⟨0, by decide⟩ ⟨0, Nat.one_pos⟩]

/-- The canonical form has bond dimension three, the sum `∑ⱼ m_j D_j` of the bond dimensions of
the copies of the blocks in arXiv:2307.01696, eq. (S2). -/
theorem totalDim_repeatedBlockSector : repeatedBlockSector.totalDim = 3 := by
  have h : repeatedBlockSector.totalCopies = 3 := by
    simp [SectorDecomposition.totalCopies, SectorDecomposition.copies, repeatedBlockMult,
      Fin.sum_univ_two]
  simp only [SectorDecomposition.totalDim, SectorDecomposition.flatDim, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, h]

/-- The bond coordinates of the copies of the blocks exhaust the bond coordinates of the
canonical form of arXiv:2307.01696, eq. (S2), each exactly once. -/
theorem bijective_repeatedBlockCopyCoord : Function.Bijective repeatedBlockCopyCoord := by
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨fun x y hxy => ?_, by
    simp [totalDim_repeatedBlockSector]⟩
  fin_cases x <;> fin_cases y <;>
    first
    | rfl
    | (exfalso
       obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.1 (repeatedBlockSector.sigma_eq_of_copyCoord_eq hxy)
       first
       | exact absurd h1 (by decide)
       | exact absurd (eq_of_heq h2) (by decide))

/-- The ordering of the bond coordinates of the canonical form under which its assembled tensor
is `repeatedBlockTensor`: a permutation of the bond basis, which is a gauge transformation. -/
noncomputable def repeatedBlockEquiv : Fin repeatedBlockSector.totalDim ≃ Fin 3 :=
  (Equiv.ofBijective _ bijective_repeatedBlockCopyCoord).symm

/-- The ordering of the bond coordinates of the canonical form of arXiv:2307.01696, eq. (S2),
sends the coordinate `x` to the bond coordinate of the `x`-th copy. -/
theorem repeatedBlockEquiv_symm_apply (x : Fin 3) :
    repeatedBlockEquiv.symm x = repeatedBlockCopyCoord x :=
  rfl

/-- **`repeatedBlockTensor` is the canonical form** `⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_j` of
arXiv:2307.01696, eq. (S2), of `repeatedBlockSector`, after ordering the bond coordinates. -/
theorem reindex_toTensor_repeatedBlockSector (i : Fin 2) :
    reindex repeatedBlockEquiv repeatedBlockEquiv (repeatedBlockSector.toTensor i) =
      repeatedBlockTensor i := by
  ext x y
  rw [reindex_apply, submatrix_apply, repeatedBlockEquiv_symm_apply,
    repeatedBlockEquiv_symm_apply]
  fin_cases x <;> fin_cases y <;>
    simp only [repeatedBlockCopyCoord, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, cons_val,
      cons_val_zero, cons_val_one] <;>
    first
    | (rw [SectorDecomposition.toTensor_copyCoord]
       fin_cases i <;> simp [SectorDecomposition.weight, repeatedBlockWeight, repeatedBlockBasis,
         repeatedBlockDiag])
    | (rw [SectorDecomposition.toTensor_copyCoord_of_ne _ _ (by simp)]
       fin_cases i <;> simp)

/-- The fixed-point pairs of the blocks of the canonical form, each placed on the first copy
of its block (`SectorDecomposition.embeddedFixedPointPair`, with the fixed point `σ_j = 1` of
the one-dimensional block), are the pairs placed on `repeatedBlockCoord`. -/
theorem embeddedFixedPointPair_repeatedBlockSector (j : Fin 2) (p : Fin 3 × Fin 3) :
    repeatedBlockSector.embeddedFixedPointPair (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℂ))
        (fun j => ⟨0, repeatedBlockSector.copies_pos j⟩) j
        (repeatedBlockEquiv.symm p.1, repeatedBlockEquiv.symm p.2) =
      embedPair (fun _ : Fin 1 => repeatedBlockCoord j)
        (fixedPointPair (1 : Matrix (Fin 1) (Fin 1) ℂ)) p := by
  have hc : repeatedBlockSector.copyCoord j ⟨0, repeatedBlockSector.copies_pos j⟩ =
      fun _ : Fin 1 => repeatedBlockEquiv.symm (repeatedBlockCoord j) := by
    funext a
    obtain rfl : a = 0 := Subsingleton.elim _ _
    rw [repeatedBlockEquiv_symm_apply]
    fin_cases j <;> rfl
  rw [SectorDecomposition.embeddedFixedPointPair, hc, embedPair_symm_comp]
  simp

/-- **Lemma 1'(ii) of arXiv:2307.01696 fails for a tensor satisfying all its hypotheses.**
The tensor `A⁰ = diag(1, 1, 0)`, `A¹ = diag(0, 0, 1)` is, after ordering its bond coordinates,
the canonical form `⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_j` of eq. (S2) of a basis of two normal
blocks in canonical form II, with weights `|μ_{j,k}| ≤ 1`, one of modulus one
(`IsBNTCanonicalForm`, normality, and the diagonal positive-definite fixed point `1` of each
block), whose states "produce orthogonal vectors in the thermodynamic limit" (arXiv:2307.01696,
line 973). The transfer maps of the blocks have no eigenvalue other than `1`, so every `λ₂` with
`0 < |λ₂| < 1` bounds their subleading eigenvalues. For the approximating state of eq. (S7),
built from the coefficients `βⱼ = ∑ₖ μ_{j,k}^N` and the pairs of that same fixed point `1`, and
for every `γ > 0` and every constant `C`, there is `M ≥ 1` such that, with `q = M` and `N = M²`
(so `q = o(N)` along this sequence) and `y = (N/q) e^{-γ q/ξ_diag}`, the error exceeds
`C y e^{C y}`. -/
theorem isBNTCanonicalForm_and_not_approximationError_le_repeatedBlock :
    IsBNTCanonicalForm repeatedBlockSector ∧
      (∀ j k, j ≠ k → Tendsto (fun N : ℕ =>
        mpvOverlap (repeatedBlockSector.basis j) (repeatedBlockSector.basis k) N) atTop (𝓝 0)) ∧
      (∀ j, IsNormalTensor (repeatedBlockSector.basis j)) ∧
      (∀ j, (1 : Matrix (Fin 1) (Fin 1) ℂ).PosDef ∧ (1 : Matrix (Fin 1) (Fin 1) ℂ).IsDiag ∧
        Kraus.transferMap (repeatedBlockSector.basis j) 1 = 1) ∧
      (∀ i, reindex repeatedBlockEquiv repeatedBlockEquiv (repeatedBlockSector.toTensor i) =
        repeatedBlockTensor i) ∧
      (∀ j (lam₂ μ : ℂ),
        Module.End.HasEigenvalue (Kraus.transferMap (repeatedBlockSector.basis j)) μ →
          μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖) ∧
      ∀ {lam₂ : ℂ}, 0 < ‖lam₂‖ → ‖lam₂‖ < 1 → ∀ {γ : ℝ}, 0 < γ → ∀ C : ℝ,
        ∃ M : ℕ, 1 ≤ M ∧
          C * (M * Real.exp (-γ * M / correlationLength lam₂)) *
              Real.exp (C * (M * Real.exp (-γ * M / correlationLength lam₂))) <
            1 - ‖nonNormalApproxOverlap repeatedBlockTensor M M
              (ghzAmplitude (repeatedBlockSector.coeff (M * M)))
              (fun j p => repeatedBlockSector.embeddedFixedPointPair
                (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℂ))
                (fun j => ⟨0, repeatedBlockSector.copies_pos j⟩) j
                (repeatedBlockEquiv.symm p.1, repeatedBlockEquiv.symm p.2))‖ := by
  refine ⟨isBNTCanonicalForm_repeatedBlockSector,
    fun _ _ hjk => isBNTCanonicalForm_repeatedBlockSector.cross_overlap_basis_tendsto_zero hjk,
    fun j => isNormalTensor_of_dim_one _ (repeatedBlockBasis_norm j),
    fun j => posDef_isDiag_transferMap_one_of_dim_one _ (repeatedBlockBasis_norm j),
    reindex_toTensor_repeatedBlockSector,
    norm_le_of_hasEigenvalue_transferMap_repeatedBlockBasis, fun h0 h1 γ hγ C => ?_⟩
  simp only [embeddedFixedPointPair_repeatedBlockSector, coeff_repeatedBlockSector]
  exact not_approximationError_le_repeatedBlockTensor h0 h1 hγ C

end MPSTensor
