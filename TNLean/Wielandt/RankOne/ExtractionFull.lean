/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/

import TNLean.Wielandt.RankOne.BoundedWord
import TNLean.Wielandt.RankOne.Extraction
import TNLean.Wielandt.RectangularSpan.Basic

/-!
# Full rank-one extraction for Wielandt Lemma 2(b)

This file closes the final gap in Wielandt's Lemma 2(b) by producing a rank-one
element `Matrix.vecMulVec φ ψ` inside a bounded word span of a blocked tensor.

## Strategy

1. **Key observation:** When `wordSpan A N₀ = ⊤` (from normality), the identity `I` lies
   in the span of length-`N₀` word evaluations. Since `tr(I) = D ≠ 0` and trace is linear,
   at least one length-`N₀` word evaluation has nonzero trace — hence a nonzero eigenvalue.

2. **Blocking at L = N₀:** Setting the blocking length to the normality witness gives
   single-index eigenvectors of the blocked tensor with nonzero eigenvalues for both the
   column and row (transpose) sides.

3. **Two-sided range embedding:** Setting `P = M₀^D` and `Q = M₁^D` (powers of the
   eigenvector words), and using a normality witness `N₁` for the blocked tensor `B`
   with `wordSpan B N₁ = ⊤`, the rank-one matrix `vecMulVec φ ψ` lies in
   `wordSpan B (D + N₁ + D)`.

## Main results

- `exists_nonzero_trace_word_of_wordSpan_eq_top`: nonzero-trace word at any full span level.
- `exists_eigenvector_of_wordSpan_eq_top`: eigenvector extraction from a full word span.
- `exists_rankOne_mem_wordSpan_blockTensor`: the rank-one extraction theorem.
- `wielandt_lemma2b`: the unconditional Lemma 2(b).

## References

- arXiv:0909.5347, Lemma 2(b)
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-! ## Linear-algebra lemmas -/

section LinearAlgebraLemmas

/-- An eigenvector with nonzero eigenvalue lies in the range of the matrix. -/
theorem mem_range_toLin'_of_eigenvector
    (M : Matrix (Fin D) (Fin D) ℂ) (φ : Fin D → ℂ) (μ : ℂ) (hμ : μ ≠ 0)
    (heig : M *ᵥ φ = μ • φ) :
    φ ∈ LinearMap.range (Matrix.toLin' M) := by
  refine LinearMap.mem_range.mpr ⟨μ⁻¹ • φ, ?_⟩
  simp only [Matrix.toLin'_apply, Matrix.mulVec_smul, heig, smul_smul,
    inv_mul_cancel₀ hμ, one_smul]

/-- A transpose eigenvector with nonzero eigenvalue lies in the range of vecMulLinear. -/
theorem mem_range_vecMulLinear_of_transpose_eigenvector
    (Q : Matrix (Fin D) (Fin D) ℂ) (ψ : Fin D → ℂ) (ν : ℂ) (hν : ν ≠ 0)
    (heig : Qᵀ *ᵥ ψ = ν • ψ) :
    ψ ∈ LinearMap.range (Q.vecMulLinear) := by
  refine LinearMap.mem_range.mpr ⟨ν⁻¹ • ψ, ?_⟩
  simp only [Matrix.vecMulLinear_apply]
  have hvecmul : ψ ᵥ* Q = Qᵀ *ᵥ ψ := by
    ext j
    simp [Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm]
  calc
    (ν⁻¹ • ψ) ᵥ* Q = ν⁻¹ • (ψ ᵥ* Q) := by
      ext j
      simp [Matrix.vecMul, dotProduct, Finset.mul_sum, mul_assoc]
    _ = ν⁻¹ • (ν • ψ) := by rw [hvecmul, heig]
    _ = ψ := by rw [smul_smul, inv_mul_cancel₀ hν, one_smul]

/-- A nonzero eigenvector of `M` lies in the range of the powered matrix `M ^ D`. -/
theorem mem_range_toLin'_pow_of_eigenvector
    (M : Matrix (Fin D) (Fin D) ℂ) (φ : Fin D → ℂ) (μ : ℂ) (hμ : μ ≠ 0)
    (heig : M *ᵥ φ = μ • φ) :
    φ ∈ LinearMap.range (Matrix.toLin' (M ^ D)) := by
  exact mem_range_toLin'_of_eigenvector (M := M ^ D) (φ := φ) (μ := μ ^ D)
    (pow_ne_zero D hμ) (pow_mulVec_eq_smul_of_mulVec_eq_smul M φ μ heig D)

/-- A nonzero transpose eigenvector of `M` lies in the range of `vecMulLinear` for `M ^ D`. -/
theorem mem_range_vecMulLinear_pow_of_transpose_eigenvector
    (M : Matrix (Fin D) (Fin D) ℂ) (ψ : Fin D → ℂ) (ν : ℂ) (hν : ν ≠ 0)
    (heig : Mᵀ *ᵥ ψ = ν • ψ) :
    ψ ∈ LinearMap.range ((M ^ D).vecMulLinear) := by
  refine mem_range_vecMulLinear_of_transpose_eigenvector
    (Q := M ^ D) (ψ := ψ) (ν := ν ^ D) (pow_ne_zero D hν) ?_
  rw [Matrix.transpose_pow]
  exact pow_mulVec_eq_smul_of_mulVec_eq_smul Mᵀ ψ ν heig D

/-- `(B i)^D ∈ wordSpan B D`. -/
theorem pow_single_mem_wordSpan (B : MPSTensor d D) (i : Fin d) :
    (B i) ^ D ∈ wordSpan B D := by
  have heq : (B i) = evalWord B [i] := by simp [evalWord]
  have hmem : (evalWord B [i]) ^ D ∈ wordSpan B (D * ([i] : List (Fin d)).length) :=
    evalWord_pow_mem_wordSpan B [i] D
  rw [show D * ([i] : List (Fin d)).length = D from by simp] at hmem
  rwa [← heq] at hmem

private structure BlockedTensorRangeData
    (A : MPSTensor d D) (L : ℕ) (σ₀ τ₀ : Fin L → Fin d)
    (φ ψ : Fin D → ℂ) where
  B : MPSTensor (blockPhysDim d L) D
  P : Matrix (Fin D) (Fin D) ℂ
  Q : Matrix (Fin D) (Fin D) ℂ
  hB : B = blockTensor (d := d) (D := D) A L
  hP : P ∈ wordSpan B D
  hQ : Q ∈ wordSpan B D
  hφ_range : φ ∈ LinearMap.range (Matrix.toLin' P)
  hψ_range : ψ ∈ LinearMap.range (Q.vecMulLinear)

private noncomputable def blockedTensorRangeData
    (A : MPSTensor d D) (L : ℕ) (σ₀ τ₀ : Fin L → Fin d)
    (φ ψ : Fin D → ℂ) (μ ν : ℂ)
    (hμ : μ ≠ 0) (hν : ν ≠ 0)
    (heigφ : evalWord A (List.ofFn σ₀) *ᵥ φ = μ • φ)
    (heigψ : (evalWord A (List.ofFn τ₀))ᵀ *ᵥ ψ = ν • ψ) :
    BlockedTensorRangeData (d := d) (D := D) A L σ₀ τ₀ φ ψ := by
  let B : MPSTensor (blockPhysDim d L) D :=
    blockTensor (d := d) (D := D) A L
  let i₀ : Fin (blockPhysDim d L) := encodeBlock d L σ₀
  let i₁ : Fin (blockPhysDim d L) := encodeBlock d L τ₀
  have hBi₀ : B i₀ = evalWord A (List.ofFn σ₀) := by
    simpa [B, i₀] using blockTensor_apply_encodeBlock A L σ₀
  have hBi₁ : B i₁ = evalWord A (List.ofFn τ₀) := by
    simpa [B, i₁] using blockTensor_apply_encodeBlock A L τ₀
  refine
    { B := B
      P := (B i₀) ^ D
      Q := (B i₁) ^ D
      hB := rfl
      hP := pow_single_mem_wordSpan B i₀
      hQ := pow_single_mem_wordSpan B i₁
      hφ_range := ?_
      hψ_range := ?_ }
  · simpa [hBi₀] using
      (mem_range_toLin'_pow_of_eigenvector
        (M := evalWord A (List.ofFn σ₀)) (φ := φ) (μ := μ) hμ heigφ)
  · simpa [hBi₁] using
      (mem_range_vecMulLinear_pow_of_transpose_eigenvector
        (M := evalWord A (List.ofFn τ₀)) (ψ := ψ) (ν := ν) hν heigψ)

private theorem BlockedTensorRangeData.rankOne_mem_range
    {A : MPSTensor d D} {L : ℕ} {σ₀ τ₀ : Fin L → Fin d}
    {φ ψ : Fin D → ℂ}
    (data : BlockedTensorRangeData (d := d) (D := D) A L σ₀ τ₀ φ ψ) :
    Matrix.vecMulVec φ ψ ∈
      LinearMap.range ((LinearMap.mulLeft ℂ data.P).comp (LinearMap.mulRight ℂ data.Q)) := by
  exact vecMulVec_mem_range_mulLeft_mulRight
    data.P data.Q φ ψ data.hφ_range data.hψ_range

private theorem BlockedTensorRangeData.rankOne_mem_cumulativeSpan_of_cumulativeSpan_eq_top
    {A : MPSTensor d D} {L : ℕ} {σ₀ τ₀ : Fin L → Fin d}
    {φ ψ : Fin D → ℂ}
    (data : BlockedTensorRangeData (d := d) (D := D) A L σ₀ τ₀ φ ψ)
    {N : ℕ} (hcs : cumulativeSpan data.B N = ⊤) :
    Matrix.vecMulVec φ ψ ∈ cumulativeSpan data.B (D + N + D) := by
  exact vecMulVec_mem_cumulativeSpan_of_cumulativeSpan_eq_top
    (d := blockPhysDim d L) (D := D)
    data.B data.P data.Q φ ψ data.hφ_range data.hψ_range data.hP data.hQ hcs

private theorem BlockedTensorRangeData.rankOne_mem_wordSpan_of_wordSpan_eq_top
    {A : MPSTensor d D} {L : ℕ} {σ₀ τ₀ : Fin L → Fin d}
    {φ ψ : Fin D → ℂ}
    (data : BlockedTensorRangeData (d := d) (D := D) A L σ₀ τ₀ φ ψ)
    {N : ℕ} (htop : wordSpan data.B N = ⊤) :
    Matrix.vecMulVec φ ψ ∈ wordSpan data.B (D + N + D) := by
  have hrange_le :
      LinearMap.range ((LinearMap.mulLeft ℂ data.P).comp (LinearMap.mulRight ℂ data.Q)) ≤
        wordSpan data.B (D + N + D) := by
    rw [← biRectSpan_eq_range_of_wordSpan_eq_top
      (d := blockPhysDim d L) (D := D) data.P data.Q data.B htop]
    exact biRectSpan_le_wordSpan (d := blockPhysDim d L) (D := D)
      data.B data.P data.Q data.hP data.hQ
  exact hrange_le data.rankOne_mem_range

private theorem BlockedTensorRangeData.rankOne_mem_wordSpan_of_cumulativeSpan_eq_top_of_aperiodic
    {A : MPSTensor d D} {L : ℕ} {σ₀ τ₀ : Fin L → Fin d}
    {φ ψ : Fin D → ℂ}
    (data : BlockedTensorRangeData (d := d) (D := D) A L σ₀ τ₀ φ ψ)
    {N : ℕ} (hcs : cumulativeSpan data.B N = ⊤)
    (hone : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ wordSpan data.B 1) :
    Matrix.vecMulVec φ ψ ∈ wordSpan data.B (D + N + D) := by
  exact (range_comp_le_wordSpan_of_cumulativeSpan_eq_top_of_aperiodic
    (d := blockPhysDim d L) (D := D)
    data.B data.P data.Q data.hP data.hQ hcs hone) data.rankOne_mem_range

end LinearAlgebraLemmas

/-! ## Nonzero-trace word extraction from a full word span -/

section NonzeroTraceExtraction

/-- If `wordSpan A N = ⊤` and `[NeZero D]`, then there exists a word function
`σ : Fin N → Fin d` such that `tr(evalWord A (List.ofFn σ)) ≠ 0`.

This follows because `I ∈ wordSpan A N = ⊤`, `tr(I) = D ≠ 0`, and trace is linear:
if all generators had zero trace, everything in the span would too. -/
theorem exists_nonzero_trace_word_of_wordSpan_eq_top [NeZero D]
    (A : MPSTensor d D) {N : ℕ} (htop : wordSpan A N = ⊤) :
    ∃ σ : Fin N → Fin d, (evalWord A (List.ofFn σ)).trace ≠ 0 := by
  by_contra hall
  push Not at hall
  have hall' : ∀ σ : Fin N → Fin d, (evalWord A (List.ofFn σ)).trace = 0 := hall
  have hI : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ wordSpan A N := htop ▸ Submodule.mem_top
  -- The trace linear map kills all generators, hence kills the span
  set trMap : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] ℂ := Matrix.traceLinearMap (Fin D) ℂ ℂ
  have hgen : ∀ M ∈ (Set.range fun σ : Fin N → Fin d => evalWord A (List.ofFn σ)),
      trMap M = 0 := by
    rintro M ⟨σ, rfl⟩
    exact hall' σ
  have hker : wordSpan A N ≤ LinearMap.ker trMap := by
    apply Submodule.span_le.mpr
    intro M hM
    exact LinearMap.mem_ker.mpr (hgen M hM)
  have hzero : ∀ M ∈ wordSpan A N, M.trace = 0 := by
    intro M hM
    have := hker hM
    exact LinearMap.mem_ker.mp this
  have htrI : (1 : Matrix (Fin D) (Fin D) ℂ).trace ≠ 0 := by
    simp only [Matrix.trace_one, Fintype.card_fin, ne_eq, Nat.cast_eq_zero]
    exact_mod_cast NeZero.ne D
  exact htrI (hzero 1 hI)

/-- If `wordSpan A N = ⊤` and `[NeZero D]`, then there exists a word function
`σ : Fin N → Fin d` with `evalWord A (List.ofFn σ)` having a nonzero eigenvalue
and eigenvector. -/
theorem exists_eigenvector_of_wordSpan_eq_top [NeZero D]
    (A : MPSTensor d D) {N : ℕ} (htop : wordSpan A N = ⊤) :
    ∃ (σ : Fin N → Fin d) (μ : ℂ) (φ : Fin D → ℂ),
      μ ≠ 0 ∧ φ ≠ 0 ∧
      evalWord A (List.ofFn σ) *ᵥ φ = μ • φ := by
  obtain ⟨σ, hσ⟩ := exists_nonzero_trace_word_of_wordSpan_eq_top A htop
  obtain ⟨μ, φ, hμ, hφ, heig⟩ := exists_eigenvector_of_trace_ne_zero _ hσ
  exact ⟨σ, μ, φ, hμ, hφ, heig⟩

end NonzeroTraceExtraction

/-! ## Two-sided range embedding into word span -/

section TwoSidedRange

/-- Membership in `range (mulLeft P ∘ mulRight Q)` implies membership in
`wordSpan B (m₁ + n + m₂)`, when `P ∈ wordSpan B m₁`, `Q ∈ wordSpan B m₂`,
and `wordSpan B n = ⊤`. -/
theorem range_comp_le_wordSpan
    (B : MPSTensor d D) {m₁ m₂ : ℕ}
    (P Q : Matrix (Fin D) (Fin D) ℂ)
    (hP : P ∈ wordSpan B m₁) (hQ : Q ∈ wordSpan B m₂)
    {n : ℕ} (htop : wordSpan B n = ⊤) :
    LinearMap.range ((LinearMap.mulLeft ℂ P).comp (LinearMap.mulRight ℂ Q)) ≤
      wordSpan B (m₁ + n + m₂) := by
  rw [← biRectSpan_eq_range_of_wordSpan_eq_top (d := d) (D := D) P Q B htop]
  exact biRectSpan_le_wordSpan (d := d) (D := D) B P Q hP hQ

end TwoSidedRange

/-! ## Main rank-one extraction -/

section RankOneExtraction

/-- **Full rank-one extraction for Wielandt Lemma 2(b).**

Under a positive normality witness `N₀ ≥ 1`, produces all data for the blocked
fixed-length matrix spanning theorem:
- word functions `σ₀`, `τ₀` of length `N₀` with eigenvector conditions,
- `vecMulVec φ ψ ∈ wordSpan (blockTensor A N₀) (D + N₀ + D)`.

The key insight: since `wordSpan A N₀ = ⊤` and `tr(I) = D ≠ 0`, at least one
length-`N₀` word has nonzero trace, providing eigenvectors on both sides.
The rank-one matrix is then embedded via the two-sided multiplication map
`X ↦ P * X * Q`, where `P, Q ∈ wordSpan B D` and the middle factor `X`
comes from the full blocked word span `wordSpan B N₀ = ⊤`.
This is the blocked-tensor normality witness used in the `D + N₀ + D` bound. -/
theorem exists_rankOne_mem_wordSpan_blockTensor [NeZero D]
    (A : MPSTensor d D) {N₀ : ℕ} (hN₀ : IsNBlkInjective A N₀) (hN₀pos : 0 < N₀) :
    ∃ (σ₀ τ₀ : Fin N₀ → Fin d)
      (φ ψ : Fin D → ℂ) (μ ν : ℂ) (m_blocked : ℕ),
      φ ≠ 0 ∧ ψ ≠ 0 ∧ μ ≠ 0 ∧ ν ≠ 0 ∧
      evalWord A (List.ofFn σ₀) *ᵥ φ = μ • φ ∧
      (evalWord A (List.ofFn τ₀))ᵀ *ᵥ ψ = ν • ψ ∧
      Matrix.vecMulVec φ ψ ∈
        wordSpan (blockTensor (d := d) (D := D) A N₀) m_blocked := by
  classical
  set L := N₀
  have hL : 0 < L := hN₀pos
  have hN₀_top : wordSpan A N₀ = ⊤ :=
    (wordSpan_eq_top_iff_isNBlkInjective A N₀).mpr hN₀
  -- Step 1: Column eigenvector from wordSpan A N₀ = ⊤
  obtain ⟨σ₀, μ, φ, hμ, hφ, heigφ⟩ :=
    exists_eigenvector_of_wordSpan_eq_top A hN₀_top
  -- Step 2: Row eigenvector from wordSpan (transposeTensor A) N₀ = ⊤
  have hN₀T : IsNBlkInjective (d := d) (D := D) (transposeTensor A) N₀ :=
    IsNBlkInjective_transposeTensor hN₀
  have hN₀T_top : wordSpan (transposeTensor A) N₀ = ⊤ :=
    (wordSpan_eq_top_iff_isNBlkInjective (transposeTensor A) N₀).mpr hN₀T
  obtain ⟨τ₀', ν, ψ, hν, hψ, heigψ'⟩ :=
    exists_eigenvector_of_wordSpan_eq_top (transposeTensor A) hN₀T_top
  -- Convert: evalWord (transposeTensor A) (List.ofFn τ₀') *ᵥ ψ = ν • ψ
  -- ⟹ (evalWord A (List.ofFn τ₀))ᵀ *ᵥ ψ = ν • ψ  where τ₀ = τ₀' ∘ Fin.rev
  set τ₀ : Fin L → Fin d := τ₀' ∘ Fin.rev
  have hτ₀_eq : List.ofFn τ₀ = (List.ofFn τ₀').reverse :=
    (List.ofFn_reverse τ₀').symm
  have heigψ : (evalWord A (List.ofFn τ₀))ᵀ *ᵥ ψ = ν • ψ := by
    rw [hτ₀_eq]
    -- Goal: (evalWord A (List.ofFn τ₀').reverse)ᵀ *ᵥ ψ = ν • ψ
    -- By evalWord_transpose: (evalWord A w)ᵀ = evalWord (transposeTensor A) w.reverse
    rw [evalWord_transpose A (List.ofFn τ₀').reverse, List.reverse_reverse]
    exact heigψ'
  let data :=
    blockedTensorRangeData A L σ₀ τ₀ φ ψ μ ν hμ hν heigφ heigψ
  have hBtop : wordSpan data.B N₀ = ⊤ := by
    have htopNL : wordSpan A (N₀ * L) = ⊤ := by
      rw [show N₀ * L = L * N₀ from by ring]
      exact wordSpan_top_of_mul A hN₀_top L hL
    have hle : wordSpan A (N₀ * L) ≤ wordSpan data.B N₀ := by
      simpa [data.hB] using wordSpan_le_wordSpan_blockTensor A L N₀
    exact eq_top_iff.mpr (htopNL ▸ hle)
  exact ⟨σ₀, τ₀, φ, ψ, μ, ν, D + N₀ + D,
    hφ, hψ, hμ, hν, heigφ, heigψ, by
      simpa [L, data.hB] using
        data.rankOne_mem_wordSpan_of_wordSpan_eq_top hBtop⟩

end RankOneExtraction

/-! ## Unconditional Wielandt Lemma 2(b) -/

section WielandtLemma2b

/-- **Wielandt Lemma 2(b), unconditional version.**

For any `IsNormal` MPS tensor `A` with `[NeZero D]`, there exists `N` such that
`wordSpan A N = ⊤`.

This combines the rank-one extraction with the blocked fixed-length matrix spanning theorem.

- When `N₀ = 0`: `wordSpan A 0 = ⊤` directly.
- When `N₀ ≥ 1`: writing `B := blockTensor A N₀`, the rank-one extraction gives
  `vecMulVec φ ψ ∈ wordSpan B (D + N₀ + D)`, where the middle `N₀` is the
  blocked-tensor full-span witness `wordSpan B N₀ = ⊤`; the blocked fixed-length matrix spanning then
  produces `wordSpan A ((4D - 2 + N₀) * N₀) = ⊤`.

The bound `N = (4D - 2 + N₀) * N₀` is coarse. -/
theorem wielandt_lemma2b [NeZero D]
    (A : MPSTensor d D) (hN : IsNormal A) :
    ∃ N : ℕ, wordSpan A N = ⊤ := by
  classical
  obtain ⟨N₀, hN₀⟩ := hN
  have hN₀_top : wordSpan A N₀ = ⊤ :=
    (wordSpan_eq_top_iff_isNBlkInjective A N₀).mpr hN₀
  by_cases hN₀pos : N₀ = 0
  · exact ⟨0, by rwa [hN₀pos] at hN₀_top⟩
  · obtain ⟨σ₀, τ₀, φ, ψ, μ, ν, m_blocked,
      hφ, hψ, hμ, hν, heigφ, heigψ, hRankOne⟩ :=
      exists_rankOne_mem_wordSpan_blockTensor A hN₀ (by omega)
    exact ⟨(D - 1 + (m_blocked + (D - 1))) * N₀,
      wielandt_blocked_assembly A ⟨N₀, hN₀⟩ N₀ (by omega)
        σ₀ φ hφ μ hμ heigφ
        τ₀ ψ hψ ν hν heigψ hRankOne⟩

end WielandtLemma2b

/-! ## Parametrized rank-one extraction lemmas -/

section ExternalEigenvectors

/-- **Rank-one element in a bounded cumulative span of the blocked tensor, from supplied
word-eigenvector data and a cumulative spanning witness.**

This is the cumulative analogue of the later exact-word-span result: the manufactured rank-one
matrix lies in `T_{D + N + D}` of the blocked tensor as soon as `T_N` is already full. -/
theorem exists_rankOne_in_cumulativeSpan_blockTensor_of_wordEigenvectors
    [NeZero D]
    (A : MPSTensor d D)
    (L : ℕ)
    (σ₀ τ₀ : Fin L → Fin d)
    (φ ψ : Fin D → ℂ) (μ ν : ℂ)
    (hμ : μ ≠ 0) (hν : ν ≠ 0)
    (heigφ : evalWord A (List.ofFn σ₀) *ᵥ φ = μ • φ)
    (heigψ : (evalWord A (List.ofFn τ₀))ᵀ *ᵥ ψ = ν • ψ)
    {N : ℕ}
    (hcs : cumulativeSpan (blockTensor (d := d) (D := D) A L) N = ⊤) :
    Matrix.vecMulVec φ ψ ∈
      cumulativeSpan (blockTensor (d := d) (D := D) A L) (D + N + D) := by
  classical
  let data :=
    blockedTensorRangeData A L σ₀ τ₀ φ ψ μ ν hμ hν heigφ heigψ
  have hcsB : cumulativeSpan data.B N = ⊤ := by
    simpa [data.hB] using hcs
  simpa [data.hB] using
    data.rankOne_mem_cumulativeSpan_of_cumulativeSpan_eq_top hcsB

/-- **Exact blocked rank-one extraction from cumulative spanning plus aperiodicity.**

If the blocked tensor has full cumulative span at level `N` and also satisfies the padding
hypothesis `1 ∈ wordSpan B 1`, then the same manufactured rank-one matrix already lies in the
single exact-length word span `S_{D + N + D}(B)`. -/
theorem exists_rankOne_in_wordSpan_blockTensor_of_wordEigenvectors_of_cumulativeSpan_of_aperiodic
    [NeZero D]
    (A : MPSTensor d D)
    (L : ℕ)
    (σ₀ τ₀ : Fin L → Fin d)
    (φ ψ : Fin D → ℂ) (μ ν : ℂ)
    (hμ : μ ≠ 0) (hν : ν ≠ 0)
    (heigφ : evalWord A (List.ofFn σ₀) *ᵥ φ = μ • φ)
    (heigψ : (evalWord A (List.ofFn τ₀))ᵀ *ᵥ ψ = ν • ψ)
    {N : ℕ}
    (hcs : cumulativeSpan (blockTensor (d := d) (D := D) A L) N = ⊤)
    (hone : (1 : Matrix (Fin D) (Fin D) ℂ) ∈
      wordSpan (blockTensor (d := d) (D := D) A L) 1) :
    Matrix.vecMulVec φ ψ ∈
      wordSpan (blockTensor (d := d) (D := D) A L) (D + N + D) := by
  classical
  let data :=
    blockedTensorRangeData A L σ₀ τ₀ φ ψ μ ν hμ hν heigφ heigψ
  have hcsB : cumulativeSpan data.B N = ⊤ := by
    simpa [data.hB] using hcs
  have honeB : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ wordSpan data.B 1 := by
    simpa [data.hB] using hone
  simpa [data.hB] using
    data.rankOne_mem_wordSpan_of_cumulativeSpan_eq_top_of_aperiodic hcsB honeB

/-- **Rank-one element in the word span of the blocked tensor, from supplied word-eigenvector
data.**

Given:
- A blocking length `L > 0` and eigenvector data (word functions `σ₀`, `τ₀`, eigenvectors
  `φ`, `ψ`, nonzero eigenvalues `μ`, `ν`),
- `IsNormal A`,

we place `vecMulVec φ ψ` in a bounded word span of the blocked tensor.

### Strategy:
1. `B := blockTensor A L` is `IsNormal` (from `isNormal_blockTensor`).
2. `P := (B (encodeBlock σ₀))^D` and `Q := (B (encodeBlock τ₀))^D` lie in `wordSpan B D`.
3. The eigenvector conditions give `φ ∈ range(toLin' P)` and `ψ ∈ range(Q.vecMulLinear)`.
4. By `vecMulVec_mem_range_mulLeft_mulRight`, `vecMulVec φ ψ ∈ range(mulLeft P ∘ mulRight Q)`.
5. Since `B` is normal, `wordSpan B N₁ = ⊤` for some `N₁`, so
   `range(mulLeft P ∘ mulRight Q) ≤ wordSpan B (D + N₁ + D)`.

The resulting bound is `m_blocked = D + N₁ + D = 2D + N₁`, where `N₁` is the
normality witness of the blocked tensor `B`. -/
theorem exists_rankOne_in_wordSpan_blockTensor_of_wordEigenvectors
    [NeZero D]
    (A : MPSTensor d D)
    (L : ℕ) (hL : 0 < L)
    (σ₀ τ₀ : Fin L → Fin d)
    (φ ψ : Fin D → ℂ) (μ ν : ℂ)
    (hμ : μ ≠ 0) (hν : ν ≠ 0)
    (heigφ : evalWord A (List.ofFn σ₀) *ᵥ φ = μ • φ)
    (heigψ : (evalWord A (List.ofFn τ₀))ᵀ *ᵥ ψ = ν • ψ)
    (hNormal : IsNormal A) :
    ∃ m_blocked : ℕ,
      Matrix.vecMulVec φ ψ ∈
        wordSpan (blockTensor (d := d) (D := D) A L) m_blocked := by
  classical
  let data :=
    blockedTensorRangeData A L σ₀ τ₀ φ ψ μ ν hμ hν heigφ heigψ
  have hNormalB : IsNormal data.B := by
    simpa [data.hB] using isNormal_blockTensor A L hL hNormal
  obtain ⟨N₁, hN₁⟩ := hNormalB
  have hBtop : wordSpan data.B N₁ = ⊤ :=
    (wordSpan_eq_top_iff_isNBlkInjective data.B N₁).mpr hN₁
  exact ⟨D + N₁ + D, by
    simpa [data.hB] using data.rankOne_mem_wordSpan_of_wordSpan_eq_top hBtop⟩

/-- **Wielandt Lemma 2(b) blocked word-span saturation from supplied word-eigenvector data.**

Given word eigenvectors of length `L` with nonzero eigenvalues and `IsNormal A`,
produces `wordSpan A N = ⊤` for an explicit `N`.

This eliminates the `hRankOne` hypothesis from `wielandt_blocked_assembly` by
using `exists_rankOne_in_wordSpan_blockTensor_of_wordEigenvectors` to internally
produce the rank-one element. -/
theorem wielandt_blocked_assembly_complete [NeZero D]
    (A : MPSTensor d D)
    (L : ℕ) (hL : 0 < L)
    (σ₀ τ₀ : Fin L → Fin d)
    (φ ψ : Fin D → ℂ)
    (hφ : φ ≠ 0) (hψ : ψ ≠ 0)
    (μ ν : ℂ) (hμ : μ ≠ 0) (hν : ν ≠ 0)
    (heigφ : evalWord A (List.ofFn σ₀) *ᵥ φ = μ • φ)
    (heigψ : (evalWord A (List.ofFn τ₀))ᵀ *ᵥ ψ = ν • ψ)
    (hNormal : IsNormal A) :
    ∃ N : ℕ, wordSpan A N = ⊤ := by
  -- Step 1: Get the rank-one element in the blocked word span
  obtain ⟨m_blocked, hRankOne⟩ :=
    exists_rankOne_in_wordSpan_blockTensor_of_wordEigenvectors
      A L hL σ₀ τ₀ φ ψ μ ν hμ hν heigφ heigψ hNormal
  -- Step 2: Apply the blocked fixed-length matrix spanning lemma
  exact ⟨(D - 1 + (m_blocked + (D - 1))) * L,
    wielandt_blocked_assembly A hNormal L hL σ₀ φ hφ μ hμ heigφ
      τ₀ ψ hψ ν hν heigψ hRankOne⟩

end ExternalEigenvectors

end MPSTensor
