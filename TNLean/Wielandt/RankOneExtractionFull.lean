/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/

import TNLean.Wielandt.RankOneManufacture
import TNLean.Wielandt.RankOneExtraction
import TNLean.Wielandt.RankOneSpanGrowth
import TNLean.Wielandt.RectangularSpan
import TNLean.Wielandt.RankOneElement

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
   eigenvector words), and using `wordSpan B N₀ = ⊤`, the rank-one matrix
   `vecMulVec φ ψ` lies in `wordSpan B (2D + N₀)`.

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

/-! ## Helper lemmas -/

section Helpers

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
  -- (ν⁻¹ • ψ) ᵥ* Q = ν⁻¹ • (ψ ᵥ* Q)
  calc (ν⁻¹ • ψ) ᵥ* Q
      = ν⁻¹ • (ψ ᵥ* Q) := by
        ext j; simp [Matrix.vecMul, dotProduct, Finset.mul_sum, mul_assoc]
    _ = ν⁻¹ • (ν • ψ) := by rw [hvecmul, heig]
    _ = ψ := by rw [smul_smul, inv_mul_cancel₀ hν, one_smul]

/-- The transpose of a power equals the power of the transpose. -/
theorem Matrix.transpose_pow_eq_pow_transpose
    (M : Matrix (Fin D) (Fin D) ℂ) (k : ℕ) :
    (M ^ k)ᵀ = (Mᵀ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Matrix.transpose_mul, ih, ← pow_succ']

/-- `(B i)^D ∈ wordSpan B D`. -/
theorem pow_single_mem_wordSpan (B : MPSTensor d D) (i : Fin d) :
    (B i) ^ D ∈ wordSpan B D := by
  have heq : (B i) = evalWord B [i] := by simp [evalWord]
  have hmem : (evalWord B [i]) ^ D ∈ wordSpan B (D * ([i] : List (Fin d)).length) :=
    evalWord_pow_mem_wordSpan B [i] D
  rw [show D * ([i] : List (Fin d)).length = D from by simp] at hmem
  rwa [← heq] at hmem

/-- Reversing `List.ofFn σ` corresponds to precomposing with `Fin.rev`. -/
private lemma ofFn_reverse {n : ℕ} {α : Type*} (σ : Fin n → α) :
    (List.ofFn σ).reverse = List.ofFn (σ ∘ Fin.rev) := by
  calc
    (List.ofFn σ).reverse = (List.map σ (List.finRange n)).reverse := by
      simp [List.ofFn_eq_map]
    _ = List.map σ (List.finRange n).reverse := by
      simp [List.map_reverse]
    _ = List.map σ (List.map Fin.rev (List.finRange n)) := by
      simp [List.finRange_reverse]
    _ = List.map (σ ∘ Fin.rev) (List.finRange n) := by
      simp [List.map_map]
    _ = List.ofFn (σ ∘ Fin.rev) := by
      simp [List.ofFn_eq_map]

end Helpers

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
  push_neg at hall
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
  intro M hM
  rcases LinearMap.mem_range.mp hM with ⟨X, rfl⟩
  -- Goal: P * (X * Q) ∈ wordSpan B (m₁ + n + m₂)
  change P * (X * Q) ∈ wordSpan B (m₁ + n + m₂)
  have hX : X ∈ wordSpan B n := htop ▸ Submodule.mem_top
  have hXQ : X * Q ∈ wordSpan B (n + m₂) :=
    (wordSpan_mul_le B n m₂) (Submodule.mul_mem_mul hX hQ)
  have hPXQ : P * (X * Q) ∈ wordSpan B (m₁ + (n + m₂)) :=
    (wordSpan_mul_le B m₁ (n + m₂)) (Submodule.mul_mem_mul hP hXQ)
  rwa [show m₁ + (n + m₂) = m₁ + n + m₂ from by omega] at hPXQ

end TwoSidedRange

/-! ## Main rank-one extraction -/

section RankOneExtraction

/-- **Full rank-one extraction for Wielandt Lemma 2(b).**

Under a positive normality witness `N₀ ≥ 1`, produces all data for the blocked
assembly theorem:
- word functions `σ₀`, `τ₀` of length `N₀` with eigenvector conditions,
- `vecMulVec φ ψ ∈ wordSpan (blockTensor A N₀) (D + N₀ + D)`.

The key insight: since `wordSpan A N₀ = ⊤` and `tr(I) = D ≠ 0`, at least one
length-`N₀` word has nonzero trace, providing eigenvectors on both sides.
The rank-one matrix is then embedded via the two-sided multiplication map
`X ↦ P * X * Q` where `P, Q ∈ wordSpan B D`. -/
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
    (ofFn_reverse τ₀').symm
  have heigψ : (evalWord A (List.ofFn τ₀))ᵀ *ᵥ ψ = ν • ψ := by
    rw [hτ₀_eq]
    -- Goal: (evalWord A (List.ofFn τ₀').reverse)ᵀ *ᵥ ψ = ν • ψ
    -- By evalWord_transpose: (evalWord A w)ᵀ = evalWord (transposeTensor A) w.reverse
    rw [evalWord_transpose A (List.ofFn τ₀').reverse, List.reverse_reverse]
    exact heigψ'
  -- Step 3: Set up the blocked tensor
  set B := blockTensor (d := d) (D := D) A L with hB_def
  set i₀ := encodeBlock d L σ₀
  set i₁ := encodeBlock d L τ₀
  have hBi₀ : B i₀ = evalWord A (List.ofFn σ₀) :=
    blockTensor_apply_encodeBlock A L σ₀
  have hBi₁ : B i₁ = evalWord A (List.ofFn τ₀) :=
    blockTensor_apply_encodeBlock A L τ₀
  -- Step 4: P = (B i₀)^D, Q = (B i₁)^D
  set P := (B i₀) ^ D
  set Q := (B i₁) ^ D
  have hP : P ∈ wordSpan B D := pow_single_mem_wordSpan B i₀
  have hQ : Q ∈ wordSpan B D := pow_single_mem_wordSpan B i₁
  -- Step 5: φ ∈ range(toLin' P) via eigenvector of M₀^D
  have hφ_range : φ ∈ LinearMap.range (Matrix.toLin' P) := by
    have hP_eig : P *ᵥ φ = (μ ^ D) • φ := by
      simp only [P]; rw [hBi₀]
      exact pow_mulVec_eq_smul_of_mulVec_eq_smul
        (evalWord A (List.ofFn σ₀)) φ μ heigφ D
    exact mem_range_toLin'_of_eigenvector P φ (μ ^ D) (pow_ne_zero D hμ) hP_eig
  -- Step 6: ψ ∈ range(Q.vecMulLinear) via transpose eigenvector of M₁^D
  have hψ_range : ψ ∈ LinearMap.range (Q.vecMulLinear) := by
    have hQ_eig : Qᵀ *ᵥ ψ = (ν ^ D) • ψ := by
      simp only [Q]
      rw [Matrix.transpose_pow_eq_pow_transpose, hBi₁]
      exact pow_mulVec_eq_smul_of_mulVec_eq_smul
        ((evalWord A (List.ofFn τ₀))ᵀ) ψ ν heigψ D
    exact mem_range_vecMulLinear_of_transpose_eigenvector
      Q ψ (ν ^ D) (pow_ne_zero D hν) hQ_eig
  -- Step 7: vecMulVec φ ψ ∈ range(mulLeft P ∘ mulRight Q)
  have hrank1_range : Matrix.vecMulVec φ ψ ∈
      LinearMap.range ((LinearMap.mulLeft ℂ P).comp (LinearMap.mulRight ℂ Q)) :=
    vecMulVec_mem_range_mulLeft_mulRight P Q φ ψ hφ_range hψ_range
  -- Step 8: wordSpan B N₀ = ⊤ (blocking preserves normality with same witness)
  have hBtop : wordSpan B N₀ = ⊤ := by
    have htopNL : wordSpan A (N₀ * L) = ⊤ := by
      rw [show N₀ * L = L * N₀ from by ring]
      exact wordSpan_top_of_mul A hN₀_top L hL
    have hle : wordSpan A (N₀ * L) ≤ wordSpan B N₀ :=
      wordSpan_le_wordSpan_blockTensor A L N₀
    exact eq_top_iff.mpr (htopNL ▸ hle)
  -- Step 9: Embed rank-one into wordSpan B (D + N₀ + D)
  have hrange_le :
      LinearMap.range ((LinearMap.mulLeft ℂ P).comp (LinearMap.mulRight ℂ Q)) ≤
        wordSpan B (D + N₀ + D) :=
    range_comp_le_wordSpan B P Q hP hQ hBtop
  exact ⟨σ₀, τ₀, φ, ψ, μ, ν, D + N₀ + D,
    hφ, hψ, hμ, hν, heigφ, heigψ, hrange_le hrank1_range⟩

end RankOneExtraction

/-! ## Unconditional Wielandt Lemma 2(b) -/

section WielandtLemma2b

set_option maxHeartbeats 800000 in
-- The blocked assembly involves multiple typeclass unifications across blocked tensor types.
/-- **Wielandt Lemma 2(b), unconditional version.**

For any `IsNormal` MPS tensor `A` with `[NeZero D]`, there exists `N` such that
`wordSpan A N = ⊤`.

This combines the rank-one extraction with the blocked assembly theorem.

- When `N₀ = 0`: `wordSpan A 0 = ⊤` directly.
- When `N₀ ≥ 1`: the rank-one extraction gives `vecMulVec φ ψ ∈ wordSpan B (2D + N₀)`,
  and the blocked assembly produces `wordSpan A ((4D - 2 + N₀) * N₀) = ⊤`.

The bound `N = (4D - 2 + N₀) * N₀` is coarse but sorry-free. -/
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
      wielandt_blocked_assembly A ⟨N₀, hN₀⟩ N₀ (by omega) σ₀ φ hφ μ hμ heigφ τ₀ ψ hψ ν hν
        heigψ hRankOne⟩

end WielandtLemma2b

/-! ## Rank-one extraction with external eigenvectors -/

section ExternalEigenvectors

/-- **Rank-one element in the word span of the blocked tensor, given external eigenvectors.**

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

The bound `m_blocked = 2D + N₁` depends on the normality witness `N₁` of the blocked tensor. -/
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
  set B := blockTensor (d := d) (D := D) A L with hB_def
  set i₀ := encodeBlock d L σ₀
  set i₁ := encodeBlock d L τ₀
  -- Step 1: B is normal
  have hNormalB : IsNormal B := isNormal_blockTensor A L hL hNormal
  -- Step 2: P = (B i₀)^D and Q = (B i₁)^D lie in wordSpan B D
  set P := (B i₀) ^ D
  set Q := (B i₁) ^ D
  have hP : P ∈ wordSpan B D := pow_single_mem_wordSpan B i₀
  have hQ : Q ∈ wordSpan B D := pow_single_mem_wordSpan B i₁
  -- Step 3a: Eigenvector conditions at the blocked level
  have hBi₀ : B i₀ = evalWord A (List.ofFn σ₀) :=
    blockTensor_apply_encodeBlock A L σ₀
  have hBi₁ : B i₁ = evalWord A (List.ofFn τ₀) :=
    blockTensor_apply_encodeBlock A L τ₀
  -- Step 3b: P *ᵥ φ = μ^D • φ
  have hP_eig : P *ᵥ φ = (μ ^ D) • φ := by
    simp only [P]; rw [hBi₀]
    exact pow_mulVec_eq_smul_of_mulVec_eq_smul
      (evalWord A (List.ofFn σ₀)) φ μ heigφ D
  -- Step 3c: φ ∈ range(toLin' P)
  have hφ_range : φ ∈ LinearMap.range (Matrix.toLin' P) :=
    mem_range_toLin'_of_eigenvector P φ (μ ^ D) (pow_ne_zero D hμ) hP_eig
  -- Step 3d: Qᵀ *ᵥ ψ = ν^D • ψ
  have hQ_eig : Qᵀ *ᵥ ψ = (ν ^ D) • ψ := by
    simp only [Q]
    rw [Matrix.transpose_pow_eq_pow_transpose, hBi₁]
    exact pow_mulVec_eq_smul_of_mulVec_eq_smul
      ((evalWord A (List.ofFn τ₀))ᵀ) ψ ν heigψ D
  -- Step 3e: ψ ∈ range(Q.vecMulLinear)
  have hψ_range : ψ ∈ LinearMap.range (Q.vecMulLinear) :=
    mem_range_vecMulLinear_of_transpose_eigenvector
      Q ψ (ν ^ D) (pow_ne_zero D hν) hQ_eig
  -- Step 4: vecMulVec φ ψ ∈ range(mulLeft P ∘ mulRight Q)
  have hrank1_range : Matrix.vecMulVec φ ψ ∈
      LinearMap.range ((LinearMap.mulLeft ℂ P).comp (LinearMap.mulRight ℂ Q)) :=
    vecMulVec_mem_range_mulLeft_mulRight P Q φ ψ hφ_range hψ_range
  -- Step 5: Get wordSpan B N₁ = ⊤ from normality of B
  obtain ⟨N₁, hN₁⟩ := hNormalB
  have hBtop : wordSpan B N₁ = ⊤ :=
    (wordSpan_eq_top_iff_isNBlkInjective B N₁).mpr hN₁
  -- Step 6: range(mulLeft P ∘ mulRight Q) ≤ wordSpan B (D + N₁ + D)
  have hrange_le :
      LinearMap.range ((LinearMap.mulLeft ℂ P).comp (LinearMap.mulRight ℂ Q)) ≤
        wordSpan B (D + N₁ + D) :=
    range_comp_le_wordSpan B P Q hP hQ hBtop
  exact ⟨D + N₁ + D, hrange_le hrank1_range⟩

set_option maxHeartbeats 800000 in
-- The blocked assembly involves multiple typeclass unifications across blocked tensor types.
/-- **Wielandt Lemma 2(b) blocked assembly — unconditional version with external eigenvectors.**

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
  -- Step 2: Apply the conditional assembly
  exact ⟨(D - 1 + (m_blocked + (D - 1))) * L,
    wielandt_blocked_assembly A hNormal L hL σ₀ φ hφ μ hμ heigφ
      τ₀ ψ hψ ν hν heigψ hRankOne⟩

end ExternalEigenvectors

end MPSTensor
