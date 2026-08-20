/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixMulRange
import TNLean.Kraus.Blocking
import TNLean.Kraus.Wielandt.RankOne.BoundedWord
import TNLean.Kraus.Wielandt.RankOne.Construction
import TNLean.Kraus.Wielandt.RankOne.Element
import TNLean.Kraus.Wielandt.RankOne.Extraction

/-!
# Full rank-one extraction for finite matrix families

This module constructs the bounded rank-one element used in Sanz, Pérez-García,
Wolf, and Cirac, arXiv:0909.5347, Lemma 2(b), for an arbitrary finite family of
square matrices whose fixed-length word span is full.
-/

open scoped Matrix

namespace Kraus

variable {d D : ℕ}

/-- A power of one matrix in a finite family belongs to the corresponding word span. -/
theorem pow_single_mem_wordSpan
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (i : Fin d) :
    (K i) ^ D ∈ wordSpan K D := by
  have heq : K i = MPSTensor.evalWord K [i] := by simp [MPSTensor.evalWord]
  have hmem :
      (MPSTensor.evalWord K [i]) ^ D ∈
        wordSpan K (D * ([i] : List (Fin d)).length) :=
    evalWord_pow_mem_wordSpan K [i] D
  rw [show D * ([i] : List (Fin d)).length = D from by simp] at hmem
  rwa [← heq] at hmem

private structure BlockedTensorRangeData
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (L : ℕ)
    (σ₀ τ₀ : Fin L → Fin d) (φ ψ : Fin D → ℂ) where
  B : Fin (MPSTensor.blockPhysDim d L) → Matrix (Fin D) (Fin D) ℂ
  P : Matrix (Fin D) (Fin D) ℂ
  Q : Matrix (Fin D) (Fin D) ℂ
  hB : B = MPSTensor.blockTensor K L
  hP : P ∈ wordSpan B D
  hQ : Q ∈ wordSpan B D
  hφ_range : φ ∈ LinearMap.range (Matrix.toLin' P)
  hψ_range : ψ ∈ LinearMap.range (Q.vecMulLinear)

private noncomputable def blockedTensorRangeData
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (L : ℕ)
    (σ₀ τ₀ : Fin L → Fin d) (φ ψ : Fin D → ℂ) (μ ν : ℂ)
    (hμ : μ ≠ 0) (hν : ν ≠ 0)
    (heigφ : MPSTensor.evalWord K (List.ofFn σ₀) *ᵥ φ = μ • φ)
    (heigψ : (MPSTensor.evalWord K (List.ofFn τ₀))ᵀ *ᵥ ψ = ν • ψ) :
    BlockedTensorRangeData K L σ₀ τ₀ φ ψ := by
  let B := MPSTensor.blockTensor K L
  let i₀ : Fin (MPSTensor.blockPhysDim d L) :=
    (MPSTensor.decodeBlockEquiv d L).symm σ₀
  let i₁ : Fin (MPSTensor.blockPhysDim d L) :=
    (MPSTensor.decodeBlockEquiv d L).symm τ₀
  have hBi₀ : B i₀ = MPSTensor.evalWord K (List.ofFn σ₀) := by
    simp [B, i₀, MPSTensor.blockTensor, MPSTensor.wordOfBlock]
  have hBi₁ : B i₁ = MPSTensor.evalWord K (List.ofFn τ₀) := by
    simp [B, i₁, MPSTensor.blockTensor, MPSTensor.wordOfBlock]
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
      MPSTensor.mem_range_toLin'_pow_of_eigenvector
        (M := MPSTensor.evalWord K (List.ofFn σ₀)) (φ := φ) (μ := μ) hμ heigφ
  · simpa [hBi₁] using
      MPSTensor.mem_range_vecMulLinear_pow_of_transpose_eigenvector
        (M := MPSTensor.evalWord K (List.ofFn τ₀)) (ψ := ψ) (ν := ν) hν heigψ

private theorem BlockedTensorRangeData.rankOne_mem_wordSpan_of_wordSpan_eq_top
    {K : Fin d → Matrix (Fin D) (Fin D) ℂ} {L : ℕ}
    {σ₀ τ₀ : Fin L → Fin d} {φ ψ : Fin D → ℂ}
    (data : BlockedTensorRangeData K L σ₀ τ₀ φ ψ)
    {N : ℕ} (htop : wordSpan data.B N = ⊤) :
    Matrix.vecMulVec φ ψ ∈ wordSpan data.B (D + N + D) := by
  have hrange_le :
      LinearMap.range
          ((LinearMap.mulLeft ℂ data.P).comp (LinearMap.mulRight ℂ data.Q)) ≤
        wordSpan data.B (D + N + D) := by
    rw [← biRectSpan_eq_range_of_wordSpan_eq_top data.P data.Q data.B htop]
    exact biRectSpan_le_wordSpan data.B data.P data.Q data.hP data.hQ
  exact hrange_le (Matrix.vecMulVec_mem_range_mulLeft_mulRight
    data.P data.Q φ ψ data.hφ_range data.hψ_range)

/-- **Full rank-one extraction for Wielandt Lemma 2(b).**

A positive level at which a finite matrix family's word span is full yields
nonzero right and transpose eigenvectors and a rank-one element in a bounded
word span of the blocked family. -/
theorem exists_rankOne_mem_wordSpan_blockTensor [NeZero D]
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) {N₀ : ℕ}
    (hN₀ : wordSpan K N₀ = ⊤) (hN₀pos : 0 < N₀) :
    ∃ (σ₀ τ₀ : Fin N₀ → Fin d)
      (φ ψ : Fin D → ℂ) (μ ν : ℂ) (m_blocked : ℕ),
      φ ≠ 0 ∧ ψ ≠ 0 ∧ μ ≠ 0 ∧ ν ≠ 0 ∧
      MPSTensor.evalWord K (List.ofFn σ₀) *ᵥ φ = μ • φ ∧
      (MPSTensor.evalWord K (List.ofFn τ₀))ᵀ *ᵥ ψ = ν • ψ ∧
      Matrix.vecMulVec φ ψ ∈
        wordSpan (MPSTensor.blockTensor K N₀) m_blocked := by
  classical
  obtain ⟨σ₀, μ, φ, hμ, hφ, heigφ⟩ :=
    exists_eigenvector_of_wordSpan_eq_top K hN₀
  have hN₀T : wordSpan (transposeFamily K) N₀ = ⊤ :=
    wordSpan_transposeFamily_eq_top_of_wordSpan_eq_top K hN₀
  obtain ⟨τ₀', ν, ψ, hν, hψ, heigψ'⟩ :=
    exists_eigenvector_of_wordSpan_eq_top (transposeFamily K) hN₀T
  let τ₀ : Fin N₀ → Fin d := τ₀' ∘ Fin.rev
  have hτ₀_eq : List.ofFn τ₀ = (List.ofFn τ₀').reverse :=
    (List.ofFn_reverse τ₀').symm
  have heigψ : (MPSTensor.evalWord K (List.ofFn τ₀))ᵀ *ᵥ ψ = ν • ψ := by
    rw [hτ₀_eq, evalWord_transpose K (List.ofFn τ₀').reverse, List.reverse_reverse]
    exact heigψ'
  let data := blockedTensorRangeData K N₀ σ₀ τ₀ φ ψ μ ν hμ hν heigφ heigψ
  have hBtop : wordSpan data.B N₀ = ⊤ := by
    have hInjective : MPSTensor.IsInjective (MPSTensor.blockTensor K N₀) :=
      (MPSTensor.isNBlkInjective_iff_blockTensor_isInjective K N₀).mp hN₀
    have hB1 : wordSpan data.B 1 = ⊤ := by
      rw [wordSpan_one, data.hB]
      exact hInjective
    simpa using wordSpan_top_of_mul data.B hB1 N₀ hN₀pos
  exact ⟨σ₀, τ₀, φ, ψ, μ, ν, D + N₀ + D,
    hφ, hψ, hμ, hν, heigφ, heigψ, by
      simpa [data.hB] using data.rankOne_mem_wordSpan_of_wordSpan_eq_top hBtop⟩

end Kraus
