/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Kraus.Wielandt.RankOne.ExtractionFull
import TNLean.Wielandt.RankOne.BoundedWord
import TNLean.Wielandt.RectangularSpan.Basic

/-!
# Full rank-one extraction for MPS tensors

This file preserves the paper-facing MPS rank-one extraction theorem and proves
Wielandt Lemma 2(b). The finite-family construction is in
`TNLean.Kraus.Wielandt.RankOne.ExtractionFull`.

## References

- arXiv:0909.5347, Lemma 2(b)
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- **Full rank-one extraction for Wielandt Lemma 2(b).**

Under a positive normality witness, this produces nonzero right and transpose
eigenvectors and a rank-one element in a bounded word span of the blocked tensor. -/
theorem exists_rankOne_mem_wordSpan_blockTensor [NeZero D]
    (A : MPSTensor d D) {N₀ : ℕ} (hN₀ : IsNBlkInjective A N₀) (hN₀pos : 0 < N₀) :
    ∃ (σ₀ τ₀ : Fin N₀ → Fin d)
      (φ ψ : Fin D → ℂ) (μ ν : ℂ) (m_blocked : ℕ),
      φ ≠ 0 ∧ ψ ≠ 0 ∧ μ ≠ 0 ∧ ν ≠ 0 ∧
      evalWord A (List.ofFn σ₀) *ᵥ φ = μ • φ ∧
      (evalWord A (List.ofFn τ₀))ᵀ *ᵥ ψ = ν • ψ ∧
      Matrix.vecMulVec φ ψ ∈
        wordSpan (blockTensor (d := d) (D := D) A N₀) m_blocked := by
  change Kraus.wordSpan A N₀ = ⊤ at hN₀
  exact Kraus.exists_rankOne_mem_wordSpan_blockTensor A hN₀ hN₀pos

/-- **Wielandt Lemma 2(b), unconditional version.**

For any normal MPS tensor `A` with positive bond dimension, some fixed-length
word span is the full matrix algebra. -/
theorem wielandt_lemma2b [NeZero D]
    (A : MPSTensor d D) (hN : IsNormal A) :
    ∃ N : ℕ, wordSpan A N = ⊤ := by
  classical
  obtain ⟨N₀, hN₀pos, hN₀⟩ := hN
  obtain ⟨σ₀, τ₀, φ, ψ, μ, ν, m_blocked,
      hφ, hψ, hμ, hν, heigφ, heigψ, hRankOne⟩ :=
    exists_rankOne_mem_wordSpan_blockTensor A hN₀ hN₀pos
  exact ⟨(D - 1 + (m_blocked + (D - 1))) * N₀,
    wielandt_blocked_assembly A ⟨N₀, hN₀pos, hN₀⟩ N₀ hN₀pos
      σ₀ φ hφ μ hμ heigφ
      τ₀ ψ hψ ν hν heigψ hRankOne⟩

end MPSTensor
