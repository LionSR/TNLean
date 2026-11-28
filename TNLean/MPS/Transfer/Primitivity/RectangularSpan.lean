/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.Wielandt.RankOne.BoundedWord
import QICLean.Kraus.Wielandt.RectangularSpan.Basic
import QICLean.Kraus.Injectivity
import QICLean.Kraus.Word
import TNLean.MPS.Tensor.Physical.Blocking
import TNLean.MPS.Tensor.Words.WordSpan
import Mathlib.Data.Fin.Tuple.Basic
import QICLean.Kraus.Wielandt.RankOne.Construction
import QICLean.Kraus.Wielandt.RectangularSpan.Growth
import QICLean.Algebra.Matrix.MatrixMulRange
import QICLean.Kraus.Wielandt.RectangularSpan.Universality
import QICLean.Kraus.Wielandt.RectangularSpan.UniversalityAux.Basic
import QICLean.Kraus.Wielandt.RectangularSpan.UniversalityAux.NilpIndex
import QICLean.Kraus.Wielandt.RectangularSpan.UniversalityAux.Sharp

/-!
# Rectangular Span Foundations: Lemma 2(b) (blocked fixed-length matrix spanning)

This module contains the foundational rectangular-span theory used in the Wielandt
bound: the basic one-sided rectangular span and the blocked fixed-length matrix
spanning theorem for Lemma 2(b).

The later growth, stabilization, universality, and sharp quantitative theorems
live in `TNLean.Wielandt.RectangularSpan.Growth` and
`TNLean.Wielandt.RectangularSpan.Universality`.

## Main results

- `Kraus.rectSpan`
- `wielandt_blocked_assembly`

## Full rank-one extraction for MPS tensors

This file preserves the paper-facing MPS rank-one extraction theorem and proves
Wielandt Lemma 2(b). The finite-family construction is in
`TNLean.Kraus.Wielandt.RankOne.ExtractionFull`.

### References

- arXiv:0909.5347, Lemma 2(b)

## Rectangular span growth for matrix product tensors

The rectangular-span growth and stabilization results hold for arbitrary finite
matrix families. This module restates them for matrix product tensors.

## Rectangular span universality compatibility names

Transfer-free results are proved for arbitrary finite matrix families in the corresponding
`Kraus` module. The three normality capstones remain specific to matrix product tensors.
-/

section

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-! ## Blocked fixed-length matrix spanning -/

/-- **Fixed-length matrix spanning at the blocked level.**

Reduces the Wielandt bound to producing a rank-one element in the word
span of the **blocked** tensor. The blocking period `L` absorbs the
word lengths of both the column and row eigenvectors.

### Conclusion:
`Kraus.wordSpan A ((D - 1 + (m_blocked + (D - 1))) * L) = ⊤`. -/
theorem wielandt_blocked_assembly [NeZero D]
    (A : MPSTensor d D)
    (hNormal : Kraus.IsNormal (ι := Fin d) (n := Fin D) A)
    (L : ℕ) (hL : 0 < L)
    (σ₀ : Fin L → Fin d)
    (φ : Fin D → ℂ) (hφ : φ ≠ 0)
    (μ : ℂ) (hμ : μ ≠ 0)
    (heigφ : Kraus.evalWord A (List.ofFn σ₀) *ᵥ φ = μ • φ)
    (τ₀ : Fin L → Fin d)
    (ψ : Fin D → ℂ) (hψ : ψ ≠ 0)
    (ν : ℂ) (hν : ν ≠ 0)
    (heigψ : (Kraus.evalWord A (List.ofFn τ₀))ᵀ *ᵥ ψ = ν • ψ)
    {m_blocked : ℕ}
    (hRankOne :
      Matrix.vecMulVec φ ψ ∈ Kraus.wordSpan (Kraus.block A L) m_blocked) :
    Kraus.wordSpan A ((D - 1 + (m_blocked + (D - 1))) * L) = ⊤ := by
  -- The Wielandt step is stated for numbered letters: number the blocks of length `L`.
  set e := Kraus.decodeBlockEquiv d L
  set B := Kraus.reindexPhysical e (Kraus.block A L)
  have hWS : ∀ k, Kraus.wordSpan B k = Kraus.wordSpan A (k * L) := fun k ↦ by
    rw [Kraus.wordSpan_eq_of_range_eq (K := B) (e.surjective.range_comp _), Kraus.wordSpan_block]
  have hB : ∀ σ : Fin L → Fin d, B (e.symm σ) = Kraus.evalWord A (List.ofFn σ) := fun σ ↦ by
    simp [B, Kraus.reindexPhysical]
  have heigφ_B : B (e.symm σ₀) *ᵥ φ = μ • φ := by rw [hB]; exact heigφ
  have heigψ_B : (B (e.symm τ₀))ᵀ *ᵥ ψ = ν • ψ := by rw [hB]; exact heigψ
  have hNormalB : Kraus.IsNormal B := by
    obtain ⟨N, hNpos, hN⟩ := hNormal.block hL
    refine ⟨N, hNpos, ?_⟩
    change Kraus.wordSpan B N = ⊤
    rw [hWS, ← Kraus.wordSpan_block]
    exact hN
  have hRankOneB : Matrix.vecMulVec φ ψ ∈ Kraus.wordSpan B m_blocked := by
    rwa [hWS, ← Kraus.wordSpan_block]
  have hBtop : Kraus.wordSpan B ((D - 1) + (m_blocked + (D - 1))) = ⊤ :=
    Kraus.wielandt_lemma2b_conditional B hNormalB (e.symm σ₀) μ hμ φ hφ heigφ_B
      (e.symm τ₀) ν hν ψ hψ heigψ_B hRankOneB
  rwa [hWS] at hBtop

end MPSTensor

end

section

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- **Full rank-one extraction for Wielandt Lemma 2(b).**

Under a positive normality witness, this produces nonzero right and transpose
eigenvectors and a rank-one element in a bounded word span of the blocked tensor. -/
theorem exists_rankOne_mem_wordSpan_block [NeZero D]
    (A : MPSTensor d D) {N₀ : ℕ} (hN₀ : Kraus.IsNBlkInjective A N₀) (hN₀pos : 0 < N₀) :
    ∃ (σ₀ τ₀ : Fin N₀ → Fin d)
      (φ ψ : Fin D → ℂ) (μ ν : ℂ) (m_blocked : ℕ),
      φ ≠ 0 ∧ ψ ≠ 0 ∧ μ ≠ 0 ∧ ν ≠ 0 ∧
      Kraus.evalWord A (List.ofFn σ₀) *ᵥ φ = μ • φ ∧
      (Kraus.evalWord A (List.ofFn τ₀))ᵀ *ᵥ ψ = ν • ψ ∧
      Matrix.vecMulVec φ ψ ∈ Kraus.wordSpan (Kraus.block A N₀) m_blocked := by
  change Kraus.wordSpan A N₀ = ⊤ at hN₀
  simpa only [Kraus.wordSpan_eq_of_range_eq (Kraus.range_blockTensor A N₀)] using
    Kraus.exists_rankOne_mem_wordSpan_blockTensor A hN₀ hN₀pos

/-- **Wielandt Lemma 2(b), unconditional version.**

For any normal MPS tensor `A` with positive bond dimension, some fixed-length
word span is the full matrix algebra. -/
theorem wielandt_lemma2b [NeZero D]
    (A : MPSTensor d D) (hN : Kraus.IsNormal A) :
    ∃ N : ℕ, Kraus.wordSpan A N = ⊤ := by
  classical
  obtain ⟨N₀, hN₀pos, hN₀⟩ := hN
  obtain ⟨σ₀, τ₀, φ, ψ, μ, ν, m_blocked,
      hφ, hψ, hμ, hν, heigφ, heigψ, hRankOne⟩ :=
    exists_rankOne_mem_wordSpan_block A hN₀ hN₀pos
  exact ⟨(D - 1 + (m_blocked + (D - 1))) * N₀,
    wielandt_blocked_assembly A ⟨N₀, hN₀pos, hN₀⟩ N₀ hN₀pos
      σ₀ φ hφ μ hμ heigφ
      τ₀ ψ hψ ν hν heigψ hRankOne⟩

end MPSTensor

end

section

open scoped Matrix

namespace MPSTensor

open Module

variable {d D : ℕ}

/-- Under normality, some rectangular span equals the full range of left
multiplication. -/
theorem exists_rectSpan_eq_range_of_isNormal
    (P : Matrix (Fin D) (Fin D) ℂ) (A : MPSTensor d D)
    (hN : Kraus.IsNormal A) :
    ∃ n, Kraus.rectSpan P A n = LinearMap.range (LinearMap.mulLeft ℂ P) := by
  obtain ⟨N₀, _hN₀pos, hN₀⟩ := hN
  exact ⟨N₀, Kraus.rectSpan_eq_range_of_wordSpan_eq_top P A hN₀⟩

end MPSTensor

end

section

open scoped Matrix
namespace MPSTensor
open Module Matrix Wielandt
variable {d D : ℕ}

/-- Under normality, the sharp rank-one conclusion holds at the exact word length. -/
theorem vecMulVec_eigenvector_exact_wordSpan [NeZero D]
    (A : MPSTensor d D) (i₀ : Fin d) (hN : Kraus.IsNormal A)
    (hNotInv : ¬ IsUnit (toLin' (A i₀))) {φ : Fin D → ℂ} {μ : ℂ} (hμ : μ ≠ 0)
    (heig : A i₀ *ᵥ φ = μ • φ) :
    ∀ ψ : Fin D → ℂ, vecMulVec φ ψ ∈ Kraus.wordSpan A (D ^ 2 - D + 1) := by
  intro ψ
  set r := nilpIndex (toLin' (A i₀))
  have hStrict : ∀ n,
      finrank ℂ (Kraus.rectSpan ((A i₀) ^ r) A n) < D * ((A i₀) ^ D).rank →
      finrank ℂ (Kraus.rectSpan ((A i₀) ^ r) A n) <
        finrank ℂ (Kraus.rectSpan ((A i₀) ^ r) A (n + 1)) :=
    fun n hlt => Kraus.rectSpan_nilpIndex_strict_growth_of_isNormal A i₀ hN n hlt
  obtain ⟨n₀, hn₀, hstab⟩ :=
    Kraus.rectSpan_nilpIndex_eq_range_of_strict_growth A i₀ hStrict
  have hmem : vecMulVec φ ψ ∈ Kraus.wordSpan A (r + n₀) :=
    Kraus.vecMulVec_eigenvector_mem_wordSpan_nilpIndex A i₀ hμ heig hstab ψ
  have hbound : r + n₀ ≤ D ^ 2 - D + 1 := by
    calc
      r + n₀ ≤ r + D * ((A i₀) ^ D).rank := Nat.add_le_add_left hn₀ _
      _ = D * ((A i₀) ^ D).rank + r := by ring
      _ ≤ D ^ 2 - D + 1 := Kraus.sharp_bound_le A i₀ hNotInv
  exact Kraus.vecMulVec_eigenvector_mem_wordSpan_of_le A i₀ hμ heig hbound hmem

end MPSTensor

end
