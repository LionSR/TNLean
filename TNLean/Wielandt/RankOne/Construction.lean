/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.Wielandt.RankOne.Construction
import TNLean.Wielandt.SpanGrowth.VectorToMatrixSpan

/-!
# Rank-one construction for MPS tensors

This file preserves the established `MPSTensor` interface to the channel-generic
rank-one construction results in `Kraus`. The normality corollary remains here
because it uses the MPS normality predicate.
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- The pointwise transpose of an MPS tensor. -/
noncomputable def transposeTensor (A : MPSTensor d D) : MPSTensor d D :=
  Kraus.transposeFamily A

/-- Transposing a word product reverses the word. -/
theorem evalWord_transpose (A : MPSTensor d D) :
    ∀ w : List (Fin d), (evalWord A w)ᵀ = evalWord (transposeTensor A) w.reverse := by
  simpa [transposeTensor] using Kraus.evalWord_transpose A

/-- `N`-block injectivity is preserved by pointwise transposition. -/
theorem IsNBlkInjective_transposeTensor
    {A : MPSTensor d D} {N : ℕ}
    (h : IsNBlkInjective (d := d) (D := D) A N) :
    IsNBlkInjective (d := d) (D := D) (transposeTensor A) N := by
  change Kraus.wordSpan A N = ⊤ at h
  change Kraus.wordSpan (Kraus.transposeFamily A) N = ⊤
  exact Kraus.wordSpan_transposeFamily_eq_top_of_wordSpan_eq_top A h

/-- The cumulative span of the transposed tensor also reaches top. -/
theorem cumulativeSpan_transposeTensor_eq_top_of_cumulativeSpan_eq_top
    (A : MPSTensor d D) {N : ℕ}
    (h : cumulativeSpan A N = ⊤) :
    cumulativeSpan (transposeTensor A) N = ⊤ := by
  change Kraus.cumulativeSpan (Kraus.transposeFamily A) N = ⊤
  exact Kraus.cumulativeSpan_transposeFamily_eq_top_of_cumulativeSpan_eq_top A h

/-- The linear map `M ↦ ψ ᵥ* M` for a fixed row vector `ψ`. -/
noncomputable def vecMulLinearMap (ψ : Fin D → ℂ) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] (Fin D → ℂ) :=
  Kraus.vecMulLinearMap ψ

/-- The span of row vectors obtained by right multiplication with words of length `n`. -/
noncomputable def rowSpreadSpan
    (A : MPSTensor d D) (ψ : Fin D → ℂ) (n : ℕ) :
    Submodule ℂ (Fin D → ℂ) :=
  Kraus.rowSpreadSpan A ψ n

/-- Row spreading is vector spreading for the pointwise-transposed tensor. -/
theorem rowSpreadSpan_eq_vectorSpreadSpan_transpose
    (A : MPSTensor d D) (ψ : Fin D → ℂ) (n : ℕ) :
    rowSpreadSpan A ψ n = vectorSpreadSpan (fun i ↦ (A i)ᵀ) ψ n := by
  simpa [rowSpreadSpan, transposeTensor] using
    Kraus.rowSpreadSpan_eq_vectorSpreadSpan_transpose A ψ n

/-- Mapping `wordSpan` along `M ↦ ψ ᵥ* M` yields `rowSpreadSpan`. -/
theorem map_wordSpan_eq_rowSpreadSpan
    (A : MPSTensor d D) (ψ : Fin D → ℂ) (n : ℕ) :
    Submodule.map (vecMulLinearMap (D := D) ψ) (wordSpan A n) =
      rowSpreadSpan A ψ n :=
  Kraus.map_wordSpan_eq_rowSpreadSpan A ψ n

/-- Full row spread realizes every standard basis row by a word-span matrix. -/
theorem exists_wordSpan_vecMul_eq_pi_single
    (A : MPSTensor d D) (ψ : Fin D → ℂ) {n : ℕ}
    (hRow : rowSpreadSpan A ψ n = ⊤) (j : Fin D) :
    ∃ M : Matrix (Fin D) (Fin D) ℂ,
      M ∈ wordSpan A n ∧ Matrix.vecMul ψ M = Pi.single j (1 : ℂ) :=
  Kraus.exists_wordSpan_vecMul_eq_pi_single A ψ hRow j

/-- Cumulative spanning and a nonzero transpose eigenvector imply full row spread. -/
theorem rowSpreadSpan_eq_top_of_cumulativeSpan_eq_top_of_eigenvector_transpose
    [NeZero D]
    (A : MPSTensor d D) (ψ : Fin D → ℂ) (hψ : ψ ≠ 0)
    (i₁ : Fin d) (ν : ℂ) (hν : ν ≠ 0)
    (heigψ : (A i₁)ᵀ *ᵥ ψ = ν • ψ)
    {N : ℕ} (hCum : cumulativeSpan A N = ⊤) :
    rowSpreadSpan A ψ (D - 1) = ⊤ :=
  Kraus.rowSpreadSpan_eq_top_of_cumulativeSpan_eq_top_of_eigenvector_transpose
    A ψ hψ i₁ ν hν heigψ hCum

/-- If `A` is normal, a nonzero transpose eigenvector spreads all rows at level `D - 1`. -/
theorem rowSpreadSpan_eq_top_of_isNormal_of_eigenvector_transpose
    [NeZero D]
    (A : MPSTensor d D) (ψ : Fin D → ℂ) (hψ : ψ ≠ 0)
    (i₀ : Fin d) (μ : ℂ) (hμ : μ ≠ 0)
    (heig : (A i₀)ᵀ *ᵥ ψ = μ • ψ)
    (hNormal : IsNormal (d := d) (D := D) A) :
    rowSpreadSpan A ψ (D - 1) = ⊤ := by
  obtain ⟨N, hCum⟩ := cumulativeSpan_eq_top_of_isNormal A hNormal
  exact rowSpreadSpan_eq_top_of_cumulativeSpan_eq_top_of_eigenvector_transpose
    A ψ hψ i₀ μ hμ heig hCum

/-- One rank-one word-span element and full row spread yield the rank-one basis. -/
theorem vecMulVec_pi_single_mem_wordSpan_of_rankOne
    (A : MPSTensor d D) (φ ψ : Fin D → ℂ) {m k : ℕ}
    (hRankOne : Matrix.vecMulVec φ ψ ∈ wordSpan A m)
    (hRow : rowSpreadSpan A ψ k = ⊤) :
    ∀ j : Fin D,
      Matrix.vecMulVec φ (Pi.single j (1 : ℂ)) ∈ wordSpan A (m + k) :=
  Kraus.vecMulVec_pi_single_mem_wordSpan_of_rankOne A φ ψ hRankOne hRow

/-- Vector spread, one rank-one element, and row spread imply full matrix span. -/
theorem wordSpan_eq_top_of_vectorSpreadSpan_eq_top_of_rankOne
    (A : MPSTensor d D) (φ ψ : Fin D → ℂ) {n m k : ℕ}
    (hVec : vectorSpreadSpan A φ n = ⊤)
    (hRankOne : Matrix.vecMulVec φ ψ ∈ wordSpan A m)
    (hRow : rowSpreadSpan A ψ k = ⊤) :
    wordSpan A (n + (m + k)) = ⊤ :=
  Kraus.wordSpan_eq_top_of_vectorSpreadSpan_eq_top_of_rankOne
    A φ ψ hVec hRankOne hRow

end MPSTensor
