/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Kraus.Injectivity
import TNLean.Kraus.Wielandt.SpanGrowth.VectorToMatrixSpan

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.Matrix.Mul

/-!
# Rectangular spans of finite matrix families

This module contains the channel-generic rectangular-span construction used in the
Quantum Wielandt bound and the conditional fixed-length matrix-spanning theorem
from Sanz, Pérez-García, Wolf, and Cirac, arXiv:0909.5347, Lemma 2(b).
-/

open scoped Matrix

namespace List

/-- Reversing `List.ofFn` precomposes the indexing function with `Fin.rev`. -/
private theorem ofFn_reverse {n : ℕ} {α : Type*} (f : Fin n → α) :
    (List.ofFn f).reverse = List.ofFn (f ∘ Fin.rev) := by
  calc
    (List.ofFn f).reverse = (List.map f (List.finRange n)).reverse := by
      simp only [List.ofFn_eq_map]
    _ = List.map f (List.finRange n).reverse := by simp only [List.map_reverse]
    _ = List.map f (List.map Fin.rev (List.finRange n)) := by
      simp only [List.finRange_reverse]
    _ = List.map (f ∘ Fin.rev) (List.finRange n) := by simp only [List.map_map]
    _ = List.ofFn (f ∘ Fin.rev) := by simp only [List.ofFn_eq_map]

end List

namespace Kraus

variable {d D : ℕ}

/-! ## Rectangular spans -/

/-- The rectangular span is the image of `wordSpan K n` under left multiplication
by a fixed matrix `P`. -/
noncomputable def rectSpan
    (P : Matrix (Fin D) (Fin D) ℂ)
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (n : ℕ) :
    Submodule ℂ (Matrix (Fin D) (Fin D) ℂ) :=
  Submodule.map (LinearMap.mulLeft ℂ P) (wordSpan K n)

/-- `rectSpan P K n ≤ wordSpan K (m + n)` when `P ∈ wordSpan K m`. -/
theorem rectSpan_le_wordSpan
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) {m n : ℕ}
    (P : Matrix (Fin D) (Fin D) ℂ) (hP : P ∈ wordSpan K m) :
    rectSpan P K n ≤ wordSpan K (m + n) := by
  intro M hM
  obtain ⟨Q, hQ, rfl⟩ := Submodule.mem_map.mp hM
  simp only [LinearMap.mulLeft_apply]
  exact (wordSpan_mul_le K m n) (Submodule.mul_mem_mul hP hQ)

/-! ## Transposed word spans -/

/-- Transposing a word product reverses the word. -/
private theorem evalWord_transpose
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) :
    ∀ w : List (Fin d),
      (MPSTensor.evalWord K w)ᵀ =
        MPSTensor.evalWord (fun i ↦ (K i)ᵀ) w.reverse := by
  intro w
  induction w with
  | nil => simp [MPSTensor.evalWord]
  | cons i w ih =>
      simp [MPSTensor.evalWord, Matrix.transpose_mul, ih, MPSTensor.evalWord_append]

/-- Transposition identifies the fixed-length word spans of a family and its transpose. -/
private theorem map_transpose_wordSpan
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (n : ℕ) :
    Submodule.map
        (Matrix.transposeLinearEquiv (Fin D) (Fin D) ℂ ℂ :
          Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
        (wordSpan K n) =
      wordSpan (fun i ↦ (K i)ᵀ) n := by
  unfold wordSpan
  rw [Submodule.map_span]
  congr 1
  ext M
  constructor
  · rintro ⟨_, ⟨σ, rfl⟩, rfl⟩
    refine ⟨σ ∘ Fin.rev, ?_⟩
    have hrev : ((σ ∘ Fin.rev) ∘ Fin.rev) = σ := by
      funext i
      simpa only [Function.comp_apply] using congrArg σ (Fin.rev_rev i)
    simpa [List.ofFn_reverse, hrev] using
      (evalWord_transpose K (List.ofFn σ)).symm
  · rintro ⟨σ, rfl⟩
    refine ⟨MPSTensor.evalWord K (List.ofFn (σ ∘ Fin.rev)), ⟨σ ∘ Fin.rev, rfl⟩, ?_⟩
    have hrev : ((σ ∘ Fin.rev) ∘ Fin.rev) = σ := by
      funext i
      simpa only [Function.comp_apply] using congrArg σ (Fin.rev_rev i)
    simpa [List.ofFn_reverse, hrev] using
      evalWord_transpose K (List.ofFn (σ ∘ Fin.rev))

/-! ## Conditional fixed-length matrix spanning -/

/-- **Lemma 2(b), conditional fixed-length matrix spanning.**

If a normal finite matrix family has nonzero right and transpose eigenvectors at
single indices, and one rank-one matrix belongs to a bounded fixed-length word
span, then a fixed-length word span is the full matrix algebra.

This is the conditional algebraic step in arXiv:0909.5347, Lemma 2(b). -/
theorem wielandt_lemma2b_conditional [NeZero D]
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hNormal : MPSTensor.IsNormal K)
    (i₀ : Fin d) (μ : ℂ) (hμ : μ ≠ 0)
    (φ : Fin D → ℂ) (hφ : φ ≠ 0)
    (heigφ : K i₀ *ᵥ φ = μ • φ)
    (i₁ : Fin d) (ν : ℂ) (hν : ν ≠ 0)
    (ψ : Fin D → ℂ) (hψ : ψ ≠ 0)
    (heigψ : (K i₁)ᵀ *ᵥ ψ = ν • ψ)
    {m : ℕ} (hRankOne : Matrix.vecMulVec φ ψ ∈ wordSpan K m) :
    wordSpan K ((D - 1) + (m + (D - 1))) = ⊤ := by
  obtain ⟨N, _hNpos, hN⟩ := hNormal
  have hWord : wordSpan K N = ⊤ := by
    simpa [wordSpan, MPSTensor.IsNBlkInjective] using hN
  have hCum : cumulativeSpan K N = ⊤ := by
    apply eq_top_iff.mpr
    rw [← hWord]
    exact wordSpan_le_cumulativeSpan K le_rfl
  have hCumVec : cumulativeVectorSpan K φ (D - 1) = ⊤ :=
    eigenvector_spreading_of_cumulativeSpan_eq_top K φ hφ hCum
  have hVec : vectorSpreadSpan K φ (D - 1) = ⊤ :=
    vectorSpreadSpan_eq_top_of_cumulativeVectorSpan_eq_top_of_eigenvector
      K φ (D - 1) i₀ μ hμ heigφ hCumVec
  let KT : Fin d → Matrix (Fin D) (Fin D) ℂ := fun i ↦ (K i)ᵀ
  have hWordT : wordSpan KT N = ⊤ := by
    have hmap := map_transpose_wordSpan K N
    rw [hWord, Submodule.map_top] at hmap
    simpa [KT] using hmap.symm
  have hCumT : cumulativeSpan KT N = ⊤ := by
    apply eq_top_iff.mpr
    rw [← hWordT]
    exact wordSpan_le_cumulativeSpan KT le_rfl
  have hCumVecT : cumulativeVectorSpan KT ψ (D - 1) = ⊤ :=
    eigenvector_spreading_of_cumulativeSpan_eq_top KT ψ hψ hCumT
  have hVecT : vectorSpreadSpan KT ψ (D - 1) = ⊤ :=
    vectorSpreadSpan_eq_top_of_cumulativeVectorSpan_eq_top_of_eigenvector
      KT ψ (D - 1) i₁ ν hν (by simpa [KT] using heigψ) hCumVecT
  have hRankOneBasis : ∀ j : Fin D,
      Matrix.vecMulVec φ (Pi.single j (1 : ℂ)) ∈ wordSpan K (m + (D - 1)) := by
    intro j
    have hj : Pi.single j (1 : ℂ) ∈ vectorSpreadSpan KT ψ (D - 1) := by
      rw [hVecT]
      exact Submodule.mem_top
    rw [← map_wordSpan_eq_vectorSpreadSpan KT ψ (D - 1)] at hj
    obtain ⟨M, hM, hMψ⟩ := hj
    have hMT : Mᵀ ∈ wordSpan K (D - 1) := by
      have hmem : Mᵀ ∈
          Submodule.map
            (Matrix.transposeLinearEquiv (Fin D) (Fin D) ℂ ℂ :
              Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
            (wordSpan KT (D - 1)) := by
        exact Submodule.mem_map.mpr ⟨M, hM, rfl⟩
      rw [map_transpose_wordSpan KT (D - 1)] at hmem
      simpa [KT] using hmem
    have hprod : Matrix.vecMulVec φ ψ * Mᵀ ∈ wordSpan K (m + (D - 1)) :=
      (wordSpan_mul_le K m (D - 1)) (Submodule.mul_mem_mul hRankOne hMT)
    have hrow : Matrix.vecMul ψ Mᵀ = Pi.single j (1 : ℂ) := by
      rw [Matrix.vecMul_transpose]
      simpa [mulVecLinearMap] using hMψ
    simpa [Matrix.vecMulVec_mul, hrow] using hprod
  exact wordSpan_eq_top_of_vectorSpreadSpan_eq_top_of_rankOneBasis
    K φ hVec hRankOneBasis

end Kraus
