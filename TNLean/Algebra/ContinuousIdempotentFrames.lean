/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Structure.ContinuousTraceQuotientMultiplication
import TNLean.Algebra.IdempotentRankContinuity
import TNLean.Algebra.MatrixGramLeftInverse

/-!
# Continuous frames for the ranges of idempotents

A continuous complex matrix family of constant rank admits a fixed local section.
Multiplication of this section by the matrix gives a continuous frame C. Its
Hermitian Gram matrix is positive definite, so H=(C†C)⁻¹C† is a continuous left
inverse. The frame need not be isometric. In particular, this construction applies
to non-Hermitian idempotents, whose ranks are locally constant.

Auxiliary context: arXiv:1010.3732, Section II.F.2, lines 953–993.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

namespace Matrix

/-- A continuous constant-rank matrix family admits a continuous local frame
and a continuous left inverse, both explicitly obtained from a fixed section. -/
theorem exists_open_continuous_rangeFrame_of_constantRank
    {T : Type*} [TopologicalSpace T] {n D : ℕ}
    (P : T → Matrix (Fin n) (Fin n) ℂ) (hP : Continuous P)
    (hRank : ∀ t, (P t).rank = D) (t₀ : T) :
    ∃ (F : Matrix (Fin n) (Fin D) ℂ) (S : Set T), IsOpen S ∧ t₀ ∈ S ∧
      ContinuousOn (fun t => P t * F) S ∧
      ContinuousOn (fun t => ((P t * F)ᴴ * (P t * F))⁻¹ * (P t * F)ᴴ) S ∧
      ∀ t ∈ S, Function.Injective (P t * F).mulVec ∧
        LinearMap.range (P t * F).mulVecLin = LinearMap.range (P t).mulVecLin ∧
        (((P t * F)ᴴ * (P t * F))⁻¹ * (P t * F)ᴴ) * (P t * F) = 1 := by
  obtain ⟨F, hF⟩ := exists_fixedSection_of_rank (P t₀) (hRank t₀)
  obtain ⟨S, hS, ht₀, hSection⟩ :=
    exists_open_fixedSection_range P hP hRank t₀ F hF
  have hH : ContinuousOn
      (fun t => ((P t * F)ᴴ * (P t * F))⁻¹ * (P t * F)ᴴ) S := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact continuous_gramLeftInverse (fun t : S => P t * F)
      ((hP.comp continuous_subtype_val).matrix_mul continuous_const)
      (fun t => (hSection t t.property).1)
  exact ⟨F, S, hS, ht₀, (hP.matrix_mul continuous_const).continuousOn,
    hH, fun t ht => ⟨(hSection t ht).1, (hSection t ht).2,
      gramLeftInverse_mul _ (hSection t ht).1⟩⟩

/-- The ranges of continuous complex idempotents admit continuous local frames
and continuous Gram left inverses. Neither Hermiticity nor positive rank is required. -/
theorem exists_local_continuous_rangeFrame_of_idempotent
    {T : Type*} [TopologicalSpace T] {n D : ℕ}
    (P : T → Matrix (Fin n) (Fin n) ℂ) (hP : Continuous P)
    (hIdem : ∀ t, IsIdempotentElem (P t)) (t₀ : T) (hRank : (P t₀).rank = D) :
    ∃ S : Set T, IsOpen S ∧ t₀ ∈ S ∧
      ∃ (F : Matrix (Fin n) (Fin D) ℂ)
        (C : S → Matrix (Fin n) (Fin D) ℂ)
        (H : S → Matrix (Fin D) (Fin n) ℂ),
        Continuous C ∧ Continuous H ∧ ∀ t,
          C t = P t * F ∧ H t = ((C t)ᴴ * C t)⁻¹ * (C t)ᴴ ∧
          Function.Injective (C t).mulVec ∧
          LinearMap.range (C t).mulVecLin = LinearMap.range (P t).mulVecLin ∧
          H t * C t = 1 ∧ P t * C t = C t := by
  obtain ⟨s, hsopen, ht₀, hsRank⟩ :=
    exists_open_constantRank_of_idempotent P hP hIdem t₀
  obtain ⟨F, q, hqopen, hp₀, hC, hH, hdata⟩ :=
    exists_open_continuous_rangeFrame_of_constantRank
      (fun t : s => P t) (hP.comp continuous_subtype_val)
      (fun t => (hsRank t t.property).trans hRank) (⟨t₀, ht₀⟩ : s)
  let w : Set T := Subtype.val '' q
  have hSub : w ⊆ s := by
    rintro t ⟨p, _, rfl⟩
    exact p.property
  let j₀ : w → s := fun t => ⟨t.val, hSub t.property⟩
  have hjq : ∀ t, j₀ t ∈ q := by
    rintro ⟨t, ⟨p, hp, rfl⟩⟩
    exact hp
  let j : w → q := fun t => ⟨j₀ t, hjq t⟩
  have hInj : ∀ t : w, Function.Injective (P t * F).mulVec :=
    fun t => (hdata (j t).val (j t).property).1
  have hCcont : Continuous (fun t : w => P t * F) :=
    (hP.comp continuous_subtype_val).matrix_mul continuous_const
  refine ⟨w, hsopen.isOpenMap_subtype_val q hqopen,
    ⟨(⟨t₀, ht₀⟩ : s), hp₀, rfl⟩, F,
    (fun t : w => P t * F),
    (fun t : w => ((P t * F)ᴴ * (P t * F))⁻¹ * (P t * F)ᴴ),
    hCcont, continuous_gramLeftInverse _ hCcont hInj, ?_⟩
  refine fun t => ⟨rfl, rfl, hInj t,
    (hdata (j t).val (j t).property).2.1,
    gramLeftInverse_mul _ (hInj t), ?_⟩
  exact (Matrix.mul_assoc _ _ _).symm.trans (congrArg (· * F) (hIdem t).eq)

end Matrix
