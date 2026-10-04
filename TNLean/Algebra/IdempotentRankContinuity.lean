/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.Complex.Basic

/-!
# Local constancy of the rank of continuous idempotents

The trace of a complex idempotent equals its rank, whether or not the
idempotent is Hermitian. Since integer-valued continuous functions are locally
constant, a continuous family of idempotents has locally constant rank.
This applies to right multiplication by a continuously varying primitive
idempotent in a trace-quotient algebra.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix Matrix.Norms.L2Operator

namespace Matrix

/-- The trace of a complex idempotent is its rank. Hermiticity is unnecessary. -/
theorem trace_eq_rank_of_idempotent {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsIdempotentElem P) :
    P.trace = (P.rank : ℂ) := by
  have hLin : IsIdempotentElem P.toLin' := by
    change P.toLin'.comp P.toLin' = P.toLin'
    rw [← Matrix.toLin'_mul, hP.eq]
  have hTrace := (LinearMap.IsIdempotentElem.isProj_range _ hLin).trace
  rw [Matrix.trace_toLin'_eq] at hTrace
  rw [Matrix.toLin'_apply'] at hTrace
  simpa only [Matrix.rank] using hTrace

/-- A continuous family of complex idempotents has locally constant rank. -/
theorem exists_open_constantRank_of_idempotent
    {T : Type*} [TopologicalSpace T] {n : ℕ}
    (P : T → Matrix (Fin n) (Fin n) ℂ) (hP : Continuous P)
    (hIdem : ∀ t, IsIdempotentElem (P t)) (t₀ : T) :
    ∃ S : Set T, IsOpen S ∧ t₀ ∈ S ∧ ∀ t ∈ S, (P t).rank = (P t₀).rank := by
  have hRank : Continuous fun t => ((P t).rank : ℤ) := by
    apply Complex.isClosedEmbedding_intCast.isEmbedding.continuous_iff.mpr
    simpa only [Function.comp_def, Int.cast_natCast,
      ← trace_eq_rank_of_idempotent _ (hIdem _)] using hP.matrix_trace
  refine ⟨{t | ((P t).rank : ℤ) = ((P t₀).rank : ℤ)},
    (isOpen_discrete {((P t₀).rank : ℤ)}).preimage hRank, rfl, ?_⟩
  intro t ht
  exact_mod_cast ht

end Matrix
