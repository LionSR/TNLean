import MPSLean.Defs
import MPSLean.TraceNondeg

import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Trace pairing tools for MPS

This file provides the basic linear-algebraic tools built around the trace pairing
on square matrices that are used throughout the proof of the Fundamental Theorem.

## Main definitions and results

* `MPSTensor.traceMulRightPi` — the linear map `M ↦ (i ↦ trace (M * A i))`
* `MPSTensor.SameMPV.trace_evalWord` — `SameMPV` implies trace agreement on all words
* `MPSTensor.sameMPV_trace_word2` — specialisation to length-2 words
* `MPSTensor.traceMulRightPi_ker_eq_bot` — injectivity of `traceMulRightPi` when `A` is injective
* `MPSTensor.ker_bot_of_range_le` — finrank transfer: range inclusion + injectivity ⟹ injectivity
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- Lemma 2 (paper proof sketch): `SameMPV` implies agreement of traces of all products.

We formulate this directly for `evalWord` on arbitrary lists. -/
lemma SameMPV.trace_evalWord {A B : MPSTensor d D} (h : SameMPV A B) (w : List (Fin d)) :
    Matrix.trace (evalWord A w) = Matrix.trace (evalWord B w) := by
  -- Use the `SameMPV` equality on the configuration `σ := w.get`.
  simpa [mpv, coeff, List.ofFn_get] using h w.length w.get

/-- Lemma 3 (helper): nondegeneracy of the trace pairing on `D×D` complex matrices. -/
lemma trace_mul_right_eq_zero {M : Matrix (Fin D) (Fin D) ℂ}
    (h : ∀ N : Matrix (Fin D) (Fin D) ℂ, Matrix.trace (M * N) = 0) : M = 0 := by
  simpa using (Matrix.trace_mul_right_eq_zero_iff (n := Fin D) M).1 h

/-- The linear map `M ↦ (i ↦ trace (M * A i))`. -/
noncomputable def traceMulRightPi (A : MPSTensor d D) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] (Fin d → ℂ) :=
  LinearMap.pi fun i : Fin d =>
    (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp (LinearMap.mulRight ℂ (A i))

@[simp]
lemma traceMulRightPi_apply (A : MPSTensor d D)
    (M : Matrix (Fin D) (Fin D) ℂ) (i : Fin d) :
    traceMulRightPi A M i = Matrix.trace (M * A i) := by
  simp [traceMulRightPi, Matrix.traceLinearMap_apply]

/-- `SameMPV` implies agreement of traces for all length-2 words. -/
lemma sameMPV_trace_word2 {A B : MPSTensor d D} (hAB : SameMPV A B) (i j : Fin d) :
    Matrix.trace (A i * A j) = Matrix.trace (B i * B j) := by
  have h := hAB.trace_evalWord [i, j]
  simpa [evalWord, Matrix.mul_assoc] using h

/-- If `A` is injective, then `traceMulRightPi A` has trivial kernel.

The proof uses nondegeneracy of the trace pairing: if `trace (M * A i) = 0` for all `i`,
and the `A i` span the full matrix algebra, then `trace (M * N) = 0` for all `N`, hence `M = 0`. -/
theorem traceMulRightPi_ker_eq_bot {A : MPSTensor d D} (hA : IsInjective A) :
    (traceMulRightPi A).ker = ⊥ := by
  classical
  apply (LinearMap.ker_eq_bot').2
  intro M hM
  -- The linear functional `N ↦ trace (M * N)` vanishes on the spanning set `{A i}`, hence is zero.
  have hφ : (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp (LinearMap.mulLeft ℂ M) = 0 := by
    apply LinearMap.ext_on_range (v := A) (hv := hA.span_eq_top)
    intro i
    simpa using congrArg (· i) hM
  -- Use trace nondegeneracy.
  exact trace_mul_right_eq_zero fun N => by
    simpa [Matrix.traceLinearMap_apply] using congrArg (· N) hφ

/-- **Trace doesn't vanish on injective tensors.**

If `A` is injective and `SameMPV A B`, then `B` can't be identically zero
(because trace would vanish on a spanning set, contradicting `trace 1 = D ≠ 0`).

This is the shared core of `linearExtension_nonzero` and
`perBlockLinearExtension_nonzero`. -/
theorem trace_ne_zero_of_injective [NeZero D] {A : MPSTensor d D}
    (hA : IsInjective A) (hAB : SameMPV A B) (hBzero : ∀ i, B i = 0) : False := by
  have hTraceA : ∀ i, Matrix.trace (A i) = 0 := fun i => by
    simpa [evalWord, hBzero i] using hAB.trace_evalWord [i]
  have htr_zero : Matrix.traceLinearMap (Fin D) ℂ ℂ = 0 := by
    apply LinearMap.ext_on_range (v := A) (hv := hA.span_eq_top)
    intro i; simpa [Matrix.traceLinearMap_apply] using hTraceA i
  have : Matrix.trace (1 : Matrix (Fin D) (Fin D) ℂ) = 0 := by
    simpa [Matrix.traceLinearMap_apply] using congrArg (· 1) htr_zero
  exact absurd this (by
    rw [Matrix.trace_one, Fintype.card_fin]
    exact (Nat.cast_ne_zero (R := ℂ)).2 (NeZero.ne D))

/-- If `ΦA` is injective and `range ΦA ≤ range ΦB`, then `ΦB` has trivial kernel.

This is the "finrank dance": `ker ΦA = ⊥` implies `finrank (range ΦA) = finrank V`,
and the range inclusion forces `finrank (range ΦB) ≥ finrank V`, so by rank-nullity `ker ΦB = ⊥`. -/
theorem ker_bot_of_range_le {V W : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (ΦA ΦB : V →ₗ[ℂ] W) (hKerA : ΦA.ker = ⊥) (hRange : ΦA.range ≤ ΦB.range) :
    ΦB.ker = ⊥ := by
  -- From ker ΦA = ⊥, get finrank(range ΦA) = finrank V.
  have hRN_A := LinearMap.finrank_range_add_finrank_ker (f := ΦA)
  rw [hKerA, finrank_bot] at hRN_A
  -- Range inclusion gives finrank(range ΦB) ≥ finrank V.
  have hRN_B := LinearMap.finrank_range_add_finrank_ker (f := ΦB)
  have hle : Module.finrank ℂ ↥ΦB.range ≤ Module.finrank ℂ V := LinearMap.finrank_range_le ΦB
  have hmono : Module.finrank ℂ ↥ΦA.range ≤ Module.finrank ℂ ↥ΦB.range :=
    Submodule.finrank_mono hRange
  exact (Submodule.finrank_eq_zero (S := ΦB.ker)).1 (by omega)

end MPSTensor
