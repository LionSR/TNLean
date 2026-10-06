/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.SharedInfra.WordTupleGauge

/-!
# Simultaneous one-site span under rectangular compression

The one-site word-tuple span is the span of the simultaneous letters.
Rectangular compression by a left/right inverse pair preserves this span.
The block labels and their common physical alphabet remain unchanged.

Source: GLM23, arXiv:2203.12563, Section 5, lines 1695–1777.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d r : ℕ} {dim smallDim : Fin r → ℕ}

/-- At length one, simultaneous word spanning is simultaneous letter spanning.
Source: arXiv:2203.12563, Section 5, lines 1695–1704. -/
theorem wordTupleSpanTop_one_iff
    (A : (x : Fin r) → MPSTensor d (dim x)) :
    WordTupleSpanTop A 1 ↔
      Submodule.span ℂ (Set.range fun i => fun x => A x i) = ⊤ := by
  have h : Set.range (wordTuple A 1) = Set.range (fun i => fun x => A x i) := by
    ext X
    constructor
    · rintro ⟨w, rfl⟩
      refine ⟨w 0, ?_⟩
      funext x
      simp [wordTuple, List.ofFn_succ, Kraus.evalWord]
    · rintro ⟨i, rfl⟩
      refine ⟨fun _ => i, ?_⟩
      funext x
      simp [wordTuple, List.ofFn_succ, Kraus.evalWord]
  simp only [WordTupleSpanTop, h]

/-- Compression by a rectangular inverse pair preserves simultaneous
one-site spanning. Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem wordTupleSpanTop_one_of_rectangular_compression
    (A : (x : Fin r) → MPSTensor d (dim x)) (hA : WordTupleSpanTop A 1)
    (U : (x : Fin r) → Matrix (Fin (smallDim x)) (Fin (dim x)) ℂ)
    (V : (x : Fin r) → Matrix (Fin (dim x)) (Fin (smallDim x)) ℂ)
    (hUV : ∀ x, U x * V x = 1) :
    WordTupleSpanTop (fun x i => U x * A x i * V x) 1 := by
  classical
  rw [wordTupleSpanTop_one_iff] at hA ⊢
  apply top_unique
  intro X _
  have hLift : (fun x => V x * X x * U x) ∈
      Submodule.span ℂ (Set.range fun i => fun x => A x i) := by
    rw [hA]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hLift
  apply (Submodule.mem_span_range_iff_exists_fun ℂ).mpr
  refine ⟨c, ?_⟩
  funext x
  have hx := congrArg (fun Y => U x * Y x * V x) hc
  have hcomp : U x * (V x * X x * U x) * V x = X x := by
    calc
      _ = (U x * V x) * X x * (U x * V x) := by simp only [Matrix.mul_assoc]
      _ = X x := by rw [hUV x, Matrix.one_mul, Matrix.mul_one]
  rw [hcomp] at hx
  simpa [Fintype.linearCombination_apply, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul] using hx

/-- An invertible right insertion preserves simultaneous one-site spanning.
Source: arXiv:2203.12563, Section 5, lines 1695–1704 and 1777. -/
theorem wordTupleSpanTop_one_of_right_inverse
    (A : (x : Fin r) → MPSTensor d (dim x)) (hA : WordTupleSpanTop A 1)
    (W V : (x : Fin r) → Matrix (Fin (dim x)) (Fin (dim x)) ℂ)
    (hVW : ∀ x, V x * W x = 1) :
    WordTupleSpanTop (fun x i => A x i * W x) 1 := by
  classical
  rw [wordTupleSpanTop_one_iff] at hA ⊢
  apply top_unique
  intro X _
  have hLift : (fun x => X x * V x) ∈
      Submodule.span ℂ (Set.range fun i => fun x => A x i) := by
    rw [hA]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hLift
  apply (Submodule.mem_span_range_iff_exists_fun ℂ).mpr
  refine ⟨c, ?_⟩
  funext x
  have hx := congrArg (fun Y => Y x * W x) hc
  simpa [Fintype.linearCombination_apply, Matrix.sum_mul, Matrix.smul_mul,
    Matrix.mul_assoc, hVW x] using hx

end MPSTensor
