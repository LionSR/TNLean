/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.FundamentalTheorem.Reduction.MultiBlock

/-!
# The word traces of a multi-block compression

The multi-block asymmetric compression theorem
(`Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`, §7.5, Theorem 7.7)
produces a compression datum from a word-trace hypothesis. This file records the converse:
every compression datum satisfies that word-trace identity, so the hypothesis of the theorem
is exactly what a compression datum delivers.

## Main results

* `MPSTensor.MultiBlockCompression.trace_evalWord_eq_sum`: the trace of a nonempty word of the
  source tensor is the sum over the slots of the traces of the corresponding words of the
  blocks.
-/

open scoped Matrix

namespace MPSTensor

/-- The trace of a matrix graded by a finite family of blocks is the sum of the traces of its
diagonal blocks. -/
theorem trace_eq_sum_blockDiag' {o : Type*} [Fintype o] {n : o → ℕ}
    (X : Matrix ((k : o) × Fin (n k)) ((k : o) × Fin (n k)) ℂ) :
    Matrix.trace X = ∑ k, Matrix.trace (X.blockDiag' k) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.blockDiag'_apply]
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]

variable {d DB : ℕ} {ι : Type*} [DecidableEq ι] {D : ι → ℕ} {B : MPSTensor d DB} {S : Finset ι}
  {C : ∀ s, MPSTensor d (D s)}

namespace MultiBlockCompression

/-- The change of bond coordinates of a multi-block compression preserves traces. -/
theorem trace_conjMatrix (P : MultiBlockCompression B S C) (A : Matrix (Fin DB) (Fin DB) ℂ) :
    Matrix.trace (conjMatrix P.gauge A) = Matrix.trace A := by
  rw [conjMatrix_eq_gaugeMatrix_mul, Matrix.trace_mul_cycle, gaugeMatrixInv_mul_gaugeMatrix,
    Matrix.one_mul]

/-- **The word-trace identity of a multi-block compression** (P5 note, Theorem 7.7, the
hypothesis of `MPSTensor.exists_multiBlockCompression_of_isNormal`). Every compression datum
reproduces the word traces of its target family: the zero slots contribute nothing to a
nonempty word, and the trace of the diagonal block of a target slot is the trace of the
corresponding word of that block. -/
theorem trace_evalWord_eq_sum (P : MultiBlockCompression B S C) (w : List (Fin d))
    (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord B w) = ∑ s ∈ S, Matrix.trace (Kraus.evalWord (C s) w) := by
  classical
  obtain ⟨i₀, w₀, rfl⟩ := List.exists_cons_of_ne_nil hw
  set T : Fin d → Matrix (BlockSpace D S P.z) (BlockSpace D S P.z) ℂ :=
    fun i => conjMatrix P.gauge (B i) with hT
  have hslot : ∀ s : {s // s ∈ S},
      Matrix.trace ((_root_.evalWord T (i₀ :: w₀)).blockDiag' (Sum.inl s)) =
        Matrix.trace (Kraus.evalWord (C s.1) (i₀ :: w₀)) := by
    intro s
    rw [Matrix.blockDiag'_evalWord P.ord.injective P.triangular (i₀ :: w₀) (Sum.inl s),
      show (fun i => (T i).blockDiag' (Sum.inl s)) = fun i => C s.1 i from
        funext fun i => P.matched i s, evalWord_aux_eq]
  have hzero : ∀ t : Fin P.z,
      Matrix.trace ((_root_.evalWord T (i₀ :: w₀)).blockDiag' (Sum.inr t)) = 0 := by
    intro t
    rw [Matrix.blockDiag'_evalWord P.ord.injective P.triangular (i₀ :: w₀) (Sum.inr t),
      show (fun i => (T i).blockDiag' (Sum.inr t)) = fun _ : Fin d =>
        (0 : Matrix (Fin 1) (Fin 1) ℂ) from funext fun i => P.unmatched i t]
    simp [_root_.evalWord]
  rw [← P.trace_conjMatrix (Kraus.evalWord B (i₀ :: w₀)), ← evalWord_conjMatrix,
    trace_eq_sum_blockDiag', Fintype.sum_sum_type,
    Finset.sum_congr rfl fun s _ => hslot s, Finset.sum_congr rfl fun t _ => hzero t,
    Finset.sum_const_zero, add_zero]
  exact Finset.sum_attach S fun s => Matrix.trace (Kraus.evalWord (C s) (i₀ :: w₀))

end MultiBlockCompression

end MPSTensor
