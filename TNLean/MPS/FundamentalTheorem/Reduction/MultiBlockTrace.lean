/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.FundamentalTheorem.Reduction.MultiBlock

/-!
# The word-trace converse of multi-block asymmetric compression

This file records the converse direction of clauses (i)–(iii) of the multi-block asymmetric
compression theorem (P5 note, `Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`,
§7.5, Theorem 7.7): any multi-block compression datum already reproduces the word-trace hypothesis
`htr` of `MPSTensor.exists_multiBlockCompression_of_isNormal`. Combined with the theorem itself,
this shows that the word-trace hypothesis is not merely sufficient for a multi-block compression
to exist, but is exactly the trace identity that every multi-block compression datum satisfies.

## Main results

* `MPSTensor.MultiBlockCompression.trace_evalWord_eq_sum`: the trace of `B`'s word evaluation is
  the sum of the traces of the corresponding word evaluations of the target blocks.
* `MPSTensor.MultiBlockCompression.mpv_eq_sum`: the same identity in the matrix-product-vector
  form, for every positive system size.
-/

open scoped Matrix

namespace MPSTensor

/-- The trace of a matrix indexed by a `Σ`-type is the sum of the traces of its diagonal
blocks. -/
theorem trace_eq_sum_blockDiag' {o : Type*} [Fintype o] {n : o → ℕ}
    (X : Matrix (Σ k, Fin (n k)) (Σ k, Fin (n k)) ℂ) :
    Matrix.trace X = ∑ k, Matrix.trace (X.blockDiag' k) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.blockDiag'_apply]
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]

variable {d DB : ℕ} {ι : Type*} [DecidableEq ι] {D : ι → ℕ} {B : MPSTensor d DB}
  {S : Finset ι} {C : ∀ s, MPSTensor d (D s)}

namespace MultiBlockCompression

variable (P : MultiBlockCompression B S C)

/-- Conjugation by the gauge equivalence of a multi-block compression preserves the trace. -/
theorem trace_conjMatrix (A : Matrix (Fin DB) (Fin DB) ℂ) :
    Matrix.trace (conjMatrix P.gauge A) = Matrix.trace A := by
  rw [conjMatrix_eq_gaugeMatrix_mul, Matrix.trace_mul_cycle, gaugeMatrixInv_mul_gaugeMatrix,
    Matrix.one_mul]

/-- **The word-trace converse of Theorem 7.7(i)–(iii).** Any multi-block compression datum
reproduces the word-trace hypothesis of `exists_multiBlockCompression_of_isNormal`: the trace of
`B^w` is the sum of the traces of the diagonal blocks of the conjugated word, which are the words
of the blocks. -/
theorem trace_evalWord_eq_sum (P : MultiBlockCompression B S C) (w : List (Fin d))
    (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord B w) = ∑ s ∈ S, Matrix.trace (Kraus.evalWord (C s) w) := by
  classical
  have hconj : Matrix.trace (conjMatrix P.gauge (Kraus.evalWord B w)) =
      Matrix.trace (Kraus.evalWord B w) :=
    P.trace_conjMatrix (Kraus.evalWord B w)
  set T : Fin d → Matrix (BlockSpace D S P.z) (BlockSpace D S P.z) ℂ :=
    fun i => conjMatrix P.gauge (B i) with hTdef
  rw [← hconj, ← evalWord_conjMatrix, trace_eq_sum_blockDiag' (_root_.evalWord T w),
    Fintype.sum_sum_type]
  have hleft : ∀ s : {s // s ∈ S},
      Matrix.trace ((_root_.evalWord T w).blockDiag' (Sum.inl s)) =
        Matrix.trace (Kraus.evalWord (C s.1) w) := by
    intro s
    rw [Matrix.blockDiag'_evalWord P.ord.injective P.triangular w (Sum.inl s)]
    have hs : (fun i => (T i).blockDiag' (Sum.inl s)) = fun i => C s.1 i :=
      funext fun i => P.matched i s
    rw [hs, MPSTensor.evalWord_aux_eq]
  have hright : ∀ t : Fin P.z,
      Matrix.trace ((_root_.evalWord T w).blockDiag' (Sum.inr t)) = 0 := by
    intro t
    rw [Matrix.blockDiag'_evalWord P.ord.injective P.triangular w (Sum.inr t)]
    have ht : (fun i => (T i).blockDiag' (Sum.inr t)) =
        fun _ : Fin d => (0 : Matrix (Fin 1) (Fin 1) ℂ) :=
      funext fun i => P.unmatched i t
    rw [ht]
    obtain ⟨i, w', rfl⟩ := List.exists_cons_of_ne_nil hw
    simp [_root_.evalWord]
  rw [Finset.sum_congr rfl fun s _ => hleft s, Finset.sum_congr rfl fun t _ => hright t,
    Finset.sum_const_zero, add_zero]
  exact Finset.sum_attach S fun s => Matrix.trace (Kraus.evalWord (C s) w)

/-- The matrix-product-vector form of `trace_evalWord_eq_sum`: for every positive system size,
the MPV of `B` is the sum of the MPVs of the blocks. -/
theorem mpv_eq_sum (P : MultiBlockCompression B S C) (N : ℕ) (hN : 0 < N) (σ : Fin N → Fin d) :
    mpv B σ = ∑ s ∈ S, mpv (C s) σ := by
  have hword : List.ofFn σ ≠ [] := by
    intro hzero
    have hlength := congrArg List.length hzero
    simp only [List.length_ofFn, List.length_nil] at hlength
    omega
  simpa [mpv, coeff] using P.trace_evalWord_eq_sum (List.ofFn σ) hword

end MultiBlockCompression

end MPSTensor
