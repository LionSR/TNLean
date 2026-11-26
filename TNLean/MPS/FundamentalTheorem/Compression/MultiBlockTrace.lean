/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.FundamentalTheorem.Compression.MultiBlock
import TNLean.MPS.Operator.Product.ActionTensor

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
* `MPSTensor.MultiBlockCompression.trace_evalWord_eq_sum_smul`: the same identity for weighted
  blocks `μ_s • A_s`, with the weights pulled out as `μ_s^{|w|}`.
* `MPSTensor.MultiBlockCompression.mpv_eq_sum`: the same identity in the matrix-product-vector
  form, for every positive system size.
* `MPOTensor.mpo_mul_eq_sum_of_multiBlockCompression`,
  `MPOTensor.mpo_mulVec_mpv_eq_sum_of_multiBlockCompression`: periodic-operator readings of a
  multi-block compression datum.
-/

open MPTensor

open scoped Matrix

section MultiBlockTrace

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
  rw [← hconj, ← evalWord_conjMatrix, trace_eq_sum_blockDiag' (Kraus.evalWord T w),
    Fintype.sum_sum_type]
  have hleft : ∀ s : {s // s ∈ S},
      Matrix.trace ((Kraus.evalWord T w).blockDiag' (Sum.inl s)) =
        Matrix.trace (Kraus.evalWord (C s.1) w) := by
    intro s
    rw [Matrix.blockDiag'_evalWord P.ord.injective P.triangular w (Sum.inl s)]
    have hs : (fun i => (T i).blockDiag' (Sum.inl s)) = fun i => C s.1 i :=
      funext fun i => P.matched i s
    rw [hs]
  have hright : ∀ t : Fin P.z,
      Matrix.trace ((Kraus.evalWord T w).blockDiag' (Sum.inr t)) = 0 := by
    intro t
    rw [Matrix.blockDiag'_evalWord P.ord.injective P.triangular w (Sum.inr t)]
    have ht : (fun i => (T i).blockDiag' (Sum.inr t)) =
        fun _ : Fin d => (0 : Matrix (Fin 1) (Fin 1) ℂ) :=
      funext fun i => P.unmatched i t
    rw [ht]
    obtain ⟨i, w', rfl⟩ := List.exists_cons_of_ne_nil hw
    simp [Kraus.evalWord]
  rw [Finset.sum_congr rfl fun s _ => hleft s, Finset.sum_congr rfl fun t _ => hright t,
    Finset.sum_const_zero, add_zero]
  exact Finset.sum_attach S fun s => Matrix.trace (Kraus.evalWord (C s) w)

/-- **The word-trace converse for weighted blocks.** When the target blocks are rescaled tensors
`μ_s • A_s`, the word trace of `B` is the weighted sum `∑_s μ_s^{|w|} tr(A_s^w)`. -/
theorem trace_evalWord_eq_sum_smul {μ : ι → ℂ} {A : ∀ s, MPSTensor d (D s)}
    (P : MultiBlockCompression B S fun s => μ s • A s) (w : List (Fin d)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord B w) =
      ∑ s ∈ S, μ s ^ w.length * Matrix.trace (Kraus.evalWord (A s) w) := by
  rw [P.trace_evalWord_eq_sum w hw]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [show μ s • A s = fun i => μ s • A s i from rfl, Kraus.evalWord_smul, Matrix.trace_smul,
    smul_eq_mul]

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

end MultiBlockTrace

section CompressionPeriodic

/-!
## Periodic-operator readings of a multi-block compression datum

The word-trace identity of a multi-block compression datum
(`MPSTensor.MultiBlockCompression.trace_evalWord_eq_sum`) has two readings on the periodic
operators of matrix product operators, converse to the existence theorems of
`TNLean/MPS/FundamentalTheorem/Reduction/MPOProduct.lean`: a compression of the stacked product
of two operator tensors onto the doubled-index views of a family of operator tensors gives the
product of the periodic operators as the sum of the periodic operators of the family, and a
compression of an action tensor onto a family of state tensors gives the periodic operator
applied to the periodic vector as the sum of the periodic vectors of the family (P5 note,
Theorem 7.12 and its action-tensor corollary, arXiv:2203.12563, equation `mpoMPSsten`).

### Main results

* `MPOTensor.mpo_mul_eq_sum_of_multiBlockCompression`: the product reading.
* `MPOTensor.mpo_mulVec_mpv_eq_sum_of_multiBlockCompression`: the action reading.
-/

namespace MPOTensor

variable {d : ℕ} {ι : Type*} [DecidableEq ι]

/-- **A compression of a stacked product is a fusion rule of periodic operators.** If the
stacked product of `M` and `N` compresses onto the doubled-index views of the operator tensors
`C s`, then at every positive length the product of the periodic operators of `M` and `N` is the
sum of the periodic operators of the `C s` (P5 note, Theorem 7.12, converse direction). -/
theorem mpo_mul_eq_sum_of_multiBlockCompression {Dα Dβ : ℕ} {Dγ : ι → ℕ}
    {M : MPOTensor d Dα} {N : MPOTensor d Dβ} {S : Finset ι} {C : ∀ s, MPOTensor d (Dγ s)}
    (P : MPSTensor.MultiBlockCompression (mulTensor M N).toMPSTensor S
      fun s => (C s).toMPSTensor) (L : ℕ) (hL : 0 < L) :
    mpo M L * mpo N L = ∑ s ∈ S, mpo (C s) L := by
  rw [← mpo_mulTensor]
  ext σ τ
  have hw : (List.ofFn fun k => finProdFinEquiv (σ k, τ k)) ≠ [] := by
    simp only [ne_eq, List.ofFn_eq_nil_iff]
    omega
  have h := P.trace_evalWord_eq_sum _ hw
  simp only [evalWord_toMPSTensor_pairConfig] at h
  rw [Matrix.sum_apply]
  simpa only [mpo_apply, mpoMatrixEntry] using h

/-- **A compression of an action tensor is an action rule of periodic operators.** If the
action tensor of `T` on `A` compresses onto the state tensors `C s`, then at every positive
length the periodic operator of `T` carries the periodic vector of `A` to the sum of the
periodic vectors of the `C s` (arXiv:2203.12563, equation `mpoMPSsten`, converse
direction). -/
theorem mpo_mulVec_mpv_eq_sum_of_multiBlockCompression {D DA : ℕ} {Dy : ι → ℕ}
    {T : MPOTensor d D} {A : MPSTensor d DA} {S : Finset ι} {C : ∀ s, MPSTensor d (Dy s)}
    (P : MPSTensor.MultiBlockCompression (actTensor T A) S C) (L : ℕ) (hL : 0 < L) :
    mpo T L *ᵥ (fun τ : Fin L → Fin d => MPTensor.mpv A τ) =
      fun σ : Fin L → Fin d => ∑ s ∈ S, MPTensor.mpv (C s) σ := by
  rw [mpo_mulVec_mpv]
  funext σ
  exact P.mpv_eq_sum L hL σ

end MPOTensor

end CompressionPeriodic
