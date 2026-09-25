/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.FundamentalTheorem.Reduction.MultiBlockTrace

/-!
# Example C: a repeated block with a nontrivial extension

**Source.** Project construction for the multi-block asymmetric compression
theorem of this development; it is not a tensor printed in a published source,
and it is not a renormalization fixed point. It shows that the gauge conclusion
of the symmetric fundamental theorem fails once the target carries a repeated
normal block, even though the word traces agree with those of the direct sum.

A machine-checked instance of the multi-block asymmetric compression theorem (P5 note,
`Notes/OpenProblemsTN/strategies/p5_asymmetric_compression_theorem.tex`, Example C, lines
970–983; verified numerically by `checks/p5_examples_verify.py`, section C).

The target `repA` is the scalar normal tensor `A^1 = (1)`, `A^2 = (2)`, repeated twice. The
source tensor `repB` compresses biorthogonally onto both copies and has the same word-trace
family as the repeated target, `A ⊕ A`, but `repB 0` is a nontrivial Jordan block: no invertible
gauge relates `repB` to `A ⊕ A`, so the conclusion of the symmetric fundamental theorem is false
for `repB`, not merely inapplicable.

## Provenance

The example and its numerical check were first recorded in
`Notes/OpenProblemsTN/strategies/p5_asymmetric_compression_theorem.tex`,
Example C (label `ex:p5ft-jordan`); they are verification records, not the
source.

## Main results

* `MPSTensor.repeatedBlock_compression`: the multi-block compression datum of Theorem 7.7 for
  `repB` onto the two copies of `repA`.
* `MPSTensor.repB_trace_evalWord_eq_two_mul`: the word-trace identity for `repB`, specializing
  `MPSTensor.MultiBlockCompression.trace_evalWord_eq_sum`.
* `MPSTensor.repeatedBlock_isReduction`: the biorthogonal compression pair for each copy.
* `MPSTensor.not_gaugeEquiv_directSum_repA`: no invertible gauge conjugates `repB` into the
  direct sum `A ⊕ A`.
-/

open scoped Matrix

namespace MPSTensor

/-- The target slots of Example C: both copies of the repeated block. -/
private abbrev RepS : Finset (Fin 2) := Finset.univ

/-- The bond dimension of each copy: the scalar target is one-dimensional. -/
private abbrev RepD : Fin 2 → ℕ := fun _ => 1

/-- The scalar normal target of Example C: `A^1 = (1)`, `A^2 = (2)` (P5 note, Example C,
`ex:p5ft-jordan`). -/
def repA : MPSTensor 2 1 := ![!![1], !![2]]

/-- The repeated target: two copies of `repA`, one per slot. -/
def repC : (s : Fin 2) → MPSTensor 2 (RepD s) := fun _ => repA

/-- The source tensor of Example C: a nontrivial Jordan-block extension of the repeated target
(P5 note, Example C, `ex:p5ft-jordan`). -/
def repB : MPSTensor 2 2 := ![!![1, 1; 0, 1], !![2, 0; 0, 2]]

/-- The identity block ordering of Example C: slot `0` at position `0`, slot `1` at position
`1`, matching the diagonal blocks of `repB` in order. -/
def repOrd : BlockIndex RepS 0 ≃ Fin 2 where
  toFun
    | Sum.inl ⟨s, _⟩ => s
    | Sum.inr t => t.elim0
  invFun n := Sum.inl ⟨n, Finset.mem_univ n⟩
  left_inv := by decide
  right_inv := by decide

/-- The coordinate change of Example C on the graded block space, agreeing with `repOrd` on
the (unique) coordinate of every block. -/
def repTau : BlockSpace RepD RepS 0 ≃ Fin 2 where
  toFun x := repOrd x.1
  invFun n := ⟨Sum.inl ⟨n, Finset.mem_univ n⟩, 0⟩
  left_inv := by decide
  right_inv := by decide

/-- The identity reindexing of the bond space of `repB` into the block coordinates given by
`repTau`. -/
noncomputable def repGauge : (Fin 2 → ℂ) ≃ₗ[ℂ] (BlockSpace RepD RepS 0 → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ repTau

/-- Conjugating a matrix by `repGauge` reindexes it along `repTau`. -/
theorem conjMatrix_repGauge (A : Matrix (Fin 2) (Fin 2) ℂ) :
    conjMatrix repGauge A = A.submatrix repTau repTau := by
  rw [repGauge, conjMatrix_apply, toMatrix'_conj_funCongrLeft, LinearMap.toMatrix'_toLin']

/-- **The multi-block asymmetric compression datum of Example C.** -/
noncomputable def repeatedBlock_compression : MultiBlockCompression repB RepS repC where
  z := 0
  ord := repOrd
  gauge := repGauge
  triangular i x y hxy := by
    rw [conjMatrix_repGauge, Matrix.submatrix_apply]
    fin_cases i <;> fin_cases x <;> fin_cases y <;>
      first
        | exact absurd hxy (by decide)
        | simp [repTau, repOrd, repB]
  matched i s := by
    ext p q
    rw [Matrix.blockDiag'_apply, conjMatrix_repGauge, Matrix.submatrix_apply]
    fin_cases p; fin_cases q
    obtain ⟨s, hs⟩ := s
    fin_cases i <;> fin_cases s <;> simp [repTau, repOrd, repB, repC, repA]
  unmatched _ t := t.elim0

/-- **The word-trace identity of Example C**, specializing `trace_evalWord_eq_sum`: the trace of
every nonempty word of `repB` is twice the trace of the corresponding word of `repA` (P5 note,
Example C). -/
theorem repB_trace_evalWord_eq_two_mul (w : List (Fin 2)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord repB w) = 2 * Matrix.trace (Kraus.evalWord repA w) := by
  have h := repeatedBlock_compression.trace_evalWord_eq_sum w hw
  simp only [repC, Fin.sum_univ_two] at h
  rwa [← two_mul] at h

/-- **Biorthogonal compression of each copy out of `repB`.** -/
theorem repeatedBlock_isReduction (s : {s // s ∈ RepS}) :
    IsReduction repB (repC s.1) (repeatedBlock_compression.left s)
      (repeatedBlock_compression.right s) :=
  repeatedBlock_compression.isReduction s

/-- **The symmetric conclusion is false.** No invertible gauge conjugates `repB` into the direct
sum `A ⊕ A`: the first diagonal block of that direct sum, coming from `repA 0 = (1)`, is the
identity matrix, but `repB 0` has a nonzero off-diagonal entry (P5 note, Example C,
`ex:p5ft-jordan`). -/
theorem not_gaugeEquiv_directSum_repA :
    ¬ ∃ X : GL (Fin 2) ℂ, ∀ i,
      repB i = X * (Matrix.diagonal fun _ : Fin 2 => repA i 0 0) * X⁻¹ := by
  rintro ⟨X, hX⟩
  have h0 := hX 0
  have hdiag :
      (Matrix.diagonal fun _ : Fin 2 => repA 0 0 0) = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    simp [repA]
  rw [hdiag, Matrix.mul_one, Units.mul_inv] at h0
  have hentry := congrFun (congrFun h0 0) 1
  simp [repB] at hentry

end MPSTensor
