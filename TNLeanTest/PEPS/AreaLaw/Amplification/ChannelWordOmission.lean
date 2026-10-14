/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.ChannelWordOmission
import TNLean.Algebra.MatrixProjectionReindex

/-!
Boundary cases and exact chronology regressions for physical omitted-event errors.
The concrete two-event example distinguishes the retained prefix in the theorem
from the full prefix, even at the level of whether the one-event norm is zero.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open QuantumCircuit Matrix MeasureTheory TNLean.PEPS.AreaLaw
open scoped BigOperators NNReal Kronecker Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace ChannelWordOmissionTest

variable {q : ℕ} {ι κ Aux : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype Aux] [DecidableEq Aux]

-- Retention of every event makes the actual norm zero, without effect hypotheses.
theorem allRetained
    (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ) (w : List κ)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    channelWordOmissionDefect k (fun _ => True) w B = 0 := by
  simp [channelWordOmissionDefect]

-- Omitting every event compares the full composition with the original input.
theorem noneRetained
    (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ) (w : List κ)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    channelWordOmissionDefect k (fun _ => False) w B =
      ‖spectatorRootChannelWord k w B - B‖ := by
  simp [channelWordOmissionDefect]

theorem emptyWord
    (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (P : κ → Prop) [DecidablePred P]
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    channelWordOmissionDefect k P [] B = 0 := by
  simp [channelWordOmissionDefect]

-- An empty alphabet has no nonempty words, for any predicate.
theorem emptyAlphabet [IsEmpty κ]
    (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (P : κ → Prop) [DecidablePred P] (w : List κ)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    channelWordOmissionDefect k P w B = 0 := by
  cases w with
  | nil => exact emptyWord k P B
  | cons i w => exact isEmptyElim i

-- The zero-dimensional spectator is handled by actual matrix equality.
theorem emptySpectator
    (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (P : κ → Prop) [DecidablePred P] (w : List κ)
    (B : Matrix ((ι → Fin q) × Empty) ((ι → Fin q) × Empty) ℂ) :
    channelWordOmissionDefect k P w B = 0 := by
  unfold channelWordOmissionDefect
  rw [Subsingleton.elim (spectatorRootChannelWord k w B)
    (spectatorRootChannelWord k (w.filter (fun i => decide (P i))) B)]
  simp

-- The error at time zero is exactly zero under the actual atomic word measure.
theorem zeroTime [Fintype κ]
    (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (P : κ → Prop) [DecidablePred P]
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    (∫ w : PoissonWord.Word κ,
        channelWordOmissionDefect k P (List.ofFn w.2) B ∂PoissonWord.measure κ 0) = 0 := by
  simp [channelWordOmissionDefect, PoissonWord.nil]

theorem emptyAlphabetExpectation [Fintype κ] [IsEmpty κ]
    (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (P : κ → Prop) [DecidablePred P]
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) (T : ℝ≥0) :
    (∫ w : PoissonWord.Word κ,
        channelWordOmissionDefect k P (List.ofFn w.2) B ∂PoissonWord.measure κ T) = 0 := by
  simp only [emptyAlphabet, integral_zero]

-- A final omitted event is evaluated on the retained first event, in this order.
theorem retainedThenOmitted
    (k : Bool → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    channelWordOmissionDefect k (fun b => b = false) [false, true] B =
      ‖spectatorRootChannel (k true) (spectatorRootChannel (k false) B) -
        spectatorRootChannel (k false) B‖ := rfl

-- Repeated omitted and retained labels keep their positions and multiplicities.
theorem repeatedLabels
    (k : Bool → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    channelWordOmissionDefect k (fun b => b = false) [true, false, true, false] B =
      ‖spectatorRootChannel (k false)
          (spectatorRootChannel (k true)
            (spectatorRootChannel (k false) (spectatorRootChannel (k true) B))) -
        spectatorRootChannel (k false) (spectatorRootChannel (k false) B)‖ := rfl

private def repeatedWord : PoissonWord.Word Bool := ⟨4, ![true, false, true, false]⟩

-- The actual Poisson prefix summand counts the same omitted label twice, with
-- different retained prefixes. In particular it cannot be a sum over a set of labels.
theorem repeatedPrefixSum
    (k : Bool → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    (∑ j : Fin repeatedWord.1, if repeatedWord.2 j = false then 0 else
      ‖spectatorRootChannel (k (repeatedWord.2 j))
          (spectatorRootChannelWord k
            ((List.ofFn (PoissonWord.take repeatedWord j).2).filter
              (fun i => decide (i = false))) B) -
        spectatorRootChannelWord k
          ((List.ofFn (PoissonWord.take repeatedWord j).2).filter
            (fun i => decide (i = false))) B‖) =
      ‖spectatorRootChannel (k true) B - B‖ +
        ‖spectatorRootChannel (k true) (spectatorRootChannel (k false) B) -
          spectatorRootChannel (k false) B‖ := by
  simp only [PoissonWord.ofFn_take]
  change (∑ j : Fin 4, _) = _
  simp only [Fin.sum_univ_succ]
  change ‖spectatorRootChannel (k true) B - B‖ +
    (0 + (‖spectatorRootChannel (k true) (spectatorRootChannel (k false) B) -
      spectatorRootChannel (k false) B‖ + (0 + 0))) = _
  abel

private def p : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]
private noncomputable def r : Matrix (Fin 2) (Fin 2) ℂ := !![9/25, 12/25; 12/25, 16/25]

private theorem hp : IsStarProjection p := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [p, IsIdempotentElem, IsSelfAdjoint, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]

private theorem hr : IsStarProjection r := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [r, IsIdempotentElem, IsSelfAdjoint, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]

private def liftQubit : Matrix (Fin 2) (Fin 2) ℂ ≃+*
    Matrix (Unit → Fin 2) (Unit → Fin 2) ℂ :=
  Matrix.reindexRingEquiv ℂ (Equiv.funUnique Unit (Fin 2)).symm

private theorem projectionChannel (P : Matrix (Fin 2) (Fin 2) ℂ) (hP : IsStarProjection P)
    (B : Matrix (Fin 2) (Fin 2) ℂ) :
    spectatorRootChannel (liftQubit P) (liftQubit B ⊗ₖ (1 : Matrix Unit Unit ℂ)) =
      liftQubit (rootChannel (1 - P) P B) ⊗ₖ (1 : Matrix Unit Unit ℂ) := by
  have h := Matrix.isStarProjection_reindex (Equiv.funUnique Unit (Fin 2)).symm P hP
  change IsStarProjection (liftQubit P) at h
  rw [spectatorRootChannel, CFC.sqrt_unique h.isIdempotentElem h.nonneg,
    CFC.sqrt_unique h.one_sub.isIdempotentElem h.one_sub.nonneg]
  simp only [rootChannel, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
    ← Matrix.add_kronecker, map_add, map_mul, map_sub, map_one]

private noncomputable def effects (b : Bool) : Matrix (Unit → Fin 2) (Unit → Fin 2) ℂ :=
  liftQubit (if b then r else p)

-- Both explicit effects meet the positivity and contraction assumptions.
theorem effectsBounds (b : Bool) : 0 ≤ effects b ∧ effects b ≤ 1 := by
  have hP : IsStarProjection (if b then r else p) := by
    cases b
    · exact hp
    · exact hr
  have h := Matrix.isStarProjection_reindex (Equiv.funUnique Unit (Fin 2)).symm _ hP
  exact ⟨h.nonneg, sub_nonneg.mp h.one_sub.nonneg⟩

private def initial : Matrix ((Unit → Fin 2) × Unit) ((Unit → Fin 2) × Unit) ℂ :=
  liftQubit p ⊗ₖ (1 : Matrix Unit Unit ℂ)

private theorem p_fixes_initial : spectatorRootChannel (effects false) initial = initial := by
  change spectatorRootChannel (liftQubit p) (liftQubit p ⊗ₖ (1 : Matrix Unit Unit ℂ)) = _
  rw [projectionChannel p hp]
  have h : rootChannel (1 - p) p p = p := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [rootChannel, p, Matrix.mul_apply, Fin.sum_univ_two]
  rw [h]
  rfl

-- The word [Q,P] has two omitted events. At its second event, the retained
-- prefix is still empty and P fixes the original observable exactly.
theorem retainedPrefixErrorZero :
    ‖spectatorRootChannel (effects false)
        (spectatorRootChannelWord effects
          ([true].filter (fun _ => decide False)) initial) -
      spectatorRootChannelWord effects
        ([true].filter (fun _ => decide False)) initial‖ = 0 := by
  change ‖spectatorRootChannel (effects false) initial - initial‖ = 0
  rw [p_fixes_initial, sub_self, norm_zero]

-- The same event evaluated on the full Q-prefix has a nonzero error entry.
theorem fullPrefixErrorEntry :
    (spectatorRootChannel (effects false)
        (spectatorRootChannelWord effects [true] initial) -
      spectatorRootChannelWord effects [true] initial)
        ((fun _ => 0), ()) ((fun _ => 1), ()) = (84 / 625 : ℂ) := by
  change (spectatorRootChannel (liftQubit p)
    (spectatorRootChannel (liftQubit r) (liftQubit p ⊗ₖ (1 : Matrix Unit Unit ℂ))) -
    spectatorRootChannel (liftQubit r) (liftQubit p ⊗ₖ (1 : Matrix Unit Unit ℂ))) _ _ = _
  simp only [projectionChannel r hr, projectionChannel p hp]
  norm_num [liftQubit, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
    rootChannel, p, r, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

-- In particular the actual operator-norm costs differ, not only matrix entries.
theorem fullPrefixErrorPositive :
    0 < ‖spectatorRootChannel (effects false)
        (spectatorRootChannelWord effects [true] initial) -
      spectatorRootChannelWord effects [true] initial‖ := by
  apply norm_pos_iff.mpr
  intro h
  have he := fullPrefixErrorEntry
  rw [h] at he
  norm_num at he

-- Chronology also changes the omitted-word defect's underlying actual operator.
theorem omissionDifferenceChronology :
    spectatorRootChannelWord effects [false, true] initial - initial ≠
      spectatorRootChannelWord effects [true, false] initial - initial := by
  intro h
  have he := congrArg (fun M => M ((fun _ => 0), ()) ((fun _ => 1), ())) h
  change (spectatorRootChannel (liftQubit r)
      (spectatorRootChannel (liftQubit p) (liftQubit p ⊗ₖ (1 : Matrix Unit Unit ℂ))) -
        liftQubit p ⊗ₖ (1 : Matrix Unit Unit ℂ)) _ _ =
    (spectatorRootChannel (liftQubit p)
      (spectatorRootChannel (liftQubit r) (liftQubit p ⊗ₖ (1 : Matrix Unit Unit ℂ))) -
        liftQubit p ⊗ₖ (1 : Matrix Unit Unit ℂ)) _ _ at he
  simp only [projectionChannel p hp, projectionChannel r hr] at he
  norm_num [liftQubit, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
    rootChannel, p, r, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] at he

end ChannelWordOmissionTest
