/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.ChannelWordObservables
import TNLean.Algebra.MatrixProjectionReindex

/-!
An exact noncommuting chronology regression. The two qubit projections are
P = diag(1, 0) and Q = (1/25) [9, 12; 12, 16]. Acting on P in the order P, Q
gives off-diagonal entry -84/625; reversing the events gives zero. The matrices
are transported to the actual one-site physical space with a one-dimensional
spectator, and all roots are evaluated by their projection property.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open Matrix TNLean.PEPS.AreaLaw
open scoped Kronecker Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace ChannelWordChronologyTest

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

-- Both concrete events satisfy the exact positivity/contraction hypotheses.
example (b : Bool) : 0 ≤ effects b ∧ effects b ≤ 1 := by
  have hP : IsStarProjection (if b then r else p) := by
    cases b
    · exact hp
    · exact hr
  have h := Matrix.isStarProjection_reindex (Equiv.funUnique Unit (Fin 2)).symm _ hP
  exact ⟨h.nonneg, sub_nonneg.mp h.one_sub.nonneg⟩

private def initial : Matrix ((Unit → Fin 2) × Unit) ((Unit → Fin 2) × Unit) ℂ :=
  liftQubit p ⊗ₖ (1 : Matrix Unit Unit ℂ)

theorem chronologicalEntry :
    spectatorRootChannelWord effects [false, true] initial
      ((fun _ => 0), ()) ((fun _ => 1), ()) = -(84 / 625 : ℂ) := by
  change spectatorRootChannel (liftQubit r)
    (spectatorRootChannel (liftQubit p) (liftQubit p ⊗ₖ (1 : Matrix Unit Unit ℂ))) _ _ = _
  rw [projectionChannel p hp, projectionChannel r hr]
  norm_num [liftQubit, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
    rootChannel, p, r, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem reversedEntry :
    spectatorRootChannelWord effects [true, false] initial
      ((fun _ => 0), ()) ((fun _ => 1), ()) = 0 := by
  change spectatorRootChannel (liftQubit p)
    (spectatorRootChannel (liftQubit r) (liftQubit p ⊗ₖ (1 : Matrix Unit Unit ℂ))) _ _ = _
  rw [projectionChannel r hr, projectionChannel p hp]
  norm_num [liftQubit, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
    rootChannel, p, r, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem chronologicalWord_ne_reverse :
    spectatorRootChannelWord effects [false, true] initial ≠
      spectatorRootChannelWord effects [true, false] initial := by
  intro h
  have hentry := congrArg (fun B => B ((fun _ => 0), ()) ((fun _ => 1), ())) h
  rw [chronologicalEntry, reversedEntry] at hentry
  norm_num at hentry

end ChannelWordChronologyTest
