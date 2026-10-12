/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.ChannelGroundVectors
import TNLean.Algebra.MatrixProjectionReindex

/-!
The qutrit projections `0 ⊕ diag(1, 0)` and
`0 ⊕ (1/25) [9, 12; 12, 16]` have the common ground vector `e₀`.
For the non-Hermitian observable `|e₁⟩⟨e₀|`, their chronological
root products give respectively zero and `-12/25` in coordinate `e₂`.
Thus the ground-vector identity detects reversal of two events.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open Matrix TNLean.PEPS.AreaLaw
open scoped Kronecker Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace ChannelGroundVectorChronologyTest

private def p : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 0; 0, 1, 0; 0, 0, 0]
private noncomputable def r : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 0; 0, 9/25, 12/25; 0, 12/25, 16/25]

private theorem hp : IsStarProjection p := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [p, IsIdempotentElem, IsSelfAdjoint, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]

private theorem hr : IsStarProjection r := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [r, IsIdempotentElem, IsSelfAdjoint, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]

private def liftQutrit : Matrix (Fin 3) (Fin 3) ℂ ≃+*
    Matrix (Unit → Fin 3) (Unit → Fin 3) ℂ :=
  Matrix.reindexRingEquiv ℂ (Equiv.funUnique Unit (Fin 3)).symm

private noncomputable def effects (b : Bool) : Matrix (Unit → Fin 3) (Unit → Fin 3) ℂ :=
  liftQutrit (if b then r else p)

private theorem effect_projection (b : Bool) : IsStarProjection (effects b) := by
  apply Matrix.isStarProjection_reindex
  cases b
  · exact hp
  · exact hr

private theorem effect_nonneg (b : Bool) : 0 ≤ effects b := (effect_projection b).nonneg

private theorem effect_le_one (b : Bool) : effects b ≤ 1 :=
  sub_nonneg.mp (effect_projection b).one_sub.nonneg

private def ground : (Unit → Fin 3) → ℂ := Pi.single (fun _ => 0) 1

private theorem common_ground (b : Bool) : effects b *ᵥ ground = 0 := by
  rw [ground, Matrix.mulVec_single_one]
  ext f
  change (if b then r else p) (f ()) 0 = 0
  generalize f () = a
  cases b <;> fin_cases a <;> norm_num [p, r]

private theorem complementary_root (b : Bool) :
    CFC.sqrt (1 - effects b) = liftQutrit (1 - if b then r else p) := by
  rw [CFC.sqrt_unique (effect_projection b).one_sub.isIdempotentElem
    (effect_projection b).one_sub.nonneg]
  simp only [map_sub, map_one, effects]

private def raising : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 0; 1, 0, 0; 0, 0, 0]

private def initial : Matrix ((Unit → Fin 3) × Unit) ((Unit → Fin 3) × Unit) ℂ :=
  liftQutrit raising ⊗ₖ (1 : Matrix Unit Unit ℂ)

private theorem ground_product :
    (fun x : (Unit → Fin 3) × Unit => ground x.1) =
      Pi.single ((fun _ => 0), ()) 1 := by
  ext ⟨f, u⟩
  cases u
  simp [ground, Pi.single_apply]

private theorem two_event_entry (i j : Bool) :
    (spectatorRootChannelWord effects [i, j] initial *ᵥ
      (fun x => ground x.1 * (1 : ℂ))) ((fun _ => 2), ()) =
      ((1 - if j then r else p) * (1 - if i then r else p) * raising) 2 0 := by
  rw [spectatorRootChannelWord_mulVec_ground effects effect_nonneg effect_le_one
    common_ground [i, j] (fun _ => 1) initial]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, complementary_root]
  rw [Matrix.mulVec_mulVec, initial, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
    ← map_mul, ← map_mul, ground_product, Matrix.mulVec_single_one]
  simp [liftQutrit, Matrix.reindex_apply, Matrix.kroneckerMap_apply]

theorem chronological_entry :
    (spectatorRootChannelWord effects [false, true] initial *ᵥ
      (fun x => ground x.1 * (1 : ℂ))) ((fun _ => 2), ()) = 0 := by
  rw [two_event_entry]
  norm_num [p, r, raising, Matrix.mul_apply, Fin.sum_univ_three]

theorem reversed_entry :
    (spectatorRootChannelWord effects [true, false] initial *ᵥ
      (fun x => ground x.1 * (1 : ℂ))) ((fun _ => 2), ()) = -(12 / 25 : ℂ) := by
  rw [two_event_entry]
  norm_num [p, r, raising, Matrix.mul_apply, Fin.sum_univ_three]

theorem chronological_ground_vector_ne_reverse :
    spectatorRootChannelWord effects [false, true] initial *ᵥ
        (fun x => ground x.1 * (1 : ℂ)) ≠
      spectatorRootChannelWord effects [true, false] initial *ᵥ
        (fun x => ground x.1 * (1 : ℂ)) := by
  intro h
  have hentry := congrFun h ((fun _ => 2), ())
  rw [chronological_entry, reversed_entry] at hentry
  norm_num at hentry

-- The example's observable is deliberately outside the Hermitian class.
example : ¬initial.IsHermitian := by
  intro h
  have hentry := congrArg (fun M => M ((fun _ => 1), ()) ((fun _ => 0), ())) h.eq
  norm_num [initial, liftQutrit, raising, Matrix.reindex_apply,
    Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply] at hentry

end ChannelGroundVectorChronologyTest
