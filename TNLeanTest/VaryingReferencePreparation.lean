/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.VaryingReferencePreparation

/-!
# Singular varying-reference regression

Two distinct rank-one density matrices distinguish the outgoing pair's cyclic reference
from the incorrect unshifted choice. The singleton checks retain trace-one normalization.
-/

namespace VaryingPairRegression
open Matrix MPSTensor MPSPreparation
open scoped BigOperators ComplexOrder MatrixOrder
private def ρ (j : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun i => if i = j then 1 else 0)
private theorem hρ (j : Fin 2) : (ρ j).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  dsimp
  split_ifs <;> positivity
private theorem htr (j : Fin 2) : (ρ j).trace = 1 := by
  simp [ρ, Matrix.trace]
private theorem hsqrt (j : Fin 2) : CFC.sqrt (ρ j) = ρ j := by
  apply (CFC.sqrt_eq_iff _ _ (hρ j).nonneg (hρ j).nonneg).2
  change (ρ j) * (ρ j) = ρ j
  dsimp [ρ]
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp
example : ρ 0 ≠ ρ 1 := by
  intro h
  have he := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℂ => X 0 0) h
  norm_num [ρ] at he
example (j : Fin 2) : (ρ j).det = 0 := by
  fin_cases j <;> norm_num [ρ, Matrix.det_fin_two]
example (j : Fin 2) :
    Matrix.trace (transferMatrix (Kraus.transferMap (fixedPointTensor (ρ j)))) = 1 := by
  simpa only [pow_one] using
    (trace_transferMatrix_transferMap_pow_eq_mpvOverlap (fixedPointTensor (ρ j)) 1).trans
      (mpvOverlap_fixedPointTensor_self (hρ j) (htr j) 1)
private def cfg (j : Fin 2) : Fin (2 * 2) :=
  finProdFinEquiv (j, finRotate 2 j)
example : mpvFamily (fun j : Fin 2 => fixedPointTensor (ρ j)) cfg = 1 ∧
    pairFamilyState (fun j : Fin 2 => fixedPointPair (ρ j))
      (fun j => finProdFinEquiv.symm (cfg j)) = 0 := by
  rw [mpvFamily_fixedPointTensor]
  simp only [pairFamilyState, fixedPointPair, hsqrt]
  norm_num [cfg, ρ, Fin.prod_univ_two]
example (j : Fin 2) :
    ‖pairFamilyVector (fun _ : Fin 1 => fixedPointPair (ρ j))‖ = 1 :=
  norm_pairFamilyVector fun _ => by rw [fixedPointPair_norm_sq (hρ j), htr]
end VaryingPairRegression
