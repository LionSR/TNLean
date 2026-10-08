/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.RectangularPreparation

/-!
# Rectangular preparation regression

A singular-reference ring with bond dimensions `1,2,1` exercises the actual rectangular
site transfers, product padding, cyclic normalization and input-corner reset convention.
-/

open Matrix MPSTensor VaryingBondChain MPSPreparation
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace RectangularPreparationRegression

/-- A genuinely varying ring with dimensions `1,2,1`, including a one-dimensional cut. -/
abbrev ring : VaryingBondChain 2 2 3 where
  bondDim := ![1, 2, 1]
  bondDim_le := by decide
  tensor _ s a b := if a.val = 0 ∧ b.val = s.val then 1 else 0

abbrev density (i : Fin 3) : Matrix (Fin (ring.bondDim i)) (Fin (ring.bondDim i)) ℂ :=
  Matrix.of fun a b => if a.val = 0 ∧ b.val = 0 then 1 else 0

example (i : Fin 3) : (density i).PosSemidef := by
  have h : density i = Matrix.vecMulVec (fun a => if a.val = 0 then (1 : ℂ) else 0)
      (star (fun a => if a.val = 0 then (1 : ℂ) else 0)) := by
    ext a b
    simp [density, Matrix.vecMulVec, ite_and]
    split_ifs <;> rfl
  rw [h]
  exact Matrix.posSemidef_vecMulVec_self_star _

example (i : Fin 3) : (density i).trace = 1 := by
  have hpos : 0 < ring.bondDim i := by fin_cases i <;> decide
  let z : Fin (ring.bondDim i) := ⟨0, hpos⟩
  simp only [density, Matrix.trace, Matrix.diag, Matrix.of_apply]
  rw [Finset.sum_eq_single z]
  · simp [z]
  · intro j _ hj
    have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
    simp [hj0]
  · simp

/-- All three actual rectangular site maps are exact reset maps. -/
example (i : Fin 3) :
    Matrix.rectangularKrausMap (ring.tensor i) = Matrix.tracePrepareMap (density i) := by
  fin_cases i <;> first
    | change Matrix.rectangularKrausMap
        (fun (s : Fin 2) => Matrix.of fun (a : Fin 1) (b : Fin 2) =>
          if a.val = 0 ∧ b.val = s.val then (1 : ℂ) else 0) =
          Matrix.tracePrepareMap (Matrix.of fun (a b : Fin 1) =>
            if a.val = 0 ∧ b.val = 0 then (1 : ℂ) else 0)
    | change Matrix.rectangularKrausMap
        (fun (s : Fin 2) => Matrix.of fun (a : Fin 2) (b : Fin 1) =>
          if a.val = 0 ∧ b.val = s.val then (1 : ℂ) else 0) =
          Matrix.tracePrepareMap (Matrix.of fun (a b : Fin 2) =>
            if a.val = 0 ∧ b.val = 0 then (1 : ℂ) else 0)
    | change Matrix.rectangularKrausMap
        (fun (s : Fin 2) => Matrix.of fun (a : Fin 1) (b : Fin 1) =>
          if a.val = 0 ∧ b.val = s.val then (1 : ℂ) else 0) =
          Matrix.tracePrepareMap (Matrix.of fun (a b : Fin 1) =>
            if a.val = 0 ∧ b.val = 0 then (1 : ℂ) else 0)
  all_goals
    apply LinearMap.ext
    intro X
    erw [Matrix.tracePrepareMap_apply]
    dsimp only [Matrix.rectangularKrausMap, LinearMap.coe_mk, AddHom.coe_mk]
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [ring, density, Matrix.vecMulVec, Matrix.of_apply, Pi.smul_apply,
        smul_eq_mul, Matrix.sum_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Matrix.trace, Matrix.diag, Fin.sum_univ_succ]

example : ring.bondDim 0 = 1 ∧ ring.bondDim 1 = 2 ∧ ring.bondDim 2 = 1 := by decide

example : ring.coeff (fun _ => 0) = 1 := by
  rw [← coeff_zeroPad, MPSChainTensor.coeff]
  simp only [MPSChainTensor.eval_succ, MPSChainTensor.eval_zero]
  norm_num [VaryingBondChain.zeroPad, Matrix.zeroPad, Matrix.mul_apply, Matrix.trace,
    Matrix.diag, Fin.sum_univ_succ, finRotate_apply]

example (j : Fin 3) (s : Fin (blockPhysDim 2 1)) :
    Matrix.zeroPad 2
      (rectangularBlockTensor ring (by simp : ∑ _ : Fin 3, 1 = 3) j s) =
      chainBlockTensor (zeroPad ring) (by simp : ∑ _ : Fin 3, 1 = 3) j s :=
  zeroPad_rectangularBlockTensor (ℓ := fun _ : Fin 3 => 1) ring (by simp) j (by decide) s

/-- Padding the map with a one-dimensional input kills the unused input coordinate. -/
example : Kraus.transferMap (zeroPad ring 1) (Matrix.single 1 1 1) = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [Kraus.transferMap_apply, VaryingBondChain.zeroPad, Matrix.zeroPad,
      Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single_apply,
      Fin.sum_univ_succ, finRotate_apply]

def ρ : Matrix (Fin 2) (Fin 2) ℂ := Matrix.single 0 0 1

example : cornerReferenceMap ρ 1 (Matrix.single 1 1 1) = 0 := by
  simp [cornerReferenceMap_apply, Matrix.trace_mul_single, cornerProjection, ρ]

/-- The full reset would incorrectly retain that unused input coordinate. -/
example : Matrix.tracePrepareMap (α := Fin 2) ρ (Matrix.single 1 1 1) = ρ := by simp

example : cornerReferenceMap ρ 1 ≠ Matrix.tracePrepareMap (α := Fin 2) ρ := by
  intro h
  have he := congrArg (fun T => T (Matrix.single 1 1 1) 0 0) h
  norm_num [cornerReferenceMap_apply, Matrix.trace_mul_single, cornerProjection, ρ] at he

example : transferMatrix (cornerReferenceMap ρ 1) * transferMatrix (cornerReferenceMap ρ 2) *
    transferMatrix (cornerReferenceMap ρ 1) = transferMatrix (cornerReferenceMap ρ 1) := by
  have hs : cornerProjection 2 1 * ρ = ρ := by
    ext a b
    simp only [cornerProjection, Matrix.diagonal_mul, ρ]
    fin_cases a <;> fin_cases b <;> norm_num [Matrix.single_apply]
  have ht : ρ.trace = 1 := by simp [ρ]
  rw [transferMatrix_cornerReferenceMap_mul ρ ρ 1 2 hs ht,
    transferMatrix_cornerReferenceMap_mul ρ ρ 2 1 (by simp) ht]

end RectangularPreparationRegression
