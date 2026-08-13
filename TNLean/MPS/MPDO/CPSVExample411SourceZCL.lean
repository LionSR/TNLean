/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CPSVExample411Ambient
import TNLean.MPS.MPDO.SourceZCLMarginal

/-!
# Source zero-correlation-length obstruction for CPSV16 Example 4.11

This module verifies the non-ZCL clause printed for CPSV16 Example 4.11 by an
exact finite-marginal obstruction. For the constant-zero retained two-site
word, the normalized entry is $14/41$ on the length-four ring and $5/14$ on
the length-three ring. These values contradict the marginal stability forced
by the source-facing physical-trace predicate `MPOTensor.IsSourceZCL`.

The predicate used here is explicitly distinct from the legacy doubled-index
predicate `MPOTensor.IsZCL`. No conclusion about the legacy predicate is made.
The ambient conclusion is obtained by isometrically embedding the supported
binary entry, not from a statement about entropy or the area law.

## Main results

* `CPSVExample411BinarySupport.reducedBlockState_four_two_zero`: the exact
  length-four supported entry $14/41$.
* `CPSVExample411BinarySupport.reducedBlockState_three_two_zero`: the exact
  length-three supported entry $5/14$.
* `CPSVExample411BinarySupport.M_not_isSourceZCL`: the effective tensor does
  not satisfy the source-facing physical-trace ZCL relation.
* `CPSVExample411Ambient.reducedBlockState_supported_apply`: ambient supported
  marginal entries agree with the effective binary entries.
* `CPSVExample411Ambient.ambientM_not_isSourceZCL`: the ambient tensor does not
  satisfy the source-facing physical-trace ZCL relation.

## Reference

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Example 4.11, lines 907--924
-/

open scoped Matrix BigOperators

noncomputable section

namespace MPOTensor.CPSVExample411BinarySupport

/-- The constant-zero two-site entry of the length-four reduced state is
$14/41$.

This is an exact finite-ring calculation from the neighboring operators in
CPSV16 Example 4.11, lines 907--924. -/
theorem reducedBlockState_four_two_zero :
    reducedBlockState M 4 2 (by omega)
        (fun _ ↦ (0 : Fin 2)) (fun _ ↦ (0 : Fin 2)) = 14 / 41 := by
  rw [reducedBlockState_apply (by omega) (by omega)]
  norm_num [internalTransitionCount]

/-- The constant-zero two-site entry of the length-three reduced state is
$5/14$.

This is an exact finite-ring calculation from the neighboring operators in
CPSV16 Example 4.11, lines 907--924. -/
theorem reducedBlockState_three_two_zero :
    reducedBlockState M 3 2 (by omega)
        (fun _ ↦ (0 : Fin 2)) (fun _ ↦ (0 : Fin 2)) = 5 / 14 := by
  rw [reducedBlockState_apply (by omega) (by omega)]
  norm_num [internalTransitionCount]

/-- The effective binary tensor for CPSV16 Example 4.11 does not satisfy the
source-facing physical-trace zero-correlation-length relation
`MPOTensor.IsSourceZCL`.

This conclusion concerns `IsSourceZCL`, not the separate legacy doubled-index
predicate `MPOTensor.IsZCL`. It follows because source ZCL would identify the
two exact finite marginal entries above, but $14/41 \ne 5/14$. -/
theorem M_not_isSourceZCL : ¬ M.IsSourceZCL := by
  intro hZCL
  have hstable := M.reducedBlockState_succ_succ_eq_succ_of_isSourceZCL hZCL 2
  have hentry := congr_fun (congr_fun hstable (fun _ ↦ (0 : Fin 2)))
    (fun _ ↦ (0 : Fin 2))
  rw [reducedBlockState_four_two_zero, reducedBlockState_three_two_zero] at hentry
  norm_num at hentry

end MPOTensor.CPSVExample411BinarySupport

namespace MPOTensor.CPSVExample411Ambient

/-- Every supported ambient reduced-state entry equals the corresponding
entry of the effective binary reduced state. This is the entrywise form of
isometric marginal transport along the inclusion $|k\rangle \mapsto |k,k\rangle$. -/
theorem reducedBlockState_supported_apply (N L : ℕ) (hL : L ≤ N)
    (x y : Fin L → Fin 2) :
    reducedBlockState ambientM N L hL (embedConfig x) (embedConfig y) =
      reducedBlockState CPSVExample411BinarySupport.M N L hL x y := by
  rw [ambientM, reducedBlockState_changePhysicalBasis_of_isometry inclusion
    inclusion_isometry, singleKrausMap_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    sitewisePhysicalMatrix_inclusion_embedConfig, ite_mul, one_mul, zero_mul,
    Fintype.sum_ite_eq]
  have hstar (q : Fin L → Fin 2) :
      star (if y = q then (1 : ℂ) else 0) = if y = q then 1 else 0 := by
    split <;> simp
  simp_rw [hstar]
  simp

/-- The embedded constant-zero two-site entry of the length-four ambient
reduced state is $14/41$. -/
theorem reducedBlockState_four_two_zero :
    reducedBlockState ambientM 4 2 (by omega)
        (embedConfig (fun _ ↦ (0 : Fin 2)))
        (embedConfig (fun _ ↦ (0 : Fin 2))) = 14 / 41 := by
  rw [reducedBlockState_supported_apply,
    CPSVExample411BinarySupport.reducedBlockState_four_two_zero]

/-- The embedded constant-zero two-site entry of the length-three ambient
reduced state is $5/14$. -/
theorem reducedBlockState_three_two_zero :
    reducedBlockState ambientM 3 2 (by omega)
        (embedConfig (fun _ ↦ (0 : Fin 2)))
        (embedConfig (fun _ ↦ (0 : Fin 2))) = 5 / 14 := by
  rw [reducedBlockState_supported_apply,
    CPSVExample411BinarySupport.reducedBlockState_three_two_zero]

/-- The ambient two-qubit-site tensor for CPSV16 Example 4.11 does not satisfy
the source-facing physical-trace zero-correlation-length relation
`MPOTensor.IsSourceZCL`.

This conclusion concerns `IsSourceZCL`, not the separate legacy doubled-index
predicate `MPOTensor.IsZCL`. It is witnessed by the two embedded supported
finite-marginal entries, without using entropy or area-law failure. -/
theorem ambientM_not_isSourceZCL : ¬ ambientM.IsSourceZCL := by
  intro hZCL
  have hstable := ambientM.reducedBlockState_succ_succ_eq_succ_of_isSourceZCL hZCL 2
  have hentry := congr_fun
    (congr_fun hstable (embedConfig (fun _ ↦ (0 : Fin 2))))
    (embedConfig (fun _ ↦ (0 : Fin 2)))
  rw [reducedBlockState_four_two_zero, reducedBlockState_three_two_zero] at hentry
  norm_num at hentry

end MPOTensor.CPSVExample411Ambient
