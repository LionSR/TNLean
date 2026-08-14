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

* `MPOTensor.CPSVExample411BinarySupport.reducedBlockState_four_two_zero`: the exact
  length-four supported entry $14/41$.
* `MPOTensor.CPSVExample411BinarySupport.reducedBlockState_three_two_zero`: the exact
  length-three supported entry $5/14$.
* `MPOTensor.CPSVExample411BinarySupport.physTraceTransfer_M_ne_zero`: the effective
  physical-trace transfer is nonzero.
* `MPOTensor.CPSVExample411BinarySupport.M_not_isSourceZCL`: the effective tensor does
  not satisfy the source-facing physical-trace ZCL relation.
* `MPOTensor.CPSVExample411BinarySupport.physTraceTransfer_M_not_idempotent`: the
  effective tensor fails the literal Definition 4.2 diagram.
* `MPOTensor.CPSVExample411Ambient.reducedBlockState_supported_apply`: ambient supported
  marginal entries agree with the effective binary entries.
* `MPOTensor.CPSVExample411Ambient.physTraceTransfer_ambientM_ne_zero`: the ambient
  physical-trace transfer is nonzero.
* `MPOTensor.CPSVExample411Ambient.ambientM_not_isSourceZCL`: the ambient tensor does not
  satisfy the source-facing physical-trace ZCL relation.
* `MPOTensor.CPSVExample411Ambient.physTraceTransfer_ambientM_not_idempotent`: the
  ambient tensor fails the literal Definition 4.2 diagram.

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

/-- The physical-trace transfer of the effective binary tensor is nonzero.

The tensor is extracted from the neighboring operators printed in CPSV16
Example 4.11, lines 907--924. The project-derived exact partition function gives
its one-site periodic MPO trace as $2$, so the cyclic trace identity rules out a
zero physical-trace transfer. -/
theorem physTraceTransfer_M_ne_zero : physTraceTransfer M ≠ 0 := by
  intro hzero
  have htrace := trace_mpo_eq_trace_verticalLoop_pow M 1
  rw [verticalLoop_eq_physTraceTransfer, hzero] at htrace
  have hclosed : Matrix.trace (mpo M 1) = 2 := by
    rw [mpo_M_eq_diagonal, Matrix.trace_diagonal]
    change partitionFunction 1 = 2
    rw [partitionFunction_closed_form]
    norm_num
  rw [hclosed] at htrace
  norm_num at htrace

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

/-- The effective binary tensor fails the literal physical-trace idempotence
diagram in arXiv:1606.00608, Definition 4.2, lines 735--739.

This is the fixed-tensor identity $\mathcal T_M^2=\mathcal T_M$, not the legacy
idempotence condition on the doubled-index transfer map. -/
theorem physTraceTransfer_M_not_idempotent :
    ¬ physTraceTransfer M * physTraceTransfer M = physTraceTransfer M := by
  intro hidem
  exact M_not_isSourceZCL
    (isSourceZCL_of_physTraceTransfer_sq M physTraceTransfer_M_ne_zero hidem)

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

/-- The physical-trace transfer of the ambient two-qubit-site tensor is nonzero.

The tensor embeds the neighboring operators printed in CPSV16 Example 4.11,
lines 907--924. The project-derived exact ambient normalization gives its
one-site periodic MPO trace as $2$, so the cyclic trace identity rules out a
zero physical-trace transfer. -/
theorem physTraceTransfer_ambientM_ne_zero : physTraceTransfer ambientM ≠ 0 := by
  intro hzero
  have htrace := trace_mpo_eq_trace_verticalLoop_pow ambientM 1
  rw [verticalLoop_eq_physTraceTransfer, hzero] at htrace
  have hclosed : Matrix.trace (mpo ambientM 1) = 2 := by
    rw [trace_mpo_ambientM_closed_form]
    norm_num
  rw [hclosed] at htrace
  norm_num at htrace

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

/-- The ambient two-qubit-site tensor fails the literal physical-trace
idempotence diagram in arXiv:1606.00608, Definition 4.2, lines 735--739.

This is the fixed-tensor identity
$\mathcal T_{\widetilde M}^2=\mathcal T_{\widetilde M}$, not the legacy
idempotence condition on the doubled-index transfer map. -/
theorem physTraceTransfer_ambientM_not_idempotent :
    ¬ physTraceTransfer ambientM * physTraceTransfer ambientM =
      physTraceTransfer ambientM := by
  intro hidem
  exact ambientM_not_isSourceZCL
    (isSourceZCL_of_physTraceTransfer_sq ambientM physTraceTransfer_ambientM_ne_zero hidem)

end MPOTensor.CPSVExample411Ambient
