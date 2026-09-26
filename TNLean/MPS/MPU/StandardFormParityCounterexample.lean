/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.SimpleScaling
import TNLean.MPS.MPDO.StackedLayers
import TNLean.MPS.MPU.Simple

/-!
# A parity obstruction for two-site standard forms

The bond-one identity tensor and its negative are both simple matrix product
unitaries. Their two-site blocks agree, but their periodic operators differ at
odd lengths. This is the formal parity witness for the unblocked all-length
reading of the converse in arXiv:1703.09188, Theorem `FundamentalMPU`, lines
619--648. The explicit source factors and local standard-form gauges are
calculated separately in `docs/paper-gaps/mpu_standard_form_parity_gap.tex`;
the theorem below does not assert those local relations from block equality
alone.
-/

open scoped Matrix

namespace MPOTensor

private noncomputable def parityIdentityTensor : MPOTensor 2 1 := idTensor 2

private noncomputable def parityNegativeIdentityTensor : MPOTensor 2 1 :=
  (-1 : ℂ) • parityIdentityTensor

private theorem parity_block_two_eq :
    blockTensor parityNegativeIdentityTensor 2 =
      blockTensor parityIdentityTensor 2 := by
  rw [parityNegativeIdentityTensor, blockTensor_smul]
  norm_num

private theorem parity_mpo_identity_three : mpo parityIdentityTensor 3 = 1 :=
  mpo_idTensor 2 3

private theorem parity_mpo_negative_three : mpo parityNegativeIdentityTensor 3 = -1 := by
  rw [parityNegativeIdentityTensor, mpo_smul, parity_mpo_identity_three]
  norm_num

private theorem parity_mpo_three_ne :
    mpo parityNegativeIdentityTensor 3 ≠ mpo parityIdentityTensor 3 := by
  rw [parity_mpo_negative_three, parity_mpo_identity_three]
  intro h
  have h00 := congrArg
    (fun M : Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ =>
      M (fun _ => 0) (fun _ => 0)) h
  norm_num at h00

private theorem parity_identity_simple : IsMPUSimple parityIdentityTensor := by
  have hW (i j : Fin 2) :
      doubleLayerTensor parityIdentityTensor i j =
        (if i = j then 1 else 0) := by
    ext a b
    fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
      simp [parityIdentityTensor, doubleLayerTensor_apply, idTensor,
        Matrix.kroneckerMap_apply, Matrix.submatrix_apply]
  have houter :
      Matrix.vecMulVec (fun _ : Fin 1 => (1 : ℂ)) (fun _ : Fin 1 => (1 : ℂ)) =
        (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext a b
    fin_cases a
    fin_cases b
    simp [Matrix.vecMulVec]
  refine ⟨fun _ => 1, fun _ => 1, ?_, ?_⟩
  · intro i j
    rw [hW]
    by_cases hij : i = j <;> simp [hij, Matrix.mulVec, dotProduct]
  · intro i j k l
    rw [hW, hW, houter]
    simp

private theorem parity_double_negative_eq_identity :
    doubleLayerTensor parityNegativeIdentityTensor =
      doubleLayerTensor parityIdentityTensor := by
  funext i j
  ext a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [parityNegativeIdentityTensor, parityIdentityTensor,
      doubleLayerTensor_apply, idTensor,
      Matrix.kroneckerMap_apply, Matrix.submatrix_apply]

private theorem parity_negative_simple : IsMPUSimple parityNegativeIdentityTensor := by
  obtain ⟨a, b, h₁, h₂⟩ := parity_identity_simple
  refine ⟨a, b, ?_, ?_⟩
  · simpa only [parity_double_negative_eq_identity] using h₁
  · simpa only [parity_double_negative_eq_identity] using h₂

/-- Two simple MPUs of physical dimension two have identical two-site blocks
but different periodic operators at length three.

This is a parity witness for the unblocked all-length converse printed in
arXiv:1703.09188, Theorem `FundamentalMPU`, lines 624--648. Definition `SF`
at lines 619--622 instead defines the standard form of the two-site block.
The local source-factor relation for this example is calculated in
`docs/paper-gaps/mpu_standard_form_parity_gap.tex`; block equality alone is
not claimed to imply that relation. -/
theorem exists_simple_blockTwo_eq_mpo_three_ne :
    ∃ (A B : MPOTensor 2 1), IsMPUSimple A ∧ IsMPUSimple B ∧
      blockTensor A 2 = blockTensor B 2 ∧ mpo A 3 ≠ mpo B 3 := by
  refine ⟨parityIdentityTensor, parityNegativeIdentityTensor,
    parity_identity_simple, parity_negative_simple, parity_block_two_eq.symm, ?_⟩
  exact Ne.symm parity_mpo_three_ne

end MPOTensor
