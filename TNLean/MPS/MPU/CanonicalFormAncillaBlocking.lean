/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.MPUCanonicalForm
import TNLean.MPS.MPU.PhysicalAncilla
import TNLean.MPS.MPU.CanonicalForm
import TNLean.MPS.CanonicalForm.CPSVBlocking
import TNLean.MPS.CanonicalForm.CPSVPhysicalReindex

/-!
# Canonical form after attaching an ancilla and blocking

The tensors compared in the definition of equivalence are obtained from an MPU
tensor in canonical form by attaching an identity ancilla and then blocking.
This file shows that these tensors are again in canonical form.

The argument uses Proposition `prop:normal-tensor` of arXiv:1703.09188
(lines 344--354): the normalized tensor \(d^{-1/2}\mathcal U\) of an MPU in
canonical form is normal. Attaching an identity ancilla and blocking preserve
normality of the normalized tensor, and a normal tensor is in canonical form
with one block filling the bond space.

## Main statements

* `MPSTensor.IsNormalTensor.isMPUCanonicalForm`: a normal tensor is in MPU
  canonical form with a single block.
* `MPOTensor.IsMPU.isMPUCanonicalForm_tensorPhysicalId`: attaching a
  positive-dimensional identity ancilla preserves canonical form of an MPU
  tensor.
* `MPOTensor.IsMPU.isMPUCanonicalForm_blockTensor`: blocking a positive number
  of sites preserves canonical form of an MPU tensor.
* `MPOTensor.IsMPU.isMPUCanonicalForm_blockTensor_tensorPhysicalId`: attaching
  a positive-dimensional identity ancilla and then blocking a positive number of
  sites preserves canonical form of an MPU tensor.

## References

* arXiv:1703.09188, canonical form, lines 259--267; Proposition
  `prop:normal-tensor`, lines 344--354; Definitions
  `def:strictly-equivalent-tensors` and `def:equivalent-tensors`,
  lines 706--724.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- A normal tensor is in MPU canonical form, with one block of weight one
filling the bond space.

Source: arXiv:1703.09188, canonical form, lines 259--267. -/
theorem IsNormalTensor.isMPUCanonicalForm {A : MPSTensor d D}
    (hA : IsNormalTensor A) : IsMPUCanonicalForm A := by
  have : NeZero D := ⟨hA.bondDim_ne_zero⟩
  classical
  let V : Matrix (Fin (∑ _ : Fin 1, D)) (Fin D) ℂ :=
    MPSTensor.blockInclusion (fun _ : Fin 1 => D) 0
  have hV : (Vᴴ * V : Matrix (Fin D) (Fin D) ℂ) = 1 :=
    MPSTensor.blockInclusion_conjTranspose_mul_self _ _
  refine ⟨{
    r := 1
    dim := fun _ => D
    dim_pos := fun _ => NeZero.pos D
    weights := fun _ => 1
    weights_ne_zero := fun _ => one_ne_zero
    blocks := fun _ => A
    ambient_coisometry := V
    coisometric := ?_
    reconstruct := ?_
    blocks_canonical := fun _ => ⟨hA.no_invariant_proj, hA.spectral_radius_one⟩
    total_dim_eq := by simp }⟩
  · have hcard : Fintype.card (Fin D) = Fintype.card (Fin (∑ _ : Fin 1, D)) := by simp
    exact (Matrix.mul_eq_one_comm_of_card_eq _ _ ℂ
      (A := (Vᴴ : Matrix (Fin D) (Fin (∑ _ : Fin 1, D)) ℂ))
      (B := V) hcard).mp hV
  · intro i
    have hmul := MPSTensor.toTensorFromBlocks_mul_blockInclusion
      (fun _ : Fin 1 => (1 : ℂ)) (fun _ : Fin 1 => A) 0 i
    have hmul' : MPSTensor.toTensorFromBlocks (fun _ : Fin 1 => (1 : ℂ))
        (fun _ : Fin 1 => A) i * V = V * A i := by
      simpa only [one_smul] using hmul
    calc
      A i = (Vᴴ * V) * A i := by rw [hV, Matrix.one_mul]
      _ = Vᴴ * (MPSTensor.toTensorFromBlocks
            (fun _ : Fin 1 => (1 : ℂ)) (fun _ : Fin 1 => A) i * V) := by
              rw [hmul', Matrix.mul_assoc]
      _ = (Vᴴ * MPSTensor.toTensorFromBlocks (fun _ : Fin 1 => (1 : ℂ))
            (fun _ : Fin 1 => A) i) * V :=
              (Matrix.mul_assoc Vᴴ _ V).symm

end MPSTensor

namespace MPOTensor

variable {d D : ℕ}

/-- If the normalized tensor of an MPO tensor is normal, the tensor itself is in
canonical form: its letters are the normalized letters with weight \(d^{1/2}\).

Source: arXiv:1703.09188, canonical form, lines 259--267. -/
theorem isMPUCanonicalForm_of_isNormalTensor_normalizedFlattening [NeZero d]
    {U : MPOTensor d D} (hU : MPSTensor.IsNormalTensor U.normalizedFlattening) :
    MPSTensor.IsMPUCanonicalForm U.toMPSTensor := by
  have hc : (Real.sqrt d : ℂ) ≠ 0 := by
    have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    exact_mod_cast (Real.sqrt_pos.mpr hd).ne'
  have hU' : (fun i => (Real.sqrt d : ℂ) • U.normalizedFlattening i) = U.toMPSTensor := by
    funext i
    simp only [normalizedFlattening, smul_smul, mul_inv_cancel₀ hc, one_smul]
  rw [← hU']
  obtain ⟨data⟩ := hU.isMPUCanonicalForm
  exact ⟨data.smul _ hc⟩

/-- **Canonical form survives attaching an identity ancilla.** If an MPU tensor
\(\mathcal U\) is in canonical form, then so is \(\mathcal U^{(p)}\) for every
\(p>0\).

Source: arXiv:1703.09188, Definition `def:equivalent-tensors`, lines 706--724,
with Proposition `prop:normal-tensor`, lines 344--354. -/
theorem IsMPU.isMPUCanonicalForm_tensorPhysicalId [NeZero d] [NeZero D]
    {U : MPOTensor d D} (hU : IsMPU U)
    (hcf : MPSTensor.IsMPUCanonicalForm U.toMPSTensor) {p : ℕ} (hp : 0 < p) :
    MPSTensor.IsMPUCanonicalForm (MPOTensor.tensorPhysicalId U p).toMPSTensor := by
  have : NeZero p := ⟨hp.ne'⟩
  apply isMPUCanonicalForm_of_isNormalTensor_normalizedFlattening
  rw [normalizedFlattening_tensorPhysicalId U p hp]
  exact (isNormalTensor_normalizedDiagonalLift
    (hU.isNormalTensor_normalizedFlattening_of_mpuCanonicalForm hcf) p hp).reindexPhysical _

/-- **Canonical form survives blocking.** If an MPU tensor \(\mathcal U\) is in
canonical form, then so is \(\mathcal U_k\) for every \(k>0\).

Source: arXiv:1703.09188, blocking, lines 297--305, with Proposition
`prop:normal-tensor`, lines 344--354. -/
theorem IsMPU.isMPUCanonicalForm_blockTensor [NeZero d] [NeZero D]
    {U : MPOTensor d D} (hU : IsMPU U)
    (hcf : MPSTensor.IsMPUCanonicalForm U.toMPSTensor) {k : ℕ} (hk : 0 < k) :
    MPSTensor.IsMPUCanonicalForm (MPOTensor.blockTensor U k).toMPSTensor := by
  have : NeZero (MPSTensor.blockPhysDim d k) := ⟨by
    rw [MPSTensor.blockPhysDim_eq_pow]
    exact pow_ne_zero k (NeZero.ne d)⟩
  apply isMPUCanonicalForm_of_isNormalTensor_normalizedFlattening
  rw [normalizedFlattening_blockTensor]
  exact ((hU.isNormalTensor_normalizedFlattening_of_mpuCanonicalForm hcf).blockTensor k
    hk).reindexPhysical _

/-- **Canonical form survives attaching an identity ancilla and blocking.** If an
MPU tensor \(\mathcal U\) is in canonical form, then so is
\((\mathcal U^{(p)})_k\) for every \(p>0\) and \(k>0\).

Source: arXiv:1703.09188, Definitions `def:strictly-equivalent-tensors` and
`def:equivalent-tensors`, lines 706--724, with Proposition
`prop:normal-tensor`, lines 344--354. -/
theorem IsMPU.isMPUCanonicalForm_blockTensor_tensorPhysicalId [NeZero d] [NeZero D]
    {U : MPOTensor d D} (hU : IsMPU U)
    (hcf : MPSTensor.IsMPUCanonicalForm U.toMPSTensor)
    {p k : ℕ} (hp : 0 < p) (hk : 0 < k) :
    MPSTensor.IsMPUCanonicalForm
      (MPOTensor.blockTensor (MPOTensor.tensorPhysicalId U p) k).toMPSTensor := by
  have : NeZero p := ⟨hp.ne'⟩
  exact (hU.tensorPhysicalId p hp).isMPUCanonicalForm_blockTensor
    (hU.isMPUCanonicalForm_tensorPhysicalId hcf hp) hk

end MPOTensor
