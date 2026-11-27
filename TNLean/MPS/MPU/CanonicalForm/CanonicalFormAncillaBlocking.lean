/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.CanonicalForm.MPUCanonicalForm
import TNLean.MPS.MPU.CanonicalForm.PhysicalAncilla
import TNLean.MPS.CanonicalForm.SimpleMPU.FullSupport
import TNLean.MPS.CanonicalForm.NormalBlocks.Blocking
import TNLean.MPS.CanonicalForm.PhysicalReindex

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

* `MPTensor.IsNormalTensor.isMPUCanonicalForm`: a normal tensor is in MPU
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

open MPTensor

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- **A canonical block is in canonical form**, as the canonical form with one block of weight
one filling the bond space.

Source: arXiv:1703.09188, canonical form, lines 258--267. -/
theorem _root_.MPTensor.IsMPUCanonicalBlock.isMPUCanonicalForm [NeZero D] {α : Type*}
    [Fintype α] {A : MPTensor α (Fin D)}
    (hA : IsMPUCanonicalBlock A) : IsMPUCanonicalForm A := by
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
    blocks_canonical := fun _ => hA
    total_dim_eq := by simp }⟩
  · have hcard : Fintype.card (Fin D) = Fintype.card (Fin (∑ _ : Fin 1, D)) := by simp
    exact (Matrix.mul_eq_one_comm_of_card_eq _ _ ℂ
      (A := (Vᴴ : Matrix (Fin D) (Fin (∑ _ : Fin 1, D)) ℂ))
      (B := V) hcard).mp hV
  · intro i
    have hmul := MPSTensor.toTensorFromBlocks_mul_blockInclusion
      (fun _ : Fin 1 => (1 : ℂ)) (fun _ : Fin 1 => A) 0 i
    have hmul' : MPTensor.toTensorFromBlocks (fun _ : Fin 1 => (1 : ℂ))
        (fun _ : Fin 1 => A) i * V = V * A i := by
      simpa only [one_smul] using hmul
    calc
      A i = (Vᴴ * V) * A i := by rw [hV, Matrix.one_mul]
      _ = Vᴴ * (MPTensor.toTensorFromBlocks
            (fun _ : Fin 1 => (1 : ℂ)) (fun _ : Fin 1 => A) i * V) := by
              rw [hmul', Matrix.mul_assoc]
      _ = (Vᴴ * MPTensor.toTensorFromBlocks (fun _ : Fin 1 => (1 : ℂ))
            (fun _ : Fin 1 => A) i) * V :=
              (Matrix.mul_assoc Vᴴ _ V).symm

/-- A normal tensor is in MPU canonical form, with one block of weight one
filling the bond space.

Source: arXiv:1703.09188, canonical form, lines 259--267. -/
theorem _root_.MPTensor.IsNormalTensor.isMPUCanonicalForm {α : Type*} [Fintype α]
    {A : MPTensor α (Fin D)}
    (hA : IsNormalTensor A) : IsMPUCanonicalForm A :=
  have : NeZero D := ⟨hA.bondDim_ne_zero⟩
  IsMPUCanonicalBlock.isMPUCanonicalForm ⟨hA.no_invariant_proj, hA.spectral_radius_one⟩

end MPSTensor

namespace MPOTensor

variable {d D : ℕ}

/-- If the normalized tensor of an MPO tensor is normal, the tensor itself is in
canonical form: its letters are the normalized letters with weight \(d^{1/2}\).

Source: arXiv:1703.09188, canonical form, lines 259--267. -/
theorem isMPUCanonicalForm_of_isNormalTensor_normalizedFlattening [NeZero d]
    {U : MPOTensor d D} (hU : MPTensor.IsNormalTensor U.normalizedFlattening) :
    MPTensor.IsMPUCanonicalForm U := by
  have hc : (Real.sqrt d : ℂ) ≠ 0 := by
    have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    exact_mod_cast (Real.sqrt_pos.mpr hd).ne'
  obtain ⟨data⟩ := hU.isMPUCanonicalForm
  have h := data.smul _ hc
  rw [sqrt_smul_normalizedFlattening] at h
  exact ⟨h⟩

/-- **Canonical form survives attaching an identity ancilla.** If an MPU tensor
\(\mathcal U\) is in canonical form, then so is \(\mathcal U^{(p)}\) for every
\(p>0\).

Source: arXiv:1703.09188, Definition `def:equivalent-tensors`, lines 706--724,
with Proposition `prop:normal-tensor`, lines 344--354. -/
theorem IsMPU.isMPUCanonicalForm_tensorPhysicalId [NeZero d] [NeZero D]
    {U : MPOTensor d D} (hU : IsMPU U)
    (hcf : MPTensor.IsMPUCanonicalForm U) {p : ℕ} (hp : 0 < p) :
    MPTensor.IsMPUCanonicalForm (MPOTensor.tensorPhysicalId U p) := by
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
    (hcf : MPTensor.IsMPUCanonicalForm U) {k : ℕ} (hk : 0 < k) :
    MPTensor.IsMPUCanonicalForm (MPOTensor.blockTensor U k) := by
  have : NeZero (Kraus.blockPhysDim d k) := ⟨by
    rw [Kraus.blockPhysDim_eq_pow]
    exact pow_ne_zero k (NeZero.ne d)⟩
  apply isMPUCanonicalForm_of_isNormalTensor_normalizedFlattening
  rw [normalizedFlattening_blockTensor, blockTensor_eq_reindexPhysical]
  exact ((((hU.isNormalTensor_normalizedFlattening_of_mpuCanonicalForm hcf).reindexPhysical
    finProdFinEquiv.symm).blockTensor k hk).reindexPhysical _).reindexPhysical _

/-- **Canonical form survives attaching an identity ancilla and blocking.** If an
MPU tensor \(\mathcal U\) is in canonical form, then so is
\((\mathcal U^{(p)})_k\) for every \(p>0\) and \(k>0\).

Source: arXiv:1703.09188, Definitions `def:strictly-equivalent-tensors` and
`def:equivalent-tensors`, lines 706--724, with Proposition
`prop:normal-tensor`, lines 344--354. -/
theorem IsMPU.isMPUCanonicalForm_blockTensor_tensorPhysicalId [NeZero d] [NeZero D]
    {U : MPOTensor d D} (hU : IsMPU U)
    (hcf : MPTensor.IsMPUCanonicalForm U)
    {p k : ℕ} (hp : 0 < p) (hk : 0 < k) :
    MPTensor.IsMPUCanonicalForm
      (MPOTensor.blockTensor (MPOTensor.tensorPhysicalId U p) k) := by
  have : NeZero p := ⟨hp.ne'⟩
  exact (hU.tensorPhysicalId p hp).isMPUCanonicalForm_blockTensor
    (hU.isMPUCanonicalForm_tensorPhysicalId hcf hp) hk

end MPOTensor
