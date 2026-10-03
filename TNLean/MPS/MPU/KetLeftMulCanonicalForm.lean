/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.MPUCanonicalForm
import TNLean.MPS.MPDO.FirstSite
import TNLean.MPS.Periodic.Applications
import QICLean.Algebra.MatrixReindexUnitary

/-!
# Canonical form under a unitary on the physical output

A unitary on the physical output of an MPO tensor acts on its flattened MPS
alphabet as \(P\otimes I\). This physical rotation preserves every irreducible
canonical block and its transfer normalization. In particular, it preserves the
canonical endpoints used in symmetry-preserving MPU paths.

Source: arXiv:1703.09188, canonical form at lines 259--267 and
Section `othersymmetries`, lines 1295--1332.
-/

open scoped Matrix BigOperators Kronecker

namespace MPSTensor
variable {d D : ℕ}

private noncomputable def rotateMPUCanonicalFormData
    {A : MPSTensor d D} (data : MPUCanonicalFormData A)
    (P : Matrix (Fin d) (Fin d) ℂ) (hP : P ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    MPUCanonicalFormData (rotatePhysical P A) := by
  refine
    { r := data.r
      dim := data.dim
      dim_pos := data.dim_pos
      weights := data.weights
      weights_ne_zero := data.weights_ne_zero
      blocks := fun k => rotatePhysical P (data.blocks k)
      ambient_coisometry := data.ambient_coisometry
      coisometric := data.coisometric
      total_dim_eq := data.total_dim_eq
      blocks_canonical := fun k =>
        { irreducible := isIrreducibleTensor_rotatePhysical _ _
            (Matrix.mem_unitaryGroup_iff.mp hP) (data.blocks_canonical k).irreducible
          spectral_radius_one := by
            rw [transferMap_rotatePhysical _ _ (Matrix.mem_unitaryGroup_iff.mp hP)]
            exact (data.blocks_canonical k).spectral_radius_one }
      reconstruct := ?_ }
  intro i
  rw [← rotatePhysical_toTensorFromBlocks]
  simp only [rotatePhysical_apply]
  simp_rw [data.reconstruct]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

end MPSTensor

namespace MPOTensor
variable {d D : ℕ}

private noncomputable def ketLeftPhysicalMatrix
    (P : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin (d * d)) (Fin (d * d)) ℂ :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv
    (P ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ))

private theorem ketLeftPhysicalMatrix_mem_unitaryGroup
    (P : Matrix (Fin d) (Fin d) ℂ) (hP : P ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    ketLeftPhysicalMatrix P ∈ Matrix.unitaryGroup (Fin (d * d)) ℂ :=
  Matrix.reindex_mem_unitaryGroup _ _ (Matrix.kronecker_mem_unitary hP (one_mem _))

private theorem toMPSTensor_ketLeftMul (M : MPOTensor d D)
    (P : Matrix (Fin d) (Fin d) ℂ) :
    (M.ketLeftMul P).toMPSTensor =
      MPSTensor.rotatePhysical (ketLeftPhysicalMatrix P) M.toMPSTensor := by
  classical
  funext p
  symm
  change (∑ q : Fin (d * d), _ • M q.divNat q.modNat) =
    ∑ k : Fin d, P p.divNat k • M k p.modNat
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp [ketLeftPhysicalMatrix, Matrix.reindex_apply,
    Matrix.one_apply, MPSTensor.finProdFinEquiv_divNat,
    MPSTensor.finProdFinEquiv_modNat]

/-- Multiplication on the physical output by a unitary preserves MPU canonical form.

Each canonical block is rotated by the doubled physical unitary \(P\otimes I\).
The block dimensions, weights, and ambient coisometry are unchanged; the rotation
preserves irreducibility and the transfer map.

Source: arXiv:1703.09188, canonical form at lines 259--267 and the symmetry
transformation in Section `othersymmetries`, lines 1295--1332. -/
theorem isMPUCanonicalForm_ketLeftMul (M : MPOTensor d D)
    (hM : MPSTensor.IsMPUCanonicalForm M.toMPSTensor)
    (P : Matrix (Fin d) (Fin d) ℂ) (hP : P ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    MPSTensor.IsMPUCanonicalForm (M.ketLeftMul P).toMPSTensor := by
  obtain ⟨data⟩ := hM
  rw [toMPSTensor_ketLeftMul]
  exact ⟨MPSTensor.rotateMPUCanonicalFormData data _
    (ketLeftPhysicalMatrix_mem_unitaryGroup P hP)⟩

end MPOTensor
