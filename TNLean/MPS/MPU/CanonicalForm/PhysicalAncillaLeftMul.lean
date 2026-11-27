/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.CanonicalForm.PhysicalAncilla
import TNLean.MPS.Operator.PhysicalSector.SitewisePhysicalMatrix
import TNLean.MPS.Operator.Unitary.Basic
import TNLean.MPS.MPU.CanonicalForm.MPUCanonicalForm
import TNLean.MPS.Operator.PairAlphabetBridge
import TNLean.MPS.Operator.Periodic.FirstSite
import TNLean.MPS.Transfer.Irreducible.PeriodicRotation
import QICLean.Algebra.Unitary.MatrixUnitaryBetween

/-!
# Physical output actions with an identity ancilla

The physical matrix \(Q\otimes I_x\), in the product coordinates of
`tensorPhysicalId`, acts on every enlarged physical operator. Its output
action on an ancilla-attached tensor is the ancilla attachment of the
original output action.

Source: arXiv:1703.09188, identity ancillas at lines 706--724 and the output
transformation in Section `othersymmetries`, lines 1301--1322.

It also contains the following results.

* `MPOTensor.IsMPU.ketLeftMul`, `MPOTensor.isMPUCanonicalForm_ketLeftMul`: matrix product unitaries
  under physical left actions.
-/

open MPTensor

section KetLeftMulCanonicalForm

/-!
## Matrix product unitaries under physical left actions

A unitary acting on the ket leg of every local MPO matrix preserves the matrix product unitary
property.

### Canonical form under a unitary on the physical output

A unitary on the physical output of an MPO tensor acts on its flattened MPS
alphabet as \(P\otimes I\). This physical rotation preserves every irreducible
canonical block and its transfer normalization. In particular, it preserves the
canonical endpoints used in symmetry-preserving MPU paths.

Source: arXiv:1703.09188, canonical form at lines 259--267 and
Section `othersymmetries`, lines 1295--1332.
-/

section

open scoped Matrix

namespace MPOTensor

variable {d D : ℕ}

/-- Left multiplication by a one-site unitary preserves the MPU property. -/
theorem IsMPU.ketLeftMul {M : MPOTensor d D} (hM : IsMPU M)
    {P : Matrix (Fin d) (Fin d) ℂ}
    (hP : P ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    IsMPU (M.ketLeftMul P) := by
  intro N hN
  rw [mpo_ketLeftMul]
  apply (Matrix.unitaryGroup (Fin N → Fin d) ℂ).mul_mem
  · rw [Matrix.mem_unitaryGroup_iff']
    rw [Matrix.star_eq_conjTranspose, Matrix.piKronecker_const_isometry P]
    rw [Matrix.mem_unitaryGroup_iff'] at hP
    simpa only [Matrix.star_eq_conjTranspose] using hP
  · exact hM.mpo_mem_unitaryGroup hN

end MPOTensor

end

section

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
        { irreducible := isIrreducibleFamily_rotatePhysical _ _
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
  change (∑ q : Fin (d * d), _ • M (q.divNat, q.modNat)) =
    ∑ k : Fin d, P p.divNat k • M (k, p.modNat)
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp [ketLeftPhysicalMatrix, Matrix.reindex_apply,
    Matrix.one_apply, MPSTensor.finProdFinEquiv_divNat,
    MPSTensor.finProdFinEquiv_modNat]

/-- Multiplication on the physical output by a unitary preserves MPU canonical form.

Each canonical block is rotated by the physical unitary \(P\otimes I\) on the pair alphabet.
The block dimensions, weights, and ambient coisometry are unchanged; the rotation
preserves irreducibility and the transfer map.

Source: arXiv:1703.09188, canonical form at lines 259--267 and the symmetry
transformation in Section `othersymmetries`, lines 1295--1332. -/
theorem isMPUCanonicalForm_ketLeftMul (M : MPOTensor d D)
    (hM : MPTensor.IsMPUCanonicalForm M)
    (P : Matrix (Fin d) (Fin d) ℂ) (hP : P ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    MPTensor.IsMPUCanonicalForm (M.ketLeftMul P) := by
  obtain ⟨data⟩ :=
    (MPTensor.isMPUCanonicalForm_reindexPhysical_iff (A := M) finProdFinEquiv.symm).2 hM
  refine (MPTensor.isMPUCanonicalForm_reindexPhysical_iff finProdFinEquiv.symm).1 ?_
  rw [← toMPSTensor_eq_reindexPhysical, toMPSTensor_ketLeftMul]
  exact ⟨MPSTensor.rotateMPUCanonicalFormData data _
    (ketLeftPhysicalMatrix_mem_unitaryGroup P hP)⟩

end MPOTensor

end

end KetLeftMulCanonicalForm

section PhysicalAncillaLeftMul

open scoped Matrix Kronecker

namespace MPOTensor

variable {d D : ℕ}

/-- The full physical matrix \(Q\otimes I_x\), in sitewise product coordinates.
Source: arXiv:1703.09188, identity ancillas, lines 706--724. -/
noncomputable def physicalIdMatrix (Q : Matrix (Fin d) (Fin d) ℂ) (x : ℕ) :
    Matrix (Fin (d * x)) (Fin (d * x)) ℂ :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv
    (Q ⊗ₖ (1 : Matrix (Fin x) (Fin x) ℂ))

/-- In product coordinates the ancillary physical matrix fixes the ancilla. -/
@[simp] theorem physicalIdMatrix_apply (Q : Matrix (Fin d) (Fin d) ℂ) (x : ℕ)
    (i j : Fin d) (a b : Fin x) :
    physicalIdMatrix Q x (finProdFinEquiv (i, a)) (finProdFinEquiv (j, b)) =
      Q i j * if a = b then 1 else 0 := by
  simp [physicalIdMatrix, Matrix.reindex_apply, Matrix.one_apply]

/-- Identity-ancilla extension preserves the identity physical matrix. -/
@[simp] theorem physicalIdMatrix_one (d x : ℕ) :
    physicalIdMatrix (1 : Matrix (Fin d) (Fin d) ℂ) x = 1 := by
  simp [physicalIdMatrix]

/-- Identity-ancilla extension preserves physical matrix multiplication. -/
theorem physicalIdMatrix_mul (P Q : Matrix (Fin d) (Fin d) ℂ) (x : ℕ) :
    physicalIdMatrix P x * physicalIdMatrix Q x = physicalIdMatrix (P * Q) x := by
  unfold physicalIdMatrix
  calc
    _ = Matrix.reindex finProdFinEquiv finProdFinEquiv
        ((P ⊗ₖ (1 : Matrix (Fin x) (Fin x) ℂ)) * (Q ⊗ₖ 1)) :=
      Matrix.reindexLinearEquiv_mul ℂ ℂ finProdFinEquiv finProdFinEquiv
        finProdFinEquiv _ _
    _ = _ := by rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]

/-- Identity-ancilla extension commutes with adjunction. -/
theorem physicalIdMatrix_conjTranspose (Q : Matrix (Fin d) (Fin d) ℂ) (x : ℕ) :
    (physicalIdMatrix Q x)ᴴ = physicalIdMatrix Qᴴ x := by
  simp [physicalIdMatrix, Matrix.conjTranspose_kronecker]

/-- Identity-ancilla extension commutes with transposition. -/
theorem physicalIdMatrix_transpose (Q : Matrix (Fin d) (Fin d) ℂ) (x : ℕ) :
    (physicalIdMatrix Q x)ᵀ = physicalIdMatrix Qᵀ x := by
  ext i j
  simp [physicalIdMatrix, Matrix.transpose_apply, Matrix.reindex_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, eq_comm]

/-- A real physical matrix remains real after adjoining an identity ancilla. -/
theorem physicalIdMatrix_map_star (Q : Matrix (Fin d) (Fin d) ℂ) (x : ℕ)
    (hQ : Q.map (starRingEnd ℂ) = Q) :
    (physicalIdMatrix Q x).map (starRingEnd ℂ) = physicalIdMatrix Q x := by
  ext i j
  have h := congrFun (congrFun hQ i.divNat) j.divNat
  by_cases hab : i.modNat = j.modNat
  · simpa [physicalIdMatrix, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
      Matrix.one_apply, hab] using h
  · simp [physicalIdMatrix, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
      hab]

/-- A physical unitary tensored with an identity ancilla is unitary. -/
theorem physicalIdMatrix_mem_unitaryGroup (Q : Matrix (Fin d) (Fin d) ℂ) (x : ℕ)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    physicalIdMatrix Q x ∈ Matrix.unitaryGroup (Fin (d * x)) ℂ :=
  Matrix.reindex_mem_unitaryGroup _ _ (Matrix.kronecker_mem_unitary hQ (one_mem _))

/-- Acting by \(Q\otimes I_x\) after identity-ancilla attachment is the
identity-ancilla attachment of the original physical output action.
Source: arXiv:1703.09188, lines 706--724 and Lemma `lemma:sym-trafo-swap`. -/
theorem ketLeftMul_tensorPhysicalId (U : MPOTensor d D)
    (Q : Matrix (Fin d) (Fin d) ℂ) (x : ℕ) :
    (tensorPhysicalId U x).ketLeftMul (physicalIdMatrix Q x) =
      tensorPhysicalId (U.ketLeftMul Q) x := by
  classical
  funext ⟨i, j⟩
  simp only [ketLeftMul]
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  by_cases hab : i.modNat = j.modNat
  · simp [physicalIdMatrix, tensorPhysicalId, ketLeftMul, Matrix.reindex_apply,
      Matrix.kroneckerMap_apply, Matrix.one_apply, hab]
  · simp [physicalIdMatrix, tensorPhysicalId, Matrix.reindex_apply,
      Matrix.kroneckerMap_apply, Matrix.one_apply, hab]

end MPOTensor

end PhysicalAncillaLeftMul
