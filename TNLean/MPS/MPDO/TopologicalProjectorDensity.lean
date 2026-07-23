/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinTupleEquiv
import TNLean.MPS.MPDO.PhysicalSectorCoordinateTransport
import TNLean.MPS.MPDO.TopologicalProjectorRecursion
import TNLean.MPS.MPDO.VerticalProductPairBlocks

/-!
# The all-label topological-projector density identity

This file sums the fixed-label recursion over every vertical-canonical label and every
multiplicity copy.  The diagonal coefficient is the corresponding entry of
`μ^{⊗ (N + 1)}`.  The second factor reconstructs each fixed-label transfer from the recursive
operator `Q`.

The result is the density identity at line 999 of arXiv:1606.00608 in the direct-sum
coordinates selected by a `BNTFusionTensorClause`.  It does not prove the following
commutator, the terminal spectral refinement, or the commuting-Hamiltonian theorem.

## Main result

* `reindex_mpo_changePhysicalBasis_eq_verticalWeightTensorPower_mul`:
  the positive-length physical density, in the retained vertical coordinates, is
  `μ^{⊗ (N + 1)}` times the reconstructed recursive operator.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608, Theorem IV.13 and
  lines 986--999.
-/

open scoped Matrix BigOperators
open MPOTensor.BNTFusionCoisometryFamily
open MPOTensor.PhysicalSectorFactorization

namespace MPOTensor.BNTFusionTensorClause

variable {d D : ℕ} {M : MPOTensor d D}

/-- A vertical-canonical label together with one copy in its multiplicity space.

Source: arXiv:1606.00608, the block label and diagonal entry of `μ` at line 999. -/
abbrev TopologicalDensityLabel (H : BNTFusionTensorClause M) :=
  (α : Fin H.labelCount) × Fin (H.multiplicity α)

/-- A choice of a vertical-canonical label and multiplicity copy at every site.

Source: arXiv:1606.00608, the label sectors of `μ^{⊗ N}` at line 999. -/
abbrev TopologicalDensitySector (H : BNTFusionTensorClause M) (N : ℕ) :=
  Fin (N + 1) → TopologicalDensityLabel H

/-- The reverse list of labels appended to the initial label in the recursive convention.

Source: arXiv:1606.00608, recursive application of equation `Ualphabeta` at line 999. -/
def topologicalFusionPrevious (H : BNTFusionTensorClause M) :
    {N : ℕ} → TopologicalDensitySector H N → List (Fin H.labelCount)
  | 0, _ => []
  | N + 1, q =>
      (q (Fin.last (N + 1))).1 ::
        topologicalFusionPrevious H (fun n : Fin (N + 1) => q n.castSucc)

/-- The first label in the recursive prefix convention. -/
def topologicalFusionInitial (H : BNTFusionTensorClause M) :
    {N : ℕ} → TopologicalDensitySector H N → Fin H.labelCount
  | 0, q => (q 0).1
  | N + 1, q =>
      topologicalFusionInitial H (fun n : Fin (N + 1) => q n.castSucc)

/-- The sitewise product-bond space for one all-label sector. -/
abbrev TopologicalSectorBond (H : BNTFusionTensorClause M) {N : ℕ}
    (q : TopologicalDensitySector H N) :=
  (n : Fin (N + 1)) → Fin (H.bondDim (q n).1)

private def piSnocEquiv {N : ℕ} {α : Fin (N + 1) → Type*} :
    ((n : Fin (N + 1)) → α n) ≃
      ((n : Fin N) → α n.castSucc) × α (Fin.last N) where
  toFun x := ⟨Fin.init x, x (Fin.last N)⟩
  invFun x := Fin.snoc x.1 x.2
  left_inv x := Fin.snoc_init_self x
  right_inv x := by
    apply Prod.ext
    · exact Fin.init_snoc x.2 x.1
    · exact Fin.snoc_last x.2 x.1

/-- The bond dimension stored on the tensor-attached clause is the bond dimension of its
fusion family. -/
private def attachedBondEquiv (H : BNTFusionTensorClause M) (α : Fin H.labelCount) :
    Fin (H.bondDim α) ≃ Fin (H.toBNTFusionCoisometryFamily.bondDim α) :=
  finCongr rfl

@[simp] private theorem attachedBondEquiv_apply
    (H : BNTFusionTensorClause M) (α : Fin H.labelCount) (x : Fin (H.bondDim α)) :
    attachedBondEquiv H α x = x :=
  rfl

@[simp] private theorem attachedFusionTensor_apply
    (H : BNTFusionTensorClause M) (α : Fin H.labelCount) (a b : Fin D)
    (x y : Fin (H.bondDim α)) :
    H.toBNTFusionCoisometryFamily.tensor α a b x y =
      H.tensor α (finProdFinEquiv (a, b)) x y :=
  rfl

/-- The canonical left-associated product-bond coordinate used by the fusion recursion. -/
def fusionChainBondEquiv (H : BNTFusionTensorClause M) :
    {N : ℕ} → (q : TopologicalDensitySector H N) →
      TopologicalSectorBond H q ≃
        Fin (BNTFusionCoisometryFamily.fusionChainBondDim
          H.toBNTFusionCoisometryFamily (topologicalFusionInitial H q)
            (topologicalFusionPrevious H q))
  | 0, q =>
      (piSnocEquiv.trans (Equiv.uniqueProd _ _)).trans
        (finCongr (by
          simp [topologicalFusionInitial, topologicalFusionPrevious,
            BNTFusionCoisometryFamily.fusionChainBondDim]
          rfl))
  | N + 1, q =>
      piSnocEquiv.trans <|
        (((fusionChainBondEquiv H
          (fun n : Fin (N + 1) => q n.castSucc)).prodCongr
            (attachedBondEquiv H (q (Fin.last (N + 1))).1)).trans finProdFinEquiv)

@[simp] private theorem fusionChainBondEquiv_zero_apply
    (H : BNTFusionTensorClause M) (q : TopologicalDensitySector H 0)
    (x : TopologicalSectorBond H q) :
    fusionChainBondEquiv H q x = x 0 := by
  apply Fin.ext
  rfl

@[simp] private theorem finProdFinEquiv_symm_fusionChainBondEquiv_succ
    (H : BNTFusionTensorClause M) {N : ℕ}
    (q : TopologicalDensitySector H (N + 1)) (x : TopologicalSectorBond H q) :
    finProdFinEquiv.symm (fusionChainBondEquiv H q x) =
      (fusionChainBondEquiv H (fun n : Fin (N + 1) => q n.castSucc) (Fin.init x),
        attachedBondEquiv H (q (Fin.last (N + 1))).1 (x (Fin.last (N + 1)))) := by
  change finProdFinEquiv.symm
      (finProdFinEquiv
        (fusionChainBondEquiv H (fun n : Fin (N + 1) => q n.castSucc) (Fin.init x),
          attachedBondEquiv H (q (Fin.last (N + 1))).1
            (x (Fin.last (N + 1))))) = _
  exact finProdFinEquiv.symm_apply_apply _

@[simp] private theorem fusionChainBondEquiv_succ_apply
    (H : BNTFusionTensorClause M) {N : ℕ}
    (q : TopologicalDensitySector H (N + 1)) (x : TopologicalSectorBond H q) :
    fusionChainBondEquiv H q x =
      finProdFinEquiv
        (fusionChainBondEquiv H (fun n : Fin (N + 1) => q n.castSucc) (Fin.init x),
          attachedBondEquiv H (q (Fin.last (N + 1))).1 (x (Fin.last (N + 1)))) :=
  rfl

/-- Apply the retained vertical coordinate change at every site and group the result by its
label and multiplicity sector. -/
def topologicalDensityChainEquiv (H : BNTFusionTensorClause M) (N : ℕ) :
    (Fin (N + 1) →
      Fin (∑ q : Fin (∑ α : Fin H.labelCount, H.multiplicity α),
        verticalCopyDim H.bondDim H.multiplicity q)) ≃
      (q : TopologicalDensitySector H N) × TopologicalSectorBond H q :=
  (Equiv.piCongrRight fun _ : Fin (N + 1) =>
    verticalCopyCoordinateEquiv H.bondDim H.multiplicity).trans piSigmaEquiv

/-- The diagonal entry of `μ^{⊗ (N + 1)}` selected by a sector.

Source: arXiv:1606.00608, the tensor power of `μ` at line 999. -/
noncomputable def topologicalSectorWeight (H : BNTFusionTensorClause M) {N : ℕ}
    (q : TopologicalDensitySector H N) : ℂ :=
  ∏ n, H.weight (q n).1 (q n).2

/-- In one retained copy, the physically changed tensor is the corresponding weighted BNT
letter. -/
private theorem changePhysicalBasis_verticalCopy_same
    (H : BNTFusionTensorClause M) (q : TopologicalDensityLabel H)
    (x y : Fin (H.bondDim q.1)) :
    changePhysicalBasis H.verticalCoisometry M
        ((verticalCopyCoordinateEquiv H.bondDim H.multiplicity).symm ⟨q, x⟩)
        ((verticalCopyCoordinateEquiv H.bondDim H.multiplicity).symm ⟨q, y⟩) =
      H.weight q.1 q.2 •
        fun a b => H.tensor q.1 (finProdFinEquiv (a, b)) x y := by
  ext a b
  have h := congrFun (congrFun (H.forward (finProdFinEquiv (a, b)))
    ((verticalCopyCoordinateEquiv H.bondDim H.multiplicity).symm ⟨q, x⟩))
    ((verticalCopyCoordinateEquiv H.bondDim H.multiplicity).symm ⟨q, y⟩)
  have hv :
      verticalTensor M (finProdFinEquiv (a, b)) = physicalSlice M a b := by
    ext i j
    exact verticalTensor_finProdFinEquiv M a b i j
  rw [hv] at h
  rw [verticalAssembledTensor_reindex_copyCoordinates] at h
  simpa only [changePhysicalBasis, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_symm, Equiv.apply_symm_apply,
    Matrix.blockDiagonal'_apply_eq, Matrix.smul_apply, Pi.smul_apply] using h

/-- Distinct retained copies do not mix under the physical coordinate change. -/
private theorem changePhysicalBasis_verticalCopy_ne
    (H : BNTFusionTensorClause M) {q r : TopologicalDensityLabel H}
    (hqr : q ≠ r) (x : Fin (H.bondDim q.1)) (y : Fin (H.bondDim r.1)) :
    changePhysicalBasis H.verticalCoisometry M
        ((verticalCopyCoordinateEquiv H.bondDim H.multiplicity).symm ⟨q, x⟩)
        ((verticalCopyCoordinateEquiv H.bondDim H.multiplicity).symm ⟨r, y⟩) = 0 := by
  ext a b
  have h := congrFun (congrFun (H.forward (finProdFinEquiv (a, b)))
    ((verticalCopyCoordinateEquiv H.bondDim H.multiplicity).symm ⟨q, x⟩))
    ((verticalCopyCoordinateEquiv H.bondDim H.multiplicity).symm ⟨r, y⟩)
  have hv :
      verticalTensor M (finProdFinEquiv (a, b)) = physicalSlice M a b := by
    ext i j
    exact verticalTensor_finProdFinEquiv M a b i j
  rw [hv] at h
  rw [verticalAssembledTensor_reindex_copyCoordinates] at h
  simpa only [changePhysicalBasis, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_symm, Equiv.apply_symm_apply,
    Matrix.blockDiagonal'_apply_ne _ _ _ hqr, Matrix.zero_apply] using h

/-- The retained vertical coordinate change reconstructs the original tensor when followed
by its adjoint.

Source: arXiv:1606.00608, Proposition 4.13, lines 943--951. -/
theorem changePhysicalBasis_conjTranspose_verticalCoisometry
    (H : BNTFusionTensorClause M) :
    changePhysicalBasis H.verticalCoisometryᴴ
        (changePhysicalBasis H.verticalCoisometry M) = M := by
  ext i j a b
  simp only [changePhysicalBasis, Matrix.conjTranspose_conjTranspose]
  change
    (H.verticalCoisometryᴴ *
        (H.verticalCoisometry * physicalSlice M a b * H.verticalCoisometryᴴ) *
        H.verticalCoisometry) i j =
      M i j a b
  have hv :
      verticalTensor M (finProdFinEquiv (a, b)) = physicalSlice M a b := by
    ext u v
    exact verticalTensor_finProdFinEquiv M a b u v
  rw [← hv, H.forward]
  have h := congrFun (congrFun (H.reconstruction (finProdFinEquiv (a, b))) i) j
  simpa only [verticalTensor_finProdFinEquiv] using h.symm

/-- The horizontal matrix obtained by fixing the two simple-bond coordinates at one site. -/
private def topologicalBondSlice (H : BNTFusionTensorClause M) {N : ℕ}
    (q : TopologicalDensitySector H N) (x y : TopologicalSectorBond H q)
    (n : Fin (N + 1)) : Matrix (Fin D) (Fin D) ℂ :=
  fun a b => H.tensor (q n).1 (finProdFinEquiv (a, b)) (x n) (y n)

/-- A fixed entry of the left-associated fusion tensor is the ordered product of the
corresponding horizontal slices. -/
private theorem fusionChainTensor_apply_fusionChainBondEquiv
    (H : BNTFusionTensorClause M) {N : ℕ}
    (q : TopologicalDensitySector H N) (x y : TopologicalSectorBond H q)
    (a b : Fin D) :
    BNTFusionCoisometryFamily.fusionChainTensor H.toBNTFusionCoisometryFamily
          (topologicalFusionInitial H q) (topologicalFusionPrevious H q) a b
          (fusionChainBondEquiv H q x) (fusionChainBondEquiv H q y) =
      (List.ofFn fun n : Fin (N + 1) => topologicalBondSlice H q x y n).prod a b := by
  induction N generalizing a b with
  | zero =>
      rw [fusionChainBondEquiv_zero_apply, fusionChainBondEquiv_zero_apply]
      simp [topologicalFusionInitial, topologicalFusionPrevious,
        BNTFusionCoisometryFamily.fusionChainTensor, topologicalBondSlice,
        BNTFusionTensorClause.toBNTFusionCoisometryFamily]
  | succ N ih =>
      rw [List.ofFn_succ', List.prod_concat]
      rw [fusionChainBondEquiv_succ_apply H q x,
        fusionChainBondEquiv_succ_apply H q y]
      simp only [topologicalFusionInitial, topologicalFusionPrevious,
        BNTFusionCoisometryFamily.fusionChainTensor]
      simp only [mulTensor_apply, Matrix.submatrix_apply]
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      rw [attachedBondEquiv_apply, attachedBondEquiv_apply]
      rw [Matrix.sum_apply, Matrix.mul_apply]
      simp only [Matrix.kroneckerMap_apply,
        attachedFusionTensor_apply]
      apply Finset.sum_congr rfl
      intro j _
      rw [ih (fun n : Fin (N + 1) => q n.castSucc)
        (Fin.init x) (Fin.init y)]
      rfl

/-- The physical-trace transfer of a label sequence is the trace of its ordered horizontal
slice product. -/
private theorem reindex_physTraceTransfer_fusionChainTensor_apply
    (H : BNTFusionTensorClause M) {N : ℕ}
    (q : TopologicalDensitySector H N) (x y : TopologicalSectorBond H q) :
    Matrix.reindex (fusionChainBondEquiv H q).symm
          (fusionChainBondEquiv H q).symm
          (physTraceTransfer
            (BNTFusionCoisometryFamily.fusionChainTensor
              H.toBNTFusionCoisometryFamily
              (topologicalFusionInitial H q) (topologicalFusionPrevious H q))) x y =
      Matrix.trace
        (List.ofFn fun n : Fin (N + 1) => topologicalBondSlice H q x y n).prod := by
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
    physTraceTransfer, Matrix.sum_apply, Matrix.trace]
  apply Finset.sum_congr rfl
  intro a _
  exact fusionChainTensor_apply_fusionChainBondEquiv H q x y a a

private theorem prod_ofFn_smul_matrix {n N : ℕ}
    (c : Fin N → ℂ) (A : Fin N → Matrix (Fin n) (Fin n) ℂ) :
    (List.ofFn fun i => c i • A i).prod =
      (∏ i, c i) • (List.ofFn A).prod := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons,
        Fin.prod_univ_succ, ih]
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

@[simp] theorem topologicalDensityChainEquiv_symm_apply
    (H : BNTFusionTensorClause M) (N : ℕ)
    (q : TopologicalDensitySector H N) (x : TopologicalSectorBond H q)
    (n : Fin (N + 1)) :
    (topologicalDensityChainEquiv H N).symm ⟨q, x⟩ n =
      (verticalCopyCoordinateEquiv H.bondDim H.multiplicity).symm ⟨q n, x n⟩ :=
  rfl

/-- The vertical weight `μ^{⊗ (N + 1)}` in all-label direct-sum coordinates.

Source: arXiv:1606.00608, the first factor of the density identity at line 999. -/
noncomputable def verticalWeightTensorPower (H : BNTFusionTensorClause M) (N : ℕ) :
    Matrix ((q : TopologicalDensitySector H N) × TopologicalSectorBond H q)
      ((q : TopologicalDensitySector H N) × TopologicalSectorBond H q) ℂ :=
  Matrix.blockDiagonal' fun q =>
    topologicalSectorWeight H q •
      (1 : Matrix (TopologicalSectorBond H q) (TopologicalSectorBond H q) ℂ)

/-- The direct sum of the reconstructed recursive operators over all label sectors.

The formal coisometry is the adjoint of the source circuit convention: its adjoint followed
by `Q` and then the coisometry is the factor
`\widetilde U Q\widetilde U^\dagger` at line 999 of arXiv:1606.00608.
-/
noncomputable def topologicalProjectorFactor (H : BNTFusionTensorClause M) (N : ℕ) :
    Matrix ((q : TopologicalDensitySector H N) × TopologicalSectorBond H q)
      ((q : TopologicalDensitySector H N) × TopologicalSectorBond H q) ℂ :=
  Matrix.blockDiagonal' fun q =>
    let Fam := H.toBNTFusionCoisometryFamily
    let W := BNTFusionCoisometryFamily.sequentialFusionCoisometry
      Fam (topologicalFusionInitial H q) (topologicalFusionPrevious H q)
    Matrix.reindex (fusionChainBondEquiv H q).symm
      (fusionChainBondEquiv H q).symm <|
        Wᴴ *
          BNTFusionCoisometryFamily.recursiveProjectorQ Fam
            (fun γ => physTraceTransfer (Fam.tensor γ))
            (topologicalFusionInitial H q) (topologicalFusionPrevious H q) *
          W

/-- The all-label density in vertical-canonical direct-sum coordinates.

Each sector is its `μ^{⊗ (N + 1)}` coefficient times the physical-trace transfer of the
corresponding left-associated product tensor.

Source: arXiv:1606.00608, the density identity at line 999. -/
noncomputable def allLabelDensity (H : BNTFusionTensorClause M) (N : ℕ) :
    Matrix ((q : TopologicalDensitySector H N) × TopologicalSectorBond H q)
      ((q : TopologicalDensitySector H N) × TopologicalSectorBond H q) ℂ :=
  Matrix.blockDiagonal' fun q =>
    let Fam := H.toBNTFusionCoisometryFamily
    topologicalSectorWeight H q •
      (Matrix.reindex (fusionChainBondEquiv H q).symm
        (fusionChainBondEquiv H q).symm <|
          physTraceTransfer
            (BNTFusionCoisometryFamily.fusionChainTensor
              Fam (topologicalFusionInitial H q) (topologicalFusionPrevious H q)))

/-- Applying the vertical coisometry at every site identifies the physical density operator
of the original tensor with the all-label density.

Source: arXiv:1606.00608, Proposition 4.13 and Theorem IV.13, lines 943--951 and
986--999. -/
theorem reindex_mpo_changePhysicalBasis_eq_allLabelDensity
    (H : BNTFusionTensorClause M) (N : ℕ) :
    Matrix.reindex (topologicalDensityChainEquiv H N)
        (topologicalDensityChainEquiv H N)
        (mpo (changePhysicalBasis H.verticalCoisometry M) (N + 1)) =
      allLabelDensity H N := by
  classical
  ext ⟨q, x⟩ ⟨r, y⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  by_cases hqr : q = r
  · subst r
    rw [mpo_apply, mpoMatrixEntry, evalWord_ofFn]
    simp_rw [topologicalDensityChainEquiv_symm_apply]
    have hlocal : ∀ i : Fin (N + 1),
        changePhysicalBasis H.verticalCoisometry M
            ((verticalCopyCoordinateEquiv H.bondDim H.multiplicity).symm
              ⟨q i, x i⟩)
            ((verticalCopyCoordinateEquiv H.bondDim H.multiplicity).symm
              ⟨q i, y i⟩) =
          H.weight (q i).1 (q i).2 • topologicalBondSlice H q x y i := by
      intro i
      change
        changePhysicalBasis H.verticalCoisometry M
            ((verticalCopyCoordinateEquiv H.bondDim H.multiplicity).symm
              ⟨q i, x i⟩)
            ((verticalCopyCoordinateEquiv H.bondDim H.multiplicity).symm
              ⟨q i, y i⟩) =
          H.weight (q i).1 (q i).2 •
            (fun a b =>
              H.tensor (q i).1 (finProdFinEquiv (a, b)) (x i) (y i))
      exact changePhysicalBasis_verticalCopy_same H (q i) (x i) (y i)
    simp_rw [hlocal]
    rw [prod_ofFn_smul_matrix, Matrix.trace_smul]
    unfold allLabelDensity
    rw [Matrix.blockDiagonal'_apply_eq]
    simp only [Matrix.smul_apply, smul_eq_mul, topologicalSectorWeight]
    rw [reindex_physTraceTransfer_fusionChainTensor_apply]
  · unfold allLabelDensity
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ hqr]
    have hsite : ∃ n, q n ≠ r n := by
      by_contra h
      apply hqr
      funext n
      exact not_ne_iff.mp (not_exists.mp h n)
    obtain ⟨n, hn⟩ := hsite
    rw [mpo_apply, mpoMatrixEntry, evalWord_ofFn]
    have hzero :
        changePhysicalBasis H.verticalCoisometry M
            ((topologicalDensityChainEquiv H N).symm ⟨q, x⟩ n)
            ((topologicalDensityChainEquiv H N).symm ⟨r, y⟩ n) = 0 := by
      rw [topologicalDensityChainEquiv_symm_apply,
        topologicalDensityChainEquiv_symm_apply]
      exact changePhysicalBasis_verticalCopy_ne H hn (x n) (y n)
    have hmem :
        (0 : Matrix (Fin D) (Fin D) ℂ) ∈
          List.ofFn (fun i : Fin (N + 1) =>
            changePhysicalBasis H.verticalCoisometry M
              ((topologicalDensityChainEquiv H N).symm ⟨q, x⟩ i)
              ((topologicalDensityChainEquiv H N).symm ⟨r, y⟩ i)) :=
      List.mem_ofFn.mpr ⟨n, hzero⟩
    rw [List.prod_eq_zero hmem, Matrix.trace_zero]

/-- The all-label vertical-canonical density is the tensor-power weight times the
topological-projector factor.

Source: arXiv:1606.00608, the identity
`(μ^{⊗ N}) \widetilde U Q \widetilde U^\dagger` at line 999.

**Scope restriction (direct-sum coordinates):** This theorem proves the density identity
after the vertical-canonical coordinate change encoded by `BNTFusionTensorClause`.  The
source commutator at lines 1000--1002 and the spectral refinement beginning at line 1010
remain separate statements, as recorded in
`docs/paper-gaps/cpsv16_topological_projector_recursion.tex`. -/
theorem allLabelDensity_eq_verticalWeightTensorPower_mul_topologicalProjectorFactor
    (H : BNTFusionTensorClause M) (N : ℕ) :
    allLabelDensity H N =
      verticalWeightTensorPower H N * topologicalProjectorFactor H N := by
  unfold allLabelDensity verticalWeightTensorPower topologicalProjectorFactor
  rw [← Matrix.blockDiagonal'_mul]
  apply congrArg Matrix.blockDiagonal'
  funext q
  simp only [Matrix.smul_mul, Matrix.one_mul]
  rw [conjTranspose_sequentialFusionCoisometry_mul_recursiveProjectorQ_physTrace_mul]

/-- The positive-length physical density operator, after the local vertical coordinate
change, is `μ^{⊗ (N + 1)}` times the reconstructed recursive operator.

Source: arXiv:1606.00608, the locally unitarily equivalent density
`(μ^{⊗ N}) \widetilde U Q \widetilde U^\dagger` at line 999.

**Scope restriction (vertical direct-sum coordinates):** The equality is stated after the
sitewise coordinate equivalence induced by the retained-row vertical coisometry.  It does
not assert the commutator at lines 1000--1002 or the spectral refinement beginning at
line 1010; see `docs/paper-gaps/cpsv16_topological_projector_recursion.tex`. -/
theorem reindex_mpo_changePhysicalBasis_eq_verticalWeightTensorPower_mul
    (H : BNTFusionTensorClause M) (N : ℕ) :
    Matrix.reindex (topologicalDensityChainEquiv H N)
        (topologicalDensityChainEquiv H N)
        (mpo (changePhysicalBasis H.verticalCoisometry M) (N + 1)) =
      verticalWeightTensorPower H N * topologicalProjectorFactor H N := by
  rw [reindex_mpo_changePhysicalBasis_eq_allLabelDensity]
  exact allLabelDensity_eq_verticalWeightTensorPower_mul_topologicalProjectorFactor H N

end MPOTensor.BNTFusionTensorClause
