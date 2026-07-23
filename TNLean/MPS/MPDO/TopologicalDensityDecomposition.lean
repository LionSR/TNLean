/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinTupleEquiv
import TNLean.MPS.MPDO.BNTFusionTensorClauseFromRFP
import TNLean.MPS.MPDO.SitewisePhysicalMatrix
import TNLean.MPS.MPDO.TopologicalProjectorRecursion
import TNLean.MPS.MPDO.VerticalProductPairBlocks

/-!
# Density decomposition by recursive fusion histories

This file combines the vertical canonical form with the recursive fusion circuit.  At every
positive chain length `N`, the retained physical coordinates split as a direct sum over one
BNT label and one multiplicity coordinate at each site.  The appended-label list inside the
fixed-label recursion has length `N - 1`: its initial label is the label at the first site.

In a fixed copy configuration, the diagonal entry of the tensor power of the multiplicity
matrix is the product of the chosen positive weights.  The remaining factor is the recursive
terminal operator transported back through the adjoint sequential fusion coisometry.  Taking
the direct sum over all copy configurations gives the density operator in retained vertical
coordinates.  Applying the adjoint vertical map reconstructs the original density exactly.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Proposition 4.13, lines 943--951, and the density identity at line 999
-/

open scoped Matrix BigOperators Kronecker

noncomputable section

namespace MPOTensor.BNTFusionTensorClause

variable {d D : ℕ} {M : MPOTensor d D}

open MPOTensor.PhysicalSectorFactorization
open _root_.MPOTensor.BNTFusionCoisometryFamily

/-- The retained one-site physical dimension of a chosen vertical canonical decomposition.

Source: arXiv:1606.00608, Proposition 4.13, lines 943--951. -/
abbrev verticalRetainedDim (H : BNTFusionTensorClause M) : ℕ :=
  ∑ q : Fin (∑ α : Fin H.labelCount, H.multiplicity α),
    verticalCopyDim H.bondDim H.multiplicity q

/-- A BNT label together with one coordinate in its positive multiplicity space.

Source: arXiv:1606.00608, Proposition 4.13, lines 943--951. -/
abbrev VerticalCopy (H : BNTFusionTensorClause M) : Type :=
  (α : Fin H.labelCount) × Fin (H.multiplicity α)

/-- The simple-bond coordinates in a fixed copy configuration of a positive chain.

Source: arXiv:1606.00608, density identity at line 999. -/
abbrev VerticalCopyChainFiber (H : BNTFusionTensorClause M) {N : ℕ}
    (p : Fin (N + 1) → H.VerticalCopy) : Type :=
  (n : Fin (N + 1)) → Fin (H.bondDim (p n).1)

/-- Retained chain coordinates grouped by their BNT-copy configuration.

Source: arXiv:1606.00608, density identity at line 999. -/
abbrev VerticalCopyChainIndex (H : BNTFusionTensorClause M) (N : ℕ) : Type :=
  Σ p : Fin (N + 1) → H.VerticalCopy, H.VerticalCopyChainFiber p

/-- Applying the retained one-site coordinates at every site separates a positive chain into
its BNT-copy configurations and their simple-bond fibers.

Source: arXiv:1606.00608, density identity at line 999. -/
def verticalCopyChainEquiv (H : BNTFusionTensorClause M) (N : ℕ) :
    (Fin (N + 1) → Fin H.verticalRetainedDim) ≃ H.VerticalCopyChainIndex N :=
  (Equiv.piCongrRight fun _ : Fin (N + 1) ↦
    verticalCopyCoordinateEquiv H.bondDim H.multiplicity).trans piSigmaEquiv

/-- The inverse chain-coordinate equivalence acts independently at every site.

Source: arXiv:1606.00608, density identity at line 999. -/
@[simp] theorem verticalCopyChainEquiv_symm_apply
    (H : BNTFusionTensorClause M) (N : ℕ)
    (p : Fin (N + 1) → H.VerticalCopy) (x : H.VerticalCopyChainFiber p)
    (n : Fin (N + 1)) :
    (H.verticalCopyChainEquiv N).symm ⟨p, x⟩ n =
      (verticalCopyCoordinateEquiv H.bondDim H.multiplicity).symm ⟨p n, x n⟩ := by
  rfl

/-- The appended labels in reverse order, as required by the structurally recursive
left-associated fusion chain.

Source: arXiv:1606.00608, recursive fusion at lines 999--1010. -/
def reverseAppendedLabels (H : BNTFusionTensorClause M) :
    {N : ℕ} → (Fin (N + 1) → H.VerticalCopy) → List (Fin H.labelCount)
  | 0, _ => []
  | N + 1, p => (p (Fin.last (N + 1))).1 :: H.reverseAppendedLabels (Fin.init p)

/-- The diagonal entry of `μ⁽⊗ⁿ⁺¹⁾` selected by a BNT-copy configuration.

Source: arXiv:1606.00608, density identity at line 999. -/
def verticalMultiplicityChainWeight (H : BNTFusionTensorClause M) {N : ℕ}
    (p : Fin (N + 1) → H.VerticalCopy) : ℂ :=
  ∏ n : Fin (N + 1), H.weight (p n).1 (p n).2

private def piSnocEquiv {N : ℕ} {f : Fin (N + 1) → Type*} :
    ((i : Fin (N + 1)) → f i) ≃
      ((i : Fin N) → f i.castSucc) × f (Fin.last N) where
  toFun x := ⟨Fin.init x, x (Fin.last N)⟩
  invFun x := Fin.snoc x.1 x.2
  left_inv x := by simp
  right_inv x := by simp

/-- Restriction of a fixed-copy chain fibre to all sites except the last one. -/
private def verticalCopyChainFiberInit (H : BNTFusionTensorClause M) {N : ℕ}
    (p : Fin (N + 2) → H.VerticalCopy) (x : H.VerticalCopyChainFiber p) :
    H.VerticalCopyChainFiber (Fin.init p) :=
  fun i ↦ x i.castSucc

/-- The canonical left-associated product coordinates of a fixed BNT-copy chain.

Source: arXiv:1606.00608, recursive fusion at lines 999--1010. -/
def verticalCopyChainBondEquiv (H : BNTFusionTensorClause M) :
    {N : ℕ} → (p : Fin (N + 1) → H.VerticalCopy) →
      H.VerticalCopyChainFiber p ≃
        Fin (H.toBNTFusionCoisometryFamily.fusionChainBondDim
          (p 0).1 (H.reverseAppendedLabels p))
  | 0, p => {
      toFun := fun x ↦ x 0
      invFun := fun b i ↦
        _root_.cast (congrArg (fun j ↦ Fin (H.bondDim (p j).1))
          (Fin.eq_zero i).symm) b
      left_inv := by
        intro x
        funext i
        have hi : i = 0 := Fin.eq_zero i
        subst i
        rfl
      right_inv := by
        intro b
        rfl }
  | N + 1, p =>
      piSnocEquiv.trans <|
        (Equiv.prodCongr
          (H.verticalCopyChainBondEquiv (Fin.init p))
          (Equiv.refl (Fin (H.bondDim (p (Fin.last (N + 1))).1)))).trans
            finProdFinEquiv

/-- The one-site product-bond equivalence is evaluation at the unique site.

Source: arXiv:1606.00608, recursive fusion at lines 999--1010. -/
@[simp] theorem verticalCopyChainBondEquiv_zero_apply
    (H : BNTFusionTensorClause M) (p : Fin (0 + 1) → H.VerticalCopy)
    (x : H.VerticalCopyChainFiber p) :
    H.verticalCopyChainBondEquiv p x = x 0 := by
  rfl

/-- The sequential fusion coisometry for a fixed BNT-copy configuration, with its product
bond coordinates written as the corresponding chain fiber.

Source: arXiv:1606.00608, recursive fusion at lines 999--1010.  Its retained-row orientation
is documented in `docs/paper-gaps/cpsv16_figure11_fusion_coisometry.tex`. -/
def verticalCopyChainFusionCoisometry (H : BNTFusionTensorClause M) {N : ℕ}
    (p : Fin (N + 1) → H.VerticalCopy) :
    Matrix
      (H.toBNTFusionCoisometryFamily.FusionHistoryIndex
        (p 0).1 (H.reverseAppendedLabels p))
      (H.VerticalCopyChainFiber p) ℂ :=
  (H.toBNTFusionCoisometryFamily.sequentialFusionCoisometry
    (p 0).1 (H.reverseAppendedLabels p)).submatrix
      (Equiv.refl _ ) (H.verticalCopyChainBondEquiv p)

/-- The recursively fused terminal operator for a fixed BNT-copy configuration.

Source: arXiv:1606.00608, the operator `Q` at lines 999--1010. -/
def verticalCopyChainProjectorQ (H : BNTFusionTensorClause M) {N : ℕ}
    (p : Fin (N + 1) → H.VerticalCopy) :
    Matrix
      (H.toBNTFusionCoisometryFamily.FusionHistoryIndex
        (p 0).1 (H.reverseAppendedLabels p))
      (H.toBNTFusionCoisometryFamily.FusionHistoryIndex
        (p 0).1 (H.reverseAppendedLabels p)) ℂ :=
  H.toBNTFusionCoisometryFamily.recursiveProjectorQ
    (fun γ ↦ physTraceTransfer (verticalBNTMPO (H.tensor γ)))
    (p 0).1 (H.reverseAppendedLabels p)

/-- The line-999 density block in a fixed BNT-copy configuration.

The scalar is the selected diagonal entry of `μ⁽⊗ⁿ⁺¹⁾`.  The remaining factor is
the recursive terminal operator transported to the product bond space by the adjoint sequential
fusion coisometry.  Thus the source embedding `\tilde U` is the adjoint of Lean's retained-row
coisometry `W`, and the bond factor is `Wᴴ Q W`; the identities mentioned after line 999 act on
the complementary tensor factors.

Source: arXiv:1606.00608, density identity at line 999. -/
def topologicalDensityBlock (H : BNTFusionTensorClause M) {N : ℕ}
    (p : Fin (N + 1) → H.VerticalCopy) :
    Matrix (H.VerticalCopyChainFiber p) (H.VerticalCopyChainFiber p) ℂ :=
  H.verticalMultiplicityChainWeight p •
    ((H.verticalCopyChainFusionCoisometry p)ᴴ *
      H.verticalCopyChainProjectorQ p *
        H.verticalCopyChainFusionCoisometry p)

/-- The positive-length density operator in retained vertical coordinates, summed over every
initial label, every appended label, and every multiplicity coordinate.  Its chain length is
`N + 1`; the corresponding recursive appended-label list has length `N`.

Source: arXiv:1606.00608, density identity at line 999. -/
def topologicalDensityOperatorSucc (H : BNTFusionTensorClause M) (N : ℕ) :
    Matrix (Fin (N + 1) → Fin H.verticalRetainedDim)
      (Fin (N + 1) → Fin H.verticalRetainedDim) ℂ :=
  Matrix.reindex (H.verticalCopyChainEquiv N).symm
    (H.verticalCopyChainEquiv N).symm
      (Matrix.blockDiagonal' fun p ↦ H.topologicalDensityBlock p)

/-- The horizontal matrix obtained by fixing the two simple-bond coordinates of one vertical
BNT tensor.

Source: arXiv:1606.00608, Proposition 4.13, lines 943--951. -/
def verticalCopyChainLetter (H : BNTFusionTensorClause M) (p : H.VerticalCopy)
    (x y : Fin (H.bondDim p.1)) : Matrix (Fin D) (Fin D) ℂ :=
  fun a b ↦ H.tensor p.1 (finProdFinEquiv (a, b)) x y

/-- A product-tensor letter in canonical chain coordinates is the ordered product of the
horizontal matrices selected at the individual sites.

Source: arXiv:1606.00608, recursive fusion at lines 999--1010. -/
theorem fusionChainTensor_apply_verticalCopyChainBondEquiv
    (H : BNTFusionTensorClause M) :
    ∀ {N : ℕ} (p : Fin (N + 1) → H.VerticalCopy)
      (x y : H.VerticalCopyChainFiber p) (a b : Fin D),
      H.toBNTFusionCoisometryFamily.fusionChainTensor
          (p 0).1 (H.reverseAppendedLabels p) a b
          (H.verticalCopyChainBondEquiv p x)
          (H.verticalCopyChainBondEquiv p y) =
        (List.ofFn fun n : Fin (N + 1) ↦
          H.verticalCopyChainLetter (p n) (x n) (y n)).prod a b
  | 0, p, x, y, a, b => by
      rw [H.verticalCopyChainBondEquiv_zero_apply p x,
        H.verticalCopyChainBondEquiv_zero_apply p y]
      simp [BNTFusionCoisometryFamily.fusionChainTensor,
        reverseAppendedLabels,
        verticalCopyChainLetter, BNTFusionTensorClause.toBNTFusionCoisometryFamily,
        verticalBNTMPO]
  | N + 1, p, x, y, a, b => by
      let xInit : H.VerticalCopyChainFiber (Fin.init p) :=
        H.verticalCopyChainFiberInit p x
      let yInit : H.VerticalCopyChainFiber (Fin.init p) :=
        H.verticalCopyChainFiberInit p y
      change mulTensor
          (H.toBNTFusionCoisometryFamily.fusionChainTensor
            ((Fin.init p) 0).1 (H.reverseAppendedLabels (Fin.init p)))
          (verticalBNTMPO (H.tensor (p (Fin.last (N + 1))).1)) a b
          (finProdFinEquiv
            (H.verticalCopyChainBondEquiv (Fin.init p) xInit,
              x (Fin.last (N + 1))))
          (finProdFinEquiv
            (H.verticalCopyChainBondEquiv (Fin.init p) yInit,
              y (Fin.last (N + 1)))) = _
      rw [mulTensor_apply]
      simp only [Matrix.submatrix_apply, finProdFinEquiv_symm_apply,
        Matrix.sum_apply, Matrix.kroneckerMap_apply,
        MPSTensor.finProdFinEquiv_divNat, MPSTensor.finProdFinEquiv_modNat]
      rw [List.ofFn_succ']
      rw [List.prod_concat, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro j _
      rw [fusionChainTensor_apply_verticalCopyChainBondEquiv H
        (Fin.init p) xInit yInit a j]
      rfl

/-- In fixed copy coordinates, closing the physical legs of the product tensor gives the
trace of the ordered product of the selected horizontal matrices.

Source: arXiv:1606.00608, the terminal traces at lines 999--1010. -/
theorem physTraceTransfer_fusionChainTensor_reindex_apply
    (H : BNTFusionTensorClause M) {N : ℕ}
    (p : Fin (N + 1) → H.VerticalCopy) (x y : H.VerticalCopyChainFiber p) :
    Matrix.reindex (H.verticalCopyChainBondEquiv p).symm
        (H.verticalCopyChainBondEquiv p).symm
        (physTraceTransfer (H.toBNTFusionCoisometryFamily.fusionChainTensor
          (p 0).1 (H.reverseAppendedLabels p))) x y =
      Matrix.trace (List.ofFn fun n : Fin (N + 1) ↦
        H.verticalCopyChainLetter (p n) (x n) (y n)).prod := by
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, physTraceTransfer,
    Matrix.sum_apply, Matrix.trace, Matrix.diag]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Equiv.symm_symm]
  rw [H.fusionChainTensor_apply_verticalCopyChainBondEquiv p x y a a]

/-- The retained physical-coordinate tensor is the weighted vertical BNT direct sum.

Source: arXiv:1606.00608, Proposition 4.13, lines 943--951, and Appendix C.4,
lines 2020--2029.

**Local fix (rectangular vertical map):** The retained nonzero sectors may have smaller
dimension than the original space.  The map is therefore a rectangular coisometry, while the
separate exact reconstruction requires the discarded complement to be a zero sector.  See
`docs/paper-gaps/cpgsv17_vertical_isometry_zero_sector.tex`. -/
def retainedVerticalAssembledMPO (H : BNTFusionTensorClause M) :
    MPOTensor H.verticalRetainedDim D :=
  fun i j a b ↦ verticalAssembledTensor H.bondDim H.multiplicity H.weight H.tensor
    (finProdFinEquiv (a, b)) i j

/-- Conjugating the local physical coordinates by the retained-row vertical coisometry gives
the weighted BNT direct sum.

Source: arXiv:1606.00608, Proposition 4.13, lines 943--951. -/
theorem changePhysicalBasis_verticalCoisometry_eq_retainedVerticalAssembledMPO
    (H : BNTFusionTensorClause M) :
    changePhysicalBasis H.verticalCoisometry M =
      H.retainedVerticalAssembledMPO := by
  ext i j a b
  unfold changePhysicalBasis retainedVerticalAssembledMPO
  have hs : physicalSlice M a b = verticalTensor M (finProdFinEquiv (a, b)) := by
    ext s t
    simp [physicalSlice]
  rw [hs, H.forward]

/-- A retained one-site matrix entry inside one fixed BNT copy.

Source: arXiv:1606.00608, Proposition 4.13, lines 943--951. -/
theorem changePhysicalBasis_verticalCoisometry_copy_same
    (H : BNTFusionTensorClause M) (p : H.VerticalCopy)
    (x y : Fin (H.bondDim p.1)) :
    changePhysicalBasis H.verticalCoisometry M
        ((verticalCopyCoordinateEquiv H.bondDim H.multiplicity).symm ⟨p, x⟩)
        ((verticalCopyCoordinateEquiv H.bondDim H.multiplicity).symm ⟨p, y⟩) =
      H.weight p.1 p.2 • H.verticalCopyChainLetter p x y := by
  rw [H.changePhysicalBasis_verticalCoisometry_eq_retainedVerticalAssembledMPO]
  ext a b
  have hAssembled := congrFun (congrFun
    (verticalAssembledTensor_reindex_copyCoordinates H.bondDim H.multiplicity
      H.weight H.tensor (finProdFinEquiv (a, b)))
    ((verticalCopyCoordinateEquiv H.bondDim H.multiplicity).symm ⟨p, x⟩))
    ((verticalCopyCoordinateEquiv H.bondDim H.multiplicity).symm ⟨p, y⟩)
  simpa only [retainedVerticalAssembledMPO, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, Equiv.apply_symm_apply, Matrix.blockDiagonal'_apply_eq,
    Matrix.smul_apply, verticalCopyChainLetter] using hAssembled

/-- Retained one-site matrix entries between distinct BNT copies vanish.

Source: arXiv:1606.00608, Proposition 4.13, lines 943--951. -/
theorem changePhysicalBasis_verticalCoisometry_copy_ne
    (H : BNTFusionTensorClause M) (p q : H.VerticalCopy) (hpq : p ≠ q)
    (x : Fin (H.bondDim p.1)) (y : Fin (H.bondDim q.1)) :
    changePhysicalBasis H.verticalCoisometry M
        ((verticalCopyCoordinateEquiv H.bondDim H.multiplicity).symm ⟨p, x⟩)
        ((verticalCopyCoordinateEquiv H.bondDim H.multiplicity).symm ⟨q, y⟩) = 0 := by
  rw [H.changePhysicalBasis_verticalCoisometry_eq_retainedVerticalAssembledMPO]
  ext a b
  have hAssembled := congrFun (congrFun
    (verticalAssembledTensor_reindex_copyCoordinates H.bondDim H.multiplicity
      H.weight H.tensor (finProdFinEquiv (a, b)))
    ((verticalCopyCoordinateEquiv H.bondDim H.multiplicity).symm ⟨p, x⟩))
    ((verticalCopyCoordinateEquiv H.bondDim H.multiplicity).symm ⟨q, y⟩)
  simpa only [retainedVerticalAssembledMPO, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, Equiv.apply_symm_apply,
    Matrix.blockDiagonal'_apply_ne _ _ _ hpq, Pi.zero_apply,
    Matrix.zero_apply] using hAssembled

private theorem list_prod_smul_ofFn {n : Type*} [Fintype n]
    [DecidableEq n] {N : ℕ} (c : Fin N → ℂ)
    (A : Fin N → Matrix n n ℂ) :
    (List.ofFn fun i : Fin N ↦ c i • A i).prod =
      (∏ i : Fin N, c i) • (List.ofFn A).prod := by
  induction N with
  | zero => simp
  | succ N ih =>
      simp only [List.ofFn_succ, List.prod_cons, ih, Fin.prod_univ_succ,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      rw [mul_comm (c 0)]

/-- The recursive line-999 block has the fixed-copy closed-chain matrix entries.

Source: arXiv:1606.00608, density identity at line 999.  The orientation of
the fusion coisometry follows `docs/paper-gaps/cpsv16_figure11_fusion_coisometry.tex`.
-/
theorem topologicalDensityBlock_apply_eq_weight_mul_trace
    (H : BNTFusionTensorClause M) {N : ℕ}
    (p : Fin (N + 1) → H.VerticalCopy) (x y : H.VerticalCopyChainFiber p) :
    H.topologicalDensityBlock p x y =
      H.verticalMultiplicityChainWeight p *
        Matrix.trace (List.ofFn fun n : Fin (N + 1) ↦
          H.verticalCopyChainLetter (p n) (x n) (y n)).prod := by
  have hRec := congrFun (congrFun
    (physTraceTransfer_fusionChainTensor_eq_conjTranspose_mul_recursiveProjectorQ_mul
        H.toBNTFusionCoisometryFamily (p 0).1 (H.reverseAppendedLabels p))
    (H.verticalCopyChainBondEquiv p x))
    (H.verticalCopyChainBondEquiv p y)
  have hTrace := H.physTraceTransfer_fusionChainTensor_reindex_apply p x y
  unfold topologicalDensityBlock
  rw [Matrix.smul_apply]
  congr 1
  rw [← hTrace]
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
  rw [hRec]
  unfold verticalCopyChainFusionCoisometry verticalCopyChainProjectorQ
  simp only [BNTFusionTensorClause.toBNTFusionCoisometryFamily]
  rfl

/-- The diagonal retained-chain block of the transformed MPO is the recursive
line-999 density block.

Source: arXiv:1606.00608, density identity at line 999. -/
theorem mpo_changePhysicalBasis_verticalCoisometry_copy_block
    (H : BNTFusionTensorClause M) {N : ℕ}
    (p : Fin (N + 1) → H.VerticalCopy) (x y : H.VerticalCopyChainFiber p) :
    mpo (changePhysicalBasis H.verticalCoisometry M) (N + 1)
        ((H.verticalCopyChainEquiv N).symm ⟨p, x⟩)
        ((H.verticalCopyChainEquiv N).symm ⟨p, y⟩) =
      H.topologicalDensityBlock p x y := by
  rw [mpo_apply, mpoMatrixEntry, evalWord_ofFn]
  simp_rw [H.verticalCopyChainEquiv_symm_apply]
  simp_rw [H.changePhysicalBasis_verticalCoisometry_copy_same]
  rw [list_prod_smul_ofFn, Matrix.trace_smul,
    H.topologicalDensityBlock_apply_eq_weight_mul_trace]
  rfl

/-- Retained-chain entries between distinct sitewise BNT-copy configurations vanish.

Source: arXiv:1606.00608, the direct-sum density identity at line 999. -/
theorem mpo_changePhysicalBasis_verticalCoisometry_copy_ne
    (H : BNTFusionTensorClause M) {N : ℕ}
    (p q : Fin (N + 1) → H.VerticalCopy) (hpq : p ≠ q)
    (x : H.VerticalCopyChainFiber p) (y : H.VerticalCopyChainFiber q) :
    mpo (changePhysicalBasis H.verticalCoisometry M) (N + 1)
        ((H.verticalCopyChainEquiv N).symm ⟨p, x⟩)
        ((H.verticalCopyChainEquiv N).symm ⟨q, y⟩) = 0 := by
  rw [mpo_apply, mpoMatrixEntry, evalWord_ofFn]
  obtain ⟨n, hn⟩ := Function.ne_iff.mp hpq
  have hzero : (0 : Matrix (Fin D) (Fin D) ℂ) ∈
      List.ofFn fun i : Fin (N + 1) ↦
        changePhysicalBasis H.verticalCoisometry M
          ((H.verticalCopyChainEquiv N).symm ⟨p, x⟩ i)
          ((H.verticalCopyChainEquiv N).symm ⟨q, y⟩ i) :=
    List.mem_ofFn.mpr ⟨n, by
      rw [H.verticalCopyChainEquiv_symm_apply,
        H.verticalCopyChainEquiv_symm_apply]
      exact H.changePhysicalBasis_verticalCoisometry_copy_ne (p n) (q n) hn
        (x n) (y n)⟩
  rw [List.prod_eq_zero hzero, Matrix.trace_zero]

/-- In retained vertical coordinates, the positive-length MPO is the direct sum of all
recursive line-999 density blocks.

Source: arXiv:1606.00608, density identity at line 999.  The direct sum includes
every initial BNT label and every multiplicity coordinate at every site. -/
theorem mpo_changePhysicalBasis_verticalCoisometry_eq_topologicalDensityOperatorSucc
    (H : BNTFusionTensorClause M) (N : ℕ) :
    mpo (changePhysicalBasis H.verticalCoisometry M) (N + 1) =
      H.topologicalDensityOperatorSucc N := by
  ext s t
  obtain ⟨⟨p, x⟩, rfl⟩ := (H.verticalCopyChainEquiv N).symm.surjective s
  obtain ⟨⟨q, y⟩, rfl⟩ := (H.verticalCopyChainEquiv N).symm.surjective t
  unfold topologicalDensityOperatorSucc
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
    Equiv.apply_symm_apply]
  by_cases hpq : p = q
  · subst q
    rw [Matrix.blockDiagonal'_apply_eq,
      H.mpo_changePhysicalBasis_verticalCoisometry_copy_block]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hpq,
      H.mpo_changePhysicalBasis_verticalCoisometry_copy_ne p q hpq]

/-- Applying the adjoint rectangular vertical map reconstructs the original local tensor.

Source: arXiv:1606.00608, Proposition 4.13, lines 943--951.

**Local fix (rectangular vertical map):** This uses the exact reconstruction on the possible
zero-sector complement, rather than treating the retained-row coisometry as a square unitary.
See `docs/paper-gaps/cpgsv17_vertical_isometry_zero_sector.tex`. -/
theorem changePhysicalBasis_conjTranspose_verticalCoisometry_reconstruction
    (H : BNTFusionTensorClause M) :
    changePhysicalBasis H.verticalCoisometryᴴ
      (changePhysicalBasis H.verticalCoisometry M) = M := by
  rw [H.changePhysicalBasis_verticalCoisometry_eq_retainedVerticalAssembledMPO]
  ext i j a b
  unfold changePhysicalBasis retainedVerticalAssembledMPO physicalSlice
  rw [Matrix.conjTranspose_conjTranspose]
  have hReconstruction := congrFun (congrFun
    (H.reconstruction (finProdFinEquiv (a, b))) i) j
  simpa only [verticalTensor_finProdFinEquiv] using hReconstruction.symm

/-- The sitewise retained-row congruence sends the original positive-length density operator
to the all-label recursive density operator.

Source: arXiv:1606.00608, density identity at line 999. -/
theorem singleKrausMap_verticalCoisometry_mpo_eq_topologicalDensityOperatorSucc
    (H : BNTFusionTensorClause M) (N : ℕ) :
    singleKrausMap (sitewisePhysicalMatrix H.verticalCoisometry (N + 1))
        (mpo M (N + 1)) = H.topologicalDensityOperatorSucc N := by
  rw [singleKrausMap_sitewisePhysicalMatrix_mpo]
  exact H.mpo_changePhysicalBasis_verticalCoisometry_eq_topologicalDensityOperatorSucc N

/-- The adjoint sitewise vertical map reconstructs the original positive-length density
operator from the all-label recursive density operator.

Source: arXiv:1606.00608, Proposition 4.13, lines 943--951, Appendix C.4,
lines 2020--2029, and the density identity at line 999.

**Local fix (rectangular vertical map):** Exact adjoint reconstruction uses the retained-sector
reconstruction of Proposition 4.13, not a square-unitary identity.  See
`docs/paper-gaps/cpgsv17_vertical_isometry_zero_sector.tex`. -/
theorem singleKrausMap_conjTranspose_verticalCoisometry_topologicalDensityOperatorSucc_eq_mpo
    (H : BNTFusionTensorClause M) (N : ℕ) :
    singleKrausMap (sitewisePhysicalMatrix H.verticalCoisometryᴴ (N + 1))
        (H.topologicalDensityOperatorSucc N) = mpo M (N + 1) := by
  rw [← H.singleKrausMap_verticalCoisometry_mpo_eq_topologicalDensityOperatorSucc N,
    singleKrausMap_sitewisePhysicalMatrix_mpo H.verticalCoisometry M (N + 1),
    singleKrausMap_sitewisePhysicalMatrix_mpo H.verticalCoisometryᴴ
      (changePhysicalBasis H.verticalCoisometry M) (N + 1),
    H.changePhysicalBasis_conjTranspose_verticalCoisometry_reconstruction]

/-- The complete all-initial-label line-999 density decomposition carried by one chosen BNT
fusion clause.  It asserts the retained-row congruence and its exact adjoint reconstruction
at every positive chain length, written as `N + 1`.

Source: arXiv:1606.00608, density identity at line 999.  In Lean the sequential fusion
map `W` is a retained-row coisometry, so the source embedding `\tilde U` is `Wᴴ` and the bond
factor is `Wᴴ Q W`.  The identities mentioned after line 999 act on the complementary tensor
factors in this block formula.  This predicate makes no assertion about the commutator at
line 1001 or its spectral and Gibbs consequences.

**Local fix (rectangular vertical map):** The reverse equality uses exact reconstruction from
the retained nonzero sectors of Proposition 4.13 and Appendix C.4, lines 2020--2029.  See
`docs/paper-gaps/cpgsv17_vertical_isometry_zero_sector.tex`. -/
def HasTopologicalDensityDecomposition (H : BNTFusionTensorClause M) : Prop :=
  ∀ N : ℕ,
    singleKrausMap (sitewisePhysicalMatrix H.verticalCoisometry (N + 1))
        (mpo M (N + 1)) = H.topologicalDensityOperatorSucc N ∧
      singleKrausMap (sitewisePhysicalMatrix H.verticalCoisometryᴴ (N + 1))
        (H.topologicalDensityOperatorSucc N) = mpo M (N + 1)

/-- A chosen BNT fusion clause supplies the complete positive-length line-999 density
decomposition, with no additional compatibility hypothesis.

Source: arXiv:1606.00608, density identity at line 999. -/
theorem hasTopologicalDensityDecomposition (H : BNTFusionTensorClause M) :
    H.HasTopologicalDensityDecomposition := by
  intro N
  exact ⟨H.singleKrausMap_verticalCoisometry_mpo_eq_topologicalDensityOperatorSucc N,
    H.singleKrausMap_conjTranspose_verticalCoisometry_topologicalDensityOperatorSucc_eq_mpo
      N⟩

end MPOTensor.BNTFusionTensorClause

namespace MPOTensor

/-- **Line-999 density decomposition for an RFP MPDO.**

A horizontal-canonical MPDO satisfying the source renormalization fixed-point condition
admits one BNT fusion clause whose same multiplicities, positive weights, rectangular vertical
coisometry, fusion histories, and terminal operators give the all-initial-label density
decomposition at every positive chain length.  No caller-supplied compatibility hypothesis is
required.

Source: arXiv:1606.00608, Theorem 4.14 and the density identity at line 999.  This theorem
stops before the commutator at line 1001 and makes no spectral or Gibbs-state assertion.

**Local fix (rectangular vertical map):** The existentially chosen vertical map is a
retained-row coisometry, and its reverse density equality uses exact retained-sector
reconstruction from Proposition 4.13 and Appendix C.4, lines 2020--2029.  See
`docs/paper-gaps/cpgsv17_vertical_isometry_zero_sector.tex`. -/
theorem exists_topologicalDensityDecomposition_of_isRFPViaTS
    (M : MPOTensor d D) (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M)
    (hRFP : IsRFPViaTS M) :
    ∃ H : BNTFusionTensorClause M, H.HasTopologicalDensityDecomposition := by
  obtain ⟨H⟩ := HasBNTFusionTensorClause.of_isRFPViaTS M hHorizontal hM hRFP
  exact ⟨H, H.hasTopologicalDensityDecomposition⟩

end MPOTensor
