/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.KroneckerFactorPositivity
import TNLean.MPS.MPDO.PhysicalSectorChainDecomposition
import TNLean.MPS.MPDO.PhysicalSectorPositiveBond
import TNLean.MPS.MPDO.CommutingForm
import TNLean.MPS.MPDO.CommutingBondEtaCyclicCore
import TNLean.MPS.MPDO.SitewisePhysicalMatrix

open scoped ComplexOrder Matrix

/-!
# Product realization from physical-sector coordinates

This file proves the all-length cyclic contraction underlying the product
form of a matrix product density operator with a physical-sector
factorization.  No positivity, normalization, area-law, or zero-correlation
hypothesis is imposed.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, Proposition C.8, lines 1581--1593
-/

open scoped Matrix BigOperators Kronecker

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

/-- The eta ordering `(right, left)` of a physical sector, encoded by the
existing finite sector coordinates.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNK2`, lines
1581--1589. -/
noncomputable def etaSectorFinEquiv
    (F : PhysicalSectorFactorization K) :
    Matrix.EtaSiteIndex F.sectorCount F.leftDim F.rightDim ≃
      Fin (Fintype.card (SectorSiteIndex F)) :=
  (Equiv.sigmaCongrRight fun _ ↦ Equiv.prodComm _ _).trans F.sectorFinEquiv.symm

/-- The pointwise finite encoding of the transformed physical chain. -/
noncomputable def physicalConfigEquiv
    (F : PhysicalSectorFactorization K) (N : ℕ) :
    (Fin N → Fin d) ≃ (Fin N → Fin (Fintype.card (SectorSiteIndex F))) :=
  Equiv.arrowCongr (Equiv.refl (Fin N)) F.physicalFinEquiv

/-- The finite sector-coordinate chain is the transformed physical chain,
followed by the sector decomposition already used in the all-length chain
decomposition. -/
noncomputable def sectorCoordinateChainEquiv
    (F : PhysicalSectorFactorization K) (N : ℕ) :
    (Fin N → Fin (Fintype.card (SectorSiteIndex F))) ≃ SectorChainIndex F N :=
  (F.physicalConfigEquiv N).symm.trans (F.sectorChainEquiv N)

@[simp] theorem sectorCoordinateChainEquiv_symm_apply
    (F : PhysicalSectorFactorization K) (N : ℕ)
    (k : Fin N → Fin F.sectorCount) (x : F.SectorChainFiber k)
    (n : Fin N) :
    (F.sectorCoordinateChainEquiv N).symm ⟨k, x⟩ n =
      F.sectorFinEquiv.symm ⟨k n, x n⟩ := by
  simp [sectorCoordinateChainEquiv, physicalConfigEquiv,
    physicalFinEquiv, sectorChainEquiv]

/-- Encoding the transformed one-site physical indices by `Fin` commutes with
forming the periodic MPO. -/
theorem mpo_sectorCoordinateTensor_eq_reindex_conjugatePhysical
    (F : PhysicalSectorFactorization K) (N : ℕ) :
    mpo F.sectorCoordinateTensor N =
      Matrix.reindex (F.physicalConfigEquiv N) (F.physicalConfigEquiv N)
        (mpo (conjugatePhysical K F.physicalIsometry) N) := by
  ext s t
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, mpo_apply,
    mpoMatrixEntry, MPOTensor.evalWord_ofFn]
  congr 1

/-- In finite sector coordinates, the full MPO is the direct sum from the
all-length physical-sector chain decomposition.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNK2`, lines
1581--1588. -/
theorem reindex_mpo_sectorCoordinateTensor_eq_blockDiagonal
    (F : PhysicalSectorFactorization K) {N : ℕ} [NeZero N] :
    Matrix.reindex (F.sectorCoordinateChainEquiv N)
        (F.sectorCoordinateChainEquiv N) (mpo F.sectorCoordinateTensor N) =
      Matrix.blockDiagonal' fun k ↦ F.cyclicNeighboringProduct k := by
  ext s t
  have h := congrFun (congrFun
    (F.mpo_reindex_sectorChainEquiv_eq_blockDiagonal (N := N)) s) t
  rw [F.mpo_sectorCoordinateTensor_eq_reindex_conjugatePhysical N]
  simpa [sectorCoordinateChainEquiv, Matrix.reindex_apply] using h

/-- Regroup a fixed sector configuration from site factors
`(L_n,R_n)` to cyclic edge factors `(R_n,L_(n+1))`.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNK2`, lines
1586--1589. -/
def cyclicEdgeEquiv (F : PhysicalSectorFactorization K) {N : ℕ} [NeZero N]
    (k : Fin N → Fin F.sectorCount) :
    ((n : Fin N) → SectorIndex F (k n)) ≃
      ((n : Fin N) → NeighborIndex F (k n) (k (n + 1))) :=
  (Equiv.arrowProdEquivProdArrow _ _ _).trans <|
    (Equiv.prodComm _ _).trans <|
      (Equiv.prodCongr (Equiv.refl _)
        (Equiv.piCongrLeft
          (fun n : Fin N ↦ Fin (F.leftDim (k n))) (finRotate N)).symm).trans <|
        (Equiv.arrowProdEquivProdArrow _ _ _).symm |>.trans <|
          Equiv.piCongrRight fun n ↦
            Equiv.prodCongr (Equiv.refl _)
              (finCongr (congrArg F.leftDim
                (congrArg k (finRotate_apply n))))

@[simp] theorem cyclicEdgeEquiv_apply
    (F : PhysicalSectorFactorization K) {N : ℕ} [NeZero N]
    (k : Fin N → Fin F.sectorCount)
    (x : (n : Fin N) → SectorIndex F (k n)) (n : Fin N) :
    F.cyclicEdgeEquiv k x n = ((x n).2, (x (n + 1)).1) := by
  apply Prod.ext
  · rfl
  · apply Fin.ext
    change ((x (finRotate N n)).1 : ℕ) = ((x (n + 1)).1 : ℕ)
    rw [finRotate_apply]

@[simp] theorem cyclicEdgeEquiv_symm_edge
    (F : PhysicalSectorFactorization K) {N : ℕ} [NeZero N]
    (k : Fin N → Fin F.sectorCount)
    (x : (n : Fin N) → NeighborIndex F (k n) (k (n + 1)))
    (n : Fin N) :
    (((F.cyclicEdgeEquiv k).symm x n).2,
        ((F.cyclicEdgeEquiv k).symm x (n + 1)).1) = x n := by
  have h := congrFun ((F.cyclicEdgeEquiv k).apply_symm_apply x) n
  simpa only [cyclicEdgeEquiv_apply] using h

/-- Under cyclic edge coordinates, a fixed-sector neighboring product is
the ordinary tensor-product matrix whose entries are products over edges.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNK2`, lines
1586--1589. -/
private theorem reindex_cyclicNeighboringProduct_cyclicEdgeEquiv
    (F : PhysicalSectorFactorization K) {N : ℕ} [NeZero N]
    (k : Fin N → Fin F.sectorCount) :
    Matrix.reindex (F.cyclicEdgeEquiv k) (F.cyclicEdgeEquiv k)
        (F.cyclicNeighboringProduct k) =
      fun x y ↦ ∏ n : Fin N,
        F.neighboringOperator (k n) (k (n + 1)) (x n) (y n) := by
  ext x y
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    cyclicNeighboringProduct]
  apply Finset.prod_congr rfl
  intro n _
  have hx := congrFun ((F.cyclicEdgeEquiv k).apply_symm_apply x) n
  have hy := congrFun ((F.cyclicEdgeEquiv k).apply_symm_apply y) n
  simpa only [cyclicEdgeEquiv_apply] using
    congrArg₂ (F.neighboringOperator (k n) (k (n + 1))) hx hy

/-- The complete sector-coordinate chain, regrouped as a direct sum over
sector configurations with one neighboring factor on every cyclic edge.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNK2`, lines
1581--1589. -/
private noncomputable def sectorEdgeChainEquiv
    (F : PhysicalSectorFactorization K) (N : ℕ) [NeZero N] :
    (Fin N → Fin (Fintype.card (SectorSiteIndex F))) ≃
      Σ k : Fin N → Fin F.sectorCount,
        (n : Fin N) → NeighborIndex F (k n) (k (n + 1)) :=
  (F.sectorCoordinateChainEquiv N).trans <|
    Equiv.sigmaCongrRight fun k ↦ F.cyclicEdgeEquiv k

@[simp] private theorem sectorEdgeChainEquiv_symm_apply
    (F : PhysicalSectorFactorization K) (N : ℕ) [NeZero N]
    (k : Fin N → Fin F.sectorCount)
    (x : (n : Fin N) → NeighborIndex F (k n) (k (n + 1)))
    (n : Fin N) :
    (F.sectorEdgeChainEquiv N).symm ⟨k, x⟩ n =
      F.sectorFinEquiv.symm
        ⟨k n, (F.cyclicEdgeEquiv k).symm x n⟩ := by
  simp [sectorEdgeChainEquiv, sectorCoordinateChainEquiv,
    physicalConfigEquiv, physicalFinEquiv, sectorChainEquiv,
    Equiv.sigmaCongrRight_symm, Equiv.sigmaCongrRight_apply]

/-- The physical-sector cyclic coordinates are the eta cyclic coordinates
after swapping the one-site `(left, right)` ordering. -/
private theorem etaCyclicEdgeEquiv_eq_sectorEdgeChainEquiv
    (F : PhysicalSectorFactorization K) {N : ℕ} [NeZero N] :
    Matrix.etaCyclicEdgeEquiv F.leftDim F.rightDim F.etaSectorFinEquiv =
      F.sectorEdgeChainEquiv N := by
  have hinv :
      (Matrix.etaCyclicEdgeEquiv F.leftDim F.rightDim
        F.etaSectorFinEquiv).symm = (F.sectorEdgeChainEquiv N).symm := by
    apply Equiv.ext
    rintro ⟨k, x⟩
    funext n
    rw [Matrix.etaCyclicEdgeEquiv_symm_apply,
      F.sectorEdgeChainEquiv_symm_apply]
    have hswap :
        (fun m ↦
          (((Matrix.etaFixedSectorCyclicEdgeEquiv F.leftDim F.rightDim k).symm
              x m).2,
            ((Matrix.etaFixedSectorCyclicEdgeEquiv F.leftDim F.rightDim k).symm
              x m).1)) =
          (F.cyclicEdgeEquiv k).symm x := by
      apply (F.cyclicEdgeEquiv k).injective
      funext m
      rw [F.cyclicEdgeEquiv_apply]
      rw [Equiv.apply_symm_apply]
      exact Matrix.etaFixedSectorCyclicEdgeEquiv_symm_edge
        F.leftDim F.rightDim k x m
    exact congrArg (fun z ↦ F.sectorFinEquiv.symm ⟨k n, z⟩)
      (congrFun hswap n)
  have h := congrArg (fun e ↦ e.symm) hinv
  simpa using h

/-- Under complete cyclic-edge coordinates, the sector-coordinate MPO is
block diagonal and each fixed-sector block is the product of its edge
matrix entries.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNK2`, lines
1581--1589. -/
private theorem reindex_mpo_sectorCoordinateTensor_sectorEdgeChainEquiv
    (F : PhysicalSectorFactorization K) {N : ℕ} [NeZero N] :
    Matrix.reindex (F.sectorEdgeChainEquiv N) (F.sectorEdgeChainEquiv N)
        (mpo F.sectorCoordinateTensor N) =
      Matrix.blockDiagonal' fun k ↦
        fun x y ↦ ∏ n : Fin N,
          F.neighboringOperator (k n) (k (n + 1)) (x n) (y n) := by
  change Matrix.reindex
      ((F.sectorCoordinateChainEquiv N).trans
        (Equiv.sigmaCongrRight fun k ↦ F.cyclicEdgeEquiv k))
      ((F.sectorCoordinateChainEquiv N).trans
        (Equiv.sigmaCongrRight fun k ↦ F.cyclicEdgeEquiv k)) _ = _
  ext ⟨k, x⟩ ⟨h, y⟩
  have hfull := congrFun (congrFun
    F.reindex_mpo_sectorCoordinateTensor_eq_blockDiagonal
      ⟨k, (F.cyclicEdgeEquiv k).symm x⟩)
      ⟨h, (F.cyclicEdgeEquiv h).symm y⟩
  change _ = Matrix.blockDiagonal' (fun q ↦ F.cyclicNeighboringProduct q)
    ⟨k, (F.cyclicEdgeEquiv k).symm x⟩
    ⟨h, (F.cyclicEdgeEquiv h).symm y⟩ at hfull
  change Matrix.reindex (F.sectorCoordinateChainEquiv N)
      (F.sectorCoordinateChainEquiv N) (mpo F.sectorCoordinateTensor N)
        ⟨k, (F.cyclicEdgeEquiv k).symm x⟩
        ⟨h, (F.cyclicEdgeEquiv h).symm y⟩ = _
  rw [hfull]
  by_cases hkh : k = h
  · subst h
    rw [Matrix.blockDiagonal'_apply_eq, Matrix.blockDiagonal'_apply_eq]
    exact congrFun (congrFun
      (F.reindex_cyclicNeighboringProduct_cyclicEdgeEquiv k) x) y
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hkh,
      Matrix.blockDiagonal'_apply_ne _ _ _ hkh]

/-- Positivity of all neighbouring blocks makes every positive-length
sector-coordinate periodic operator positive semidefinite. -/
theorem mpo_sectorCoordinateTensor_posSemidef
    (F : PhysicalSectorFactorization K) {N : ℕ} [NeZero N]
    (hpos : ∀ q h, (F.neighboringOperator q h).PosSemidef) :
    (mpo F.sectorCoordinateTensor N).PosSemidef := by
  classical
  rw [← Matrix.posSemidef_submatrix_equiv
    (M := mpo F.sectorCoordinateTensor N) (F.sectorEdgeChainEquiv N).symm]
  change (Matrix.reindex (F.sectorEdgeChainEquiv N) (F.sectorEdgeChainEquiv N)
    (mpo F.sectorCoordinateTensor N)).PosSemidef
  rw [F.reindex_mpo_sectorCoordinateTensor_sectorEdgeChainEquiv]
  apply Matrix.PosSemidef.blockDiagonal'
  intro k
  have heq :
      (fun x y ↦ ∏ n : Fin N,
        F.neighboringOperator (k n) (k (n + 1)) (x n) (y n)) =
        Matrix.finKronecker (fun n : Fin N ↦
          F.neighboringOperator (k n) (k (n + 1))) := by
    ext x y
    simp [Matrix.finKronecker_apply]
  rw [heq]
  exact Matrix.finKronecker_posSemidef _ fun n ↦ hpos _ _

/-- Positivity of every neighbouring sector operator makes the original tensor an MPDO.  The
sector-coordinate operators are positive by their cyclic product decomposition, and the
physical isometry transports positivity back to the original physical space.

Source: arXiv:1606.00608, Appendix C.2, equations `AppUkU=rl` and `Appetakhetc`,
lines 1383--1450. -/
theorem isMPDO_of_neighboringOperator_pos
    (F : PhysicalSectorFactorization K)
    (hpos : ∀ q h, (F.neighboringOperator q h).PosSemidef) : IsMPDO K := by
  apply isMPDO_of_changePhysicalBasis_isMPDO_of_isometry
    F.physicalCoordinateMatrix F.physicalCoordinateMatrix_isometry K
  rw [← F.sectorCoordinateTensor_eq_changePhysicalBasis]
  intro N hN
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  exact F.mpo_sectorCoordinateTensor_posSemidef hpos

/-- The sector-coordinate bond indexed by two-site configurations. -/
noncomputable def sectorBond (F : PhysicalSectorFactorization K) :
    Matrix
      (Fin 2 → Fin (Fintype.card (SectorSiteIndex F)))
      (Fin 2 → Fin (Fintype.card (SectorSiteIndex F))) ℂ :=
  Matrix.reindex
    (finTwoArrowEquiv (Fin (Fintype.card (SectorSiteIndex F)))).symm
    (finTwoArrowEquiv (Fin (Fintype.card (SectorSiteIndex F)))).symm
    F.sectorCoordinateBond

@[simp] private theorem twoSiteGlobalRegroupEquiv_twoSiteSectorEmbedding
    (F : PhysicalSectorFactorization K) (k h : Fin F.sectorCount)
    (x : SectorIndex F k × SectorIndex F h) :
    F.twoSiteGlobalRegroupEquiv (F.twoSiteSectorEmbedding k h x) =
      ⟨(k, h), F.twoSiteRegroupEquiv k h x⟩ := by
  apply F.twoSiteGlobalRegroupEquiv.symm.injective
  rw [Equiv.symm_apply_apply, twoSiteGlobalRegroupEquiv_symm_apply]
  rfl

/-- In eta pair coordinates, the physical-sector bond has the neighboring
operator decomposition required by cyclic eta transport.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNK2`, lines
1581--1589; Beigi, J. Phys. A 45 (2012) 025306, Section III. -/
theorem sectorCoordinateBond_etaPair_decomposition
    (F : PhysicalSectorFactorization K) :
    Matrix.reindex (Matrix.etaPairSpatialBlockEquiv F.etaSectorFinEquiv).symm
        (Matrix.etaPairSpatialBlockEquiv F.etaSectorFinEquiv).symm
        F.sectorCoordinateBond =
      Matrix.blockDiagonal' fun qh : Fin F.sectorCount × Fin F.sectorCount ↦
        ((1 : Matrix (Fin (F.leftDim qh.1)) (Fin (F.leftDim qh.1)) ℂ) ⊗ₖ
          F.neighboringOperator qh.1 qh.2) ⊗ₖ
            (1 : Matrix (Fin (F.rightDim qh.2)) (Fin (F.rightDim qh.2)) ℂ) := by
  ext ⟨⟨q, h⟩, ⟨⟨lq, rq, lh⟩, rh⟩⟩
    ⟨⟨q', h'⟩, ⟨⟨lq', rq', lh'⟩, rh'⟩⟩
  change F.sectorCoordinateBond
      (F.sectorFinEquiv.symm ⟨q, (lq, rq)⟩,
        F.sectorFinEquiv.symm ⟨h, (lh, rh)⟩)
      (F.sectorFinEquiv.symm ⟨q', (lq', rq')⟩,
        F.sectorFinEquiv.symm ⟨h', (lh', rh')⟩) = _
  have hx : F.twoSiteGlobalRegroupEquiv
      (F.sectorFinEquiv.symm ⟨q, (lq, rq)⟩,
        F.sectorFinEquiv.symm ⟨h, (lh, rh)⟩) =
      ⟨(q, h), ((lq, rh), (rq, lh))⟩ := by
    change F.twoSiteGlobalRegroupEquiv
        (F.twoSiteSectorEmbedding q h ((lq, rq), (lh, rh))) = _
    exact F.twoSiteGlobalRegroupEquiv_twoSiteSectorEmbedding q h _
  have hy : F.twoSiteGlobalRegroupEquiv
      (F.sectorFinEquiv.symm ⟨q', (lq', rq')⟩,
        F.sectorFinEquiv.symm ⟨h', (lh', rh')⟩) =
      ⟨(q', h'), ((lq', rh'), (rq', lh'))⟩ := by
    change F.twoSiteGlobalRegroupEquiv
        (F.twoSiteSectorEmbedding q' h' ((lq', rq'), (lh', rh'))) = _
    exact F.twoSiteGlobalRegroupEquiv_twoSiteSectorEmbedding q' h' _
  simp only [sectorCoordinateBond, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm]
  rw [hx, hy]
  by_cases hp : (q, h) = (q', h')
  · have hq : q = q' := congrArg Prod.fst hp
    have hh : h = h' := congrArg Prod.snd hp
    subst q'
    subst h'
    rw [Matrix.blockDiagonal'_apply_eq, Matrix.blockDiagonal'_apply_eq]
    simp only [Matrix.kroneckerMap_apply, Matrix.one_apply]
    by_cases hl : lq = lq' <;> by_cases hr : rh = rh' <;> simp [hl, hr]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hp,
      Matrix.blockDiagonal'_apply_ne _ _ _ hp]

/-- For every length at least three, the sector-coordinate MPO is exactly
the ordered product of the translated sector bonds. -/
theorem mpo_sectorCoordinateTensor_eq_product_sectorBond
    (F : PhysicalSectorFactorization K) {N : ℕ} [NeZero N]
    (hN : 3 ≤ N) :
    mpo F.sectorCoordinateTensor N =
      (List.ofFn fun i : Fin N ↦
        embedLocalOperator
          (d := Fintype.card (SectorSiteIndex F)) 2 N (by omega) i
            F.sectorBond).prod := by
  have hcyclic := reindex_product_embedLocalOperator_of_etaPair_decomposition
    (d := Fintype.card (SectorSiteIndex F)) (N := N) (by omega)
    F.leftDim F.rightDim F.etaSectorFinEquiv F.neighboringOperator
    F.sectorCoordinateBond F.sectorCoordinateBond_etaPair_decomposition
  apply (Matrix.reindex (F.sectorEdgeChainEquiv N)
    (F.sectorEdgeChainEquiv N)).injective
  rw [F.reindex_mpo_sectorCoordinateTensor_sectorEdgeChainEquiv]
  simpa only [sectorBond, F.etaCyclicEdgeEquiv_eq_sectorEdgeChainEquiv]
    using hcyclic.symm

end MPOTensor.PhysicalSectorFactorization
