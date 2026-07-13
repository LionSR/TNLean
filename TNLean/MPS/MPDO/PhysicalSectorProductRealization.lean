/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorChainDecomposition
import TNLean.MPS.MPDO.PhysicalSectorBondCommutativity

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

/-- The pointwise finite encoding of the transformed physical chain. -/
private noncomputable def physicalConfigEquiv
    (F : PhysicalSectorFactorization K) (N : ℕ) :
    (Fin N → Fin d) ≃ (Fin N → Fin (Fintype.card (SectorSiteIndex F))) :=
  Equiv.arrowCongr (Equiv.refl (Fin N)) F.physicalFinEquiv

/-- The finite sector-coordinate chain is the transformed physical chain,
followed by the sector decomposition already used in the all-length chain
decomposition. -/
private noncomputable def sectorCoordinateChainEquiv
    (F : PhysicalSectorFactorization K) (N : ℕ) :
    (Fin N → Fin (Fintype.card (SectorSiteIndex F))) ≃ SectorChainIndex F N :=
  (F.physicalConfigEquiv N).symm.trans (F.sectorChainEquiv N)

/-- Encoding the transformed one-site physical indices by `Fin` commutes with
forming the periodic MPO. -/
private theorem mpo_sectorCoordinateTensor_eq_reindex_conjugatePhysical
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
private theorem reindex_mpo_sectorCoordinateTensor_eq_blockDiagonal
    (F : PhysicalSectorFactorization K) {N : ℕ} [NeZero N] :
    Matrix.reindex (F.sectorCoordinateChainEquiv N)
        (F.sectorCoordinateChainEquiv N) (mpo F.sectorCoordinateTensor N) =
      Matrix.blockDiagonal' fun k ↦ F.cyclicNeighboringProduct k := by
  ext s t
  have h := congrFun (congrFun
    (F.mpo_reindex_sectorChainEquiv_eq_blockDiagonal (N := N)) s) t
  rw [F.mpo_sectorCoordinateTensor_eq_reindex_conjugatePhysical N]
  simpa [sectorCoordinateChainEquiv, Matrix.reindex_apply] using h

private def piProdEquiv
    {ι : Type*} {A B : ι → Type*} :
    ((i : ι) → A i × B i) ≃ ((i : ι) → A i) × ((i : ι) → B i) where
  toFun x := (fun i ↦ (x i).1, fun i ↦ (x i).2)
  invFun x i := (x.1 i, x.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Regroup a fixed sector configuration from site factors
`(L_n,R_n)` to cyclic edge factors `(R_n,L_(n+1))`.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNK2`, lines
1586--1589. -/
private def cyclicEdgeEquiv (F : PhysicalSectorFactorization K) {N : ℕ} [NeZero N]
    (k : Fin N → Fin F.sectorCount) :
    ((n : Fin N) → SectorIndex F (k n)) ≃
      ((n : Fin N) → NeighborIndex F (k n) (k (n + 1))) :=
  piProdEquiv.trans <|
    (Equiv.prodComm _ _).trans <|
      (Equiv.prodCongr (Equiv.refl _)
        (Equiv.piCongrLeft
          (fun n : Fin N ↦ Fin (F.leftDim (k n))) (finRotate N)).symm).trans <|
        piProdEquiv.symm |>.trans <|
          Equiv.piCongrRight fun n ↦
            Equiv.prodCongr (Equiv.refl _)
              (finCongr (congrArg F.leftDim
                (congrArg k (finRotate_apply n))))

@[simp] private theorem cyclicEdgeEquiv_apply
    (F : PhysicalSectorFactorization K) {N : ℕ} [NeZero N]
    (k : Fin N → Fin F.sectorCount)
    (x : (n : Fin N) → SectorIndex F (k n)) (n : Fin N) :
    F.cyclicEdgeEquiv k x n = ((x n).2, (x (n + 1)).1) := by
  apply Prod.ext
  · rfl
  · apply Fin.ext
    change ((x (finRotate N n)).1 : ℕ) = ((x (n + 1)).1 : ℕ)
    rw [finRotate_apply]

@[simp] private theorem cyclicEdgeEquiv_symm_edge
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
    physicalConfigEquiv, physicalFinEquiv, sectorChainEquiv]
  rfl

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

/-- The product on a chosen set of cyclic edges in a fixed sector
configuration.  Edges outside the set carry the identity matrix.

This is the scalar-entry form of a partial tensor product. -/
private noncomputable def edgePartialProduct
    (F : PhysicalSectorFactorization K) {N : ℕ} [NeZero N]
    (k : Fin N → Fin F.sectorCount) (s : Finset (Fin N)) :
    Matrix ((n : Fin N) → NeighborIndex F (k n) (k (n + 1)))
      ((n : Fin N) → NeighborIndex F (k n) (k (n + 1))) ℂ :=
  fun x y ↦ ∏ n : Fin N,
    if n ∈ s then
      F.neighboringOperator (k n) (k (n + 1)) (x n) (y n)
    else if x n = y n then 1 else 0

@[simp] private theorem edgePartialProduct_empty
    (F : PhysicalSectorFactorization K) {N : ℕ} [NeZero N]
    (k : Fin N → Fin F.sectorCount) :
    F.edgePartialProduct k ∅ = 1 := by
  ext x y
  simp only [edgePartialProduct, Finset.notMem_empty, ↓reduceIte,
    Matrix.one_apply]
  by_cases hxy : x = y
  · subst y
    simp
  · obtain ⟨n, hn⟩ := Function.ne_iff.mp hxy
    rw [Finset.prod_eq_zero (Finset.mem_univ n)]
    · simp [hxy]
    · simp [hn]

@[simp] private theorem edgePartialProduct_univ
    (F : PhysicalSectorFactorization K) {N : ℕ} [NeZero N]
    (k : Fin N → Fin F.sectorCount) :
    F.edgePartialProduct k Finset.univ =
      fun x y ↦ ∏ n : Fin N,
        F.neighboringOperator (k n) (k (n + 1)) (x n) (y n) := by
  ext x y
  simp [edgePartialProduct]

/-- Multiplying by a new single-edge factor adjoins that edge to the partial
tensor product. -/
private theorem edgePartialProduct_mul_singleton
    (F : PhysicalSectorFactorization K) {N : ℕ} [NeZero N]
    (k : Fin N → Fin F.sectorCount) (s : Finset (Fin N))
    (i : Fin N) (hi : i ∉ s) :
    F.edgePartialProduct k s * F.edgePartialProduct k {i} =
      F.edgePartialProduct k (insert i s) := by
  classical
  ext x y
  simp only [Matrix.mul_apply, edgePartialProduct]
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.piFinset_univ]
  rw [← Finset.prod_univ_sum
    (fun n : Fin N ↦
      (Finset.univ : Finset (NeighborIndex F (k n) (k (n + 1)))))
    (fun n z ↦
      (if n ∈ s then
        F.neighboringOperator (k n) (k (n + 1)) (x n) z
      else if x n = z then 1 else 0) *
      (if n ∈ ({i} : Finset (Fin N)) then
        F.neighboringOperator (k n) (k (n + 1)) z (y n)
      else if z = y n then 1 else 0))]
  apply Finset.prod_congr rfl
  intro n _
  by_cases hni : n = i
  · subst n
    simp [hi]
  · by_cases hns : n ∈ s
    · simp [hni, hns]
    · by_cases hxy : x n = y n
      · simp [hni, hns, hxy]
      · simp [hni, hns, hxy]

/-- Multiplying a partial tensor product on the left by a new single-edge
factor adjoins that edge. -/
private theorem edgePartialProduct_singleton_mul
    (F : PhysicalSectorFactorization K) {N : ℕ} [NeZero N]
    (k : Fin N → Fin F.sectorCount) (s : Finset (Fin N))
    (i : Fin N) (hi : i ∉ s) :
    F.edgePartialProduct k {i} * F.edgePartialProduct k s =
      F.edgePartialProduct k (insert i s) := by
  classical
  ext x y
  simp only [Matrix.mul_apply, edgePartialProduct]
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.piFinset_univ]
  rw [← Finset.prod_univ_sum
    (fun n : Fin N ↦
      (Finset.univ : Finset (NeighborIndex F (k n) (k (n + 1)))))
    (fun n z ↦
      (if n ∈ ({i} : Finset (Fin N)) then
        F.neighboringOperator (k n) (k (n + 1)) (x n) z
      else if x n = z then 1 else 0) *
      (if n ∈ s then
        F.neighboringOperator (k n) (k (n + 1)) z (y n)
      else if z = y n then 1 else 0))]
  apply Finset.prod_congr rfl
  intro n _
  by_cases hni : n = i
  · subst n
    simp [hi]
  · by_cases hns : n ∈ s
    · simp [hni, hns]
    · by_cases hxy : x n = y n
      · simp [hni, hns, hxy]
      · simp [hni, hns, hxy]

/-- The ordered product of the single-edge matrices indexed by a list
without repetitions is the partial tensor product over the entries of that
list. -/
private theorem prod_edgePartialProduct_singletons
    (F : PhysicalSectorFactorization K) {N : ℕ} [NeZero N]
    (k : Fin N → Fin F.sectorCount) (l : List (Fin N)) (hl : l.Nodup) :
    (l.map fun i ↦ F.edgePartialProduct k {i}).prod =
      F.edgePartialProduct k l.toFinset := by
  induction l with
  | nil => simp
  | cons i l ih =>
      rw [List.nodup_cons] at hl
      simp only [List.map_cons, List.prod_cons, List.toFinset_cons]
      rw [ih hl.2]
      exact F.edgePartialProduct_singleton_mul k l.toFinset i (by
        simpa only [List.mem_toFinset] using hl.1)

/-- The ordered product over all cyclic edges is the complete product of
neighboring-operator entries. -/
private theorem prod_edgePartialProduct_singletons_univ
    (F : PhysicalSectorFactorization K) {N : ℕ} [NeZero N]
    (k : Fin N → Fin F.sectorCount) :
    (List.ofFn fun i : Fin N ↦ F.edgePartialProduct k {i}).prod =
      fun x y ↦ ∏ n : Fin N,
        F.neighboringOperator (k n) (k (n + 1)) (x n) (y n) := by
  have hlist : List.ofFn (fun i : Fin N ↦ F.edgePartialProduct k {i}) =
      (List.ofFn id).map fun i ↦ F.edgePartialProduct k {i} := by
    simp
  rw [hlist]
  rw [F.prod_edgePartialProduct_singletons k (List.ofFn id)
    (List.nodup_ofFn.mpr Function.injective_id)]
  have hfin : (List.ofFn id : List (Fin N)).toFinset = Finset.univ := by
    ext i
    simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  rw [hfin]
  exact F.edgePartialProduct_univ k

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

private theorem add_one_ne_self_of_three_le {N : ℕ} [NeZero N]
    (hN : 3 ≤ N) (i : Fin N) :
    i + 1 ≠ i := by
  have h1 : ((1 : Fin N) : ℕ) = 1 := by
    change 1 % N = 1
    rw [Nat.mod_eq_of_lt (by omega)]
  intro h
  have hval := congrArg Fin.val h
  rw [Fin.val_add_eq_ite, h1] at hval
  have := i.isLt
  split_ifs at hval <;> omega

private theorem mem_cyclicWindowSupport_two {N : ℕ} (i q : Fin N) :
    q ∈ MPSTensor.cyclicWindowSupport N 2 i ↔
      q = i ∨ q = MPSTensor.cyclicForwardSite i 1 := by
  rw [MPSTensor.cyclicWindowSupport]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨r, hr, rfl⟩
    interval_cases r
    · simp
    · simp
  · rintro (rfl | rfl)
    · exact ⟨0, by simp, by simp⟩
    · exact ⟨1, by simp, rfl⟩

/-- Within a fixed pair of sectors, the sector bond carries the neighboring
operator and the two outer factors contribute Kronecker deltas. -/
private theorem sectorBond_fixedSector_apply
    (F : PhysicalSectorFactorization K) (k h : Fin F.sectorCount)
    (x x' : SectorIndex F k) (y y' : SectorIndex F h) :
    F.sectorBond
        ![F.sectorFinEquiv.symm ⟨k, x⟩, F.sectorFinEquiv.symm ⟨h, y⟩]
        ![F.sectorFinEquiv.symm ⟨k, x'⟩, F.sectorFinEquiv.symm ⟨h, y'⟩] =
      (if x.1 = x'.1 then 1 else 0) *
        (if y.2 = y'.2 then 1 else 0) *
          F.neighboringOperator k h (x.2, y.1) (x'.2, y'.1) := by
  simp only [sectorBond, Matrix.reindex_apply, Matrix.submatrix_apply,
    finTwoArrowEquiv]
  change F.sectorCoordinateBond
      (F.twoSiteSectorEmbedding k h (x, y))
      (F.twoSiteSectorEmbedding k h (x', y')) = _
  simp only [sectorCoordinateBond, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_symm,
    twoSiteGlobalRegroupEquiv_twoSiteSectorEmbedding]
  change Matrix.blockDiagonal' (fun kh :
      Fin F.sectorCount × Fin F.sectorCount ↦
        (1 : Matrix (BoundaryIndex F kh.1 kh.2)
          (BoundaryIndex F kh.1 kh.2) ℂ) ⊗ₖ
            F.neighboringOperator kh.1 kh.2)
      ⟨(k, h), ((x.1, y.2), (x.2, y.1))⟩
      ⟨(k, h), ((x'.1, y'.2), (x'.2, y'.1))⟩ = _
  rw [Matrix.blockDiagonal'_apply_eq]
  simp only [Matrix.kroneckerMap_apply, Matrix.one_apply,
    Prod.ext_iff, neighboringOperator_apply]
  by_cases hx : x.1 = x'.1 <;> by_cases hy : y.2 = y'.2 <;>
    simp [hx, hy]

/-- In complete cyclic-edge coordinates, a translated two-site sector bond
is block diagonal in the sector configuration and acts only on the
corresponding edge.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8, lines
1586--1593. -/
private theorem reindex_embedLocalOperator_sectorBond
    (F : PhysicalSectorFactorization K) {N : ℕ} [NeZero N]
    (hN : 3 ≤ N) (i : Fin N) :
    Matrix.reindex (F.sectorEdgeChainEquiv N) (F.sectorEdgeChainEquiv N)
        (embedLocalOperator
          (d := Fintype.card (SectorSiteIndex F)) 2 N (by omega) i F.sectorBond) =
      Matrix.blockDiagonal' fun k ↦ F.edgePartialProduct k {i} := by
  classical
  ext ⟨k, x⟩ ⟨h, y⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    embedLocalOperator_apply]
  by_cases hkh : k = h
  · subst h
    rw [Matrix.blockDiagonal'_apply_eq]
    let sx := (F.cyclicEdgeEquiv k).symm x
    let sy := (F.cyclicEdgeEquiv k).symm y
    have hxchain : (F.sectorEdgeChainEquiv N).symm ⟨k, x⟩ =
        fun n ↦ F.sectorFinEquiv.symm ⟨k n, sx n⟩ := by
      funext n
      exact F.sectorEdgeChainEquiv_symm_apply N k x n
    have hychain : (F.sectorEdgeChainEquiv N).symm ⟨k, y⟩ =
        fun n ↦ F.sectorFinEquiv.symm ⟨k n, sy n⟩ := by
      funext n
      exact F.sectorEdgeChainEquiv_symm_apply N k y n
    rw [hxchain, hychain]
    simp only [sectorBond, sectorCoordinateBond, Matrix.reindex_apply,
      Equiv.symm_symm, MPSTensor.extractWindow, finTwoArrowEquiv_apply,
      Equiv.toFun_as_coe, piFinTwoEquiv_apply, Fin.isValue,
      Matrix.submatrix_apply, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
      Nat.add_zero, Nat.reduceMod, edgePartialProduct,
      Finset.mem_singleton, neighboringOperator_apply]
    have hi0 : (⟨i.val % N, Nat.mod_lt _ (Fin.pos i)⟩ : Fin N) = i := by
      ext
      exact Nat.mod_eq_of_lt i.isLt
    have hi1 : (⟨(i.val + 1) % N, Nat.mod_lt _ (Fin.pos i)⟩ : Fin N) =
        i + 1 := by
      ext
      simp [Fin.add_def]
    rw [hi0, hi1]
    have hregx : F.twoSiteGlobalRegroupEquiv
        (F.sectorFinEquiv.symm ⟨k i, sx i⟩,
          F.sectorFinEquiv.symm ⟨k (i + 1), sx (i + 1)⟩) =
        ⟨(k i, k (i + 1)), F.twoSiteRegroupEquiv (k i) (k (i + 1))
          (sx i, sx (i + 1))⟩ := by
      change F.twoSiteGlobalRegroupEquiv
          (F.twoSiteSectorEmbedding (k i) (k (i + 1))
            (sx i, sx (i + 1))) = _
      exact F.twoSiteGlobalRegroupEquiv_twoSiteSectorEmbedding _ _ _
    have hregy : F.twoSiteGlobalRegroupEquiv
        (F.sectorFinEquiv.symm ⟨k i, sy i⟩,
          F.sectorFinEquiv.symm ⟨k (i + 1), sy (i + 1)⟩) =
        ⟨(k i, k (i + 1)), F.twoSiteRegroupEquiv (k i) (k (i + 1))
          (sy i, sy (i + 1))⟩ := by
      change F.twoSiteGlobalRegroupEquiv
          (F.twoSiteSectorEmbedding (k i) (k (i + 1))
            (sy i, sy (i + 1))) = _
      exact F.twoSiteGlobalRegroupEquiv_twoSiteSectorEmbedding _ _ _
    rw [hregx, hregy, Matrix.blockDiagonal'_apply_eq]
    simp only [Matrix.kroneckerMap_apply, Matrix.one_apply]
    change (if AgreesOutsideWindow 2 (by omega) i
          (fun n ↦ F.sectorFinEquiv.symm ⟨k n, sx n⟩)
          (fun n ↦ F.sectorFinEquiv.symm ⟨k n, sy n⟩) then
        (if ((sx i).1, (sx (i + 1)).2) =
            ((sy i).1, (sy (i + 1)).2) then 1 else 0) *
          F.neighboringOperator (k i) (k (i + 1))
            ((sx i).2, (sx (i + 1)).1) ((sy i).2, (sy (i + 1)).1)
      else 0) = _
    have hxedge : ∀ n : Fin N,
        x n = ((sx n).2, (sx (n + 1)).1) := by
      intro n
      simpa only [sx, cyclicEdgeEquiv_apply] using
        (congrFun ((F.cyclicEdgeEquiv k).apply_symm_apply x) n).symm
    have hyedge : ∀ n : Fin N,
        y n = ((sy n).2, (sy (n + 1)).1) := by
      intro n
      simpa only [sy, cyclicEdgeEquiv_apply] using
        (congrFun ((F.cyclicEdgeEquiv k).apply_symm_apply y) n).symm
    have hj : MPSTensor.cyclicForwardSite i 1 = i + 1 := by
      ext
      simp [MPSTensor.cyclicForwardSite, Fin.add_def]
    have hij : i + 1 ≠ i := by
      exact add_one_ne_self_of_three_le hN i
    have hcondition :
        (AgreesOutsideWindow 2 (by omega) i
            (fun n ↦ F.sectorFinEquiv.symm ⟨k n, sx n⟩)
            (fun n ↦ F.sectorFinEquiv.symm ⟨k n, sy n⟩) ∧
          ((sx i).1, (sx (i + 1)).2) =
            ((sy i).1, (sy (i + 1)).2)) ↔
          ∀ n : Fin N, n ≠ i → x n = y n := by
      constructor
      · rintro ⟨ha, hb⟩ n hni
        rw [hxedge, hyedge]
        apply Prod.ext
        · by_cases hnj : n = i + 1
          · subst n
            exact congrArg (fun z : Fin (F.leftDim (k i)) ×
              Fin (F.rightDim (k (i + 1))) ↦ z.2) hb
          · have hs := (agreesOutsideWindow_iff 2 (by omega) i _ _).mp ha
              n (by
                rw [← MPSTensor.mem_cyclicWindowSupport_iff (by omega),
                  mem_cyclicWindowSupport_two, hj]
                simp [hni, hnj])
            have hs' := congrArg F.sectorFinEquiv hs
            simp only [Equiv.apply_symm_apply, Sigma.mk.injEq,
              true_and] at hs'
            exact congrArg Prod.snd (eq_of_heq hs').symm
        · by_cases hn1i : n + 1 = i
          · rw [hn1i]
            exact congrArg (fun z : Fin (F.leftDim (k i)) ×
              Fin (F.rightDim (k (i + 1))) ↦ z.1) hb
          · have hn1j : n + 1 ≠ i + 1 := by
              intro hn
              exact hni (add_right_cancel hn)
            have hs := (agreesOutsideWindow_iff 2 (by omega) i _ _).mp ha
              (n + 1) (by
                rw [← MPSTensor.mem_cyclicWindowSupport_iff (by omega),
                  mem_cyclicWindowSupport_two, hj]
                simp [hn1i, hn1j])
            have hs' := congrArg F.sectorFinEquiv hs
            simp only [Equiv.apply_symm_apply, Sigma.mk.injEq,
              true_and] at hs'
            exact congrArg Prod.fst (eq_of_heq hs').symm
      · intro he
        constructor
        · rw [agreesOutsideWindow_iff]
          intro q hq
          have hqi : q ≠ i := by
            intro h
            subst q
            exact hq (by simp)
          have hqj : q ≠ i + 1 := by
            intro h
            subst q
            apply hq
            rw [← MPSTensor.mem_cyclicWindowSupport_iff (by omega),
              mem_cyclicWindowSupport_two, hj]
            simp
          congr 1
          refine Sigma.ext rfl (heq_of_eq ?_)
          apply Prod.ext
          · let p : Fin N := q - 1
            have hpnext : p + 1 = q := by simp [p]
            have hpne : p ≠ i := by
              intro hp
              have : q = i + 1 := by rw [← hpnext, hp]
              exact hqj this
            have hpedge := congrArg Prod.snd (he p hpne).symm
            rw [hxedge p, hyedge p, hpnext] at hpedge
            exact hpedge
          · have hqedge := congrArg Prod.fst (he q hqi).symm
            rw [hxedge q, hyedge q] at hqedge
            exact hqedge
        · apply Prod.ext
          · let p : Fin N := i - 1
            have hpnext : p + 1 = i := by simp [p]
            have hpne : p ≠ i := by
              intro hp
              have hpnext' := hpnext
              rw [hp] at hpnext'
              exact hij hpnext'
            have hpedge := he p hpne
            rw [hxedge p, hyedge p, hpnext] at hpedge
            exact congrArg (fun z : NeighborIndex F (k p) (k i) ↦ z.2) hpedge
          · have hedge := congrArg Prod.fst (he (i + 1) hij)
            rw [hxedge (i + 1), hyedge (i + 1)] at hedge
            exact hedge
    by_cases he : ∀ n : Fin N, n ≠ i → x n = y n
    · obtain ⟨ha, hb⟩ := hcondition.mpr he
      rw [if_pos ha, if_pos hb, one_mul]
      rw [Finset.prod_eq_single i]
      · rw [if_pos rfl]
        rw [hxedge i, hyedge i]
        rfl
      · intro n _ hni
        rw [if_neg hni, if_pos (he n hni)]
      · simp
    · have hnot : ¬ (AgreesOutsideWindow 2 (by omega) i
            (fun n ↦ F.sectorFinEquiv.symm ⟨k n, sx n⟩)
            (fun n ↦ F.sectorFinEquiv.symm ⟨k n, sy n⟩) ∧
          ((sx i).1, (sx (i + 1)).2) =
            ((sy i).1, (sy (i + 1)).2)) := by
        exact fun hc ↦ he (hcondition.mp hc)
      push Not at he
      obtain ⟨n, hni, hnxy⟩ := he
      have hprod : (∏ q : Fin N,
          if q = i then
            ∑ a, F.rightTensor (k q) a (x q).1 (y q).1 *
              F.leftTensor (k (q + 1)) a (x q).2 (y q).2
          else if x q = y q then 1 else 0) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ n)
        simp [hni, hnxy]
      rw [hprod]
      by_cases ha : AgreesOutsideWindow 2 (by omega) i
          (fun n ↦ F.sectorFinEquiv.symm ⟨k n, sx n⟩)
          (fun n ↦ F.sectorFinEquiv.symm ⟨k n, sy n⟩)
      · rw [if_pos ha]
        have hb : ((sx i).1, (sx (i + 1)).2) ≠
            ((sy i).1, (sy (i + 1)).2) := fun hb ↦ hnot ⟨ha, hb⟩
        rw [if_neg hb, zero_mul]
      · rw [if_neg ha]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hkh]
    let sx := (F.cyclicEdgeEquiv k).symm x
    let ty := (F.cyclicEdgeEquiv h).symm y
    have hxchain : (F.sectorEdgeChainEquiv N).symm ⟨k, x⟩ =
        fun n ↦ F.sectorFinEquiv.symm ⟨k n, sx n⟩ := by
      funext n
      exact F.sectorEdgeChainEquiv_symm_apply N k x n
    have hychain : (F.sectorEdgeChainEquiv N).symm ⟨h, y⟩ =
        fun n ↦ F.sectorFinEquiv.symm ⟨h n, ty n⟩ := by
      funext n
      exact F.sectorEdgeChainEquiv_symm_apply N h y n
    rw [hxchain, hychain]
    simp only [sectorBond, sectorCoordinateBond, Matrix.reindex_apply,
      Equiv.symm_symm, MPSTensor.extractWindow, finTwoArrowEquiv_apply,
      Equiv.toFun_as_coe, piFinTwoEquiv_apply, Fin.isValue,
      Matrix.submatrix_apply, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
      Nat.add_zero, Nat.reduceMod]
    have hi0 : (⟨i.val % N, Nat.mod_lt _ (Fin.pos i)⟩ : Fin N) = i := by
      ext
      exact Nat.mod_eq_of_lt i.isLt
    have hi1 : (⟨(i.val + 1) % N, Nat.mod_lt _ (Fin.pos i)⟩ : Fin N) =
        i + 1 := by
      ext
      simp [Fin.add_def]
    rw [hi0, hi1]
    have hregx : F.twoSiteGlobalRegroupEquiv
        (F.sectorFinEquiv.symm ⟨k i, sx i⟩,
          F.sectorFinEquiv.symm ⟨k (i + 1), sx (i + 1)⟩) =
        ⟨(k i, k (i + 1)), F.twoSiteRegroupEquiv (k i) (k (i + 1))
          (sx i, sx (i + 1))⟩ := by
      change F.twoSiteGlobalRegroupEquiv
          (F.twoSiteSectorEmbedding (k i) (k (i + 1))
            (sx i, sx (i + 1))) = _
      exact F.twoSiteGlobalRegroupEquiv_twoSiteSectorEmbedding _ _ _
    have hregy : F.twoSiteGlobalRegroupEquiv
        (F.sectorFinEquiv.symm ⟨h i, ty i⟩,
          F.sectorFinEquiv.symm ⟨h (i + 1), ty (i + 1)⟩) =
        ⟨(h i, h (i + 1)), F.twoSiteRegroupEquiv (h i) (h (i + 1))
          (ty i, ty (i + 1))⟩ := by
      change F.twoSiteGlobalRegroupEquiv
          (F.twoSiteSectorEmbedding (h i) (h (i + 1))
            (ty i, ty (i + 1))) = _
      exact F.twoSiteGlobalRegroupEquiv_twoSiteSectorEmbedding _ _ _
    rw [hregx, hregy]
    by_cases ha : AgreesOutsideWindow 2 (by omega) i
        (fun n ↦ F.sectorFinEquiv.symm ⟨k n, sx n⟩)
        (fun n ↦ F.sectorFinEquiv.symm ⟨h n, ty n⟩)
    · rw [if_pos ha]
      have hpairs : (k i, k (i + 1)) ≠ (h i, h (i + 1)) := by
        intro hp
        apply hkh
        funext q
        by_cases hq : ((q.val + N - i.val) % N < 2)
        · rw [← MPSTensor.mem_cyclicWindowSupport_iff (by omega),
            mem_cyclicWindowSupport_two] at hq
          rcases hq with rfl | hq
          · exact congrArg Prod.fst hp
          · have hj : MPSTensor.cyclicForwardSite i 1 = i + 1 := by
              ext
              simp [MPSTensor.cyclicForwardSite, Fin.add_def]
            rw [hj] at hq
            subst q
            exact congrArg Prod.snd hp
        · have hs := (agreesOutsideWindow_iff 2 (by omega) i _ _).mp ha q hq
          have hs' := congrArg F.sectorFinEquiv hs
          simpa only [Equiv.apply_symm_apply] using
            (congrArg Sigma.fst hs').symm
      rw [Matrix.blockDiagonal'_apply_ne _ _ _ hpairs]
    · rw [if_neg ha]

private theorem reindex_list_prod
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β)
    (l : List (Matrix α α ℂ)) :
    Matrix.reindex e e l.prod =
      (l.map fun A ↦ Matrix.reindex e e A).prod := by
  induction l with
  | nil =>
      ext x y
      simp [Matrix.reindex_apply, Matrix.one_apply]
  | cons A l ih =>
      simp only [List.prod_cons, List.map_cons]
      change Matrix.reindexLinearEquiv ℂ ℂ e e (A * l.prod) = _
      rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ e e e]
      simp only [Matrix.coe_reindexLinearEquiv, ih]

private theorem blockDiagonal'_list_prod
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    (l : List ((i : ι) → Matrix (α i) (α i) ℂ)) :
    (l.map Matrix.blockDiagonal').prod =
      Matrix.blockDiagonal' fun i ↦ (l.map fun A ↦ A i).prod := by
  induction l with
  | nil =>
      ext ⟨i, x⟩ ⟨j, y⟩
      by_cases hij : i = j
      · subst j
        simp [Matrix.one_apply, Matrix.blockDiagonal'_apply]
      · simp [Matrix.blockDiagonal'_apply_ne _ _ _ hij, hij]
  | cons A l ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [ih, ← Matrix.blockDiagonal'_mul]

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
  apply (Matrix.reindex (F.sectorEdgeChainEquiv N)
    (F.sectorEdgeChainEquiv N)).injective
  rw [F.reindex_mpo_sectorCoordinateTensor_sectorEdgeChainEquiv]
  rw [reindex_list_prod]
  rw [show (List.ofFn fun i : Fin N ↦
      embedLocalOperator
        (d := Fintype.card (SectorSiteIndex F)) 2 N (by omega) i
          F.sectorBond).map
        (fun A ↦ Matrix.reindex (F.sectorEdgeChainEquiv N)
          (F.sectorEdgeChainEquiv N) A) =
      List.ofFn (fun i : Fin N ↦
        Matrix.reindex (F.sectorEdgeChainEquiv N) (F.sectorEdgeChainEquiv N)
          (embedLocalOperator
            (d := Fintype.card (SectorSiteIndex F)) 2 N (by omega) i
              F.sectorBond)) by
    simp
    rfl]
  have hmap :
      (List.ofFn fun i : Fin N ↦
        Matrix.reindex (F.sectorEdgeChainEquiv N) (F.sectorEdgeChainEquiv N)
          (embedLocalOperator
            (d := Fintype.card (SectorSiteIndex F)) 2 N (by omega) i
              F.sectorBond)) =
      List.ofFn (fun i : Fin N ↦
        Matrix.blockDiagonal' fun k ↦ F.edgePartialProduct k {i}) := by
    exact congrArg List.ofFn (funext fun i ↦
      F.reindex_embedLocalOperator_sectorBond hN i)
  rw [hmap]
  rw [show List.ofFn (fun i : Fin N ↦
      Matrix.blockDiagonal' fun k ↦ F.edgePartialProduct k {i}) =
      (List.ofFn fun i : Fin N ↦
        fun k ↦ F.edgePartialProduct k {i}).map Matrix.blockDiagonal' by
    simp
    rfl]
  rw [blockDiagonal'_list_prod]
  congr
  funext k
  symm
  have hl : (List.ofFn fun i : Fin N ↦
      fun q ↦ F.edgePartialProduct q {i}).map (fun A ↦ A k) =
      List.ofFn (fun i : Fin N ↦ F.edgePartialProduct k {i}) := by
    simp
    rfl
  rw [hl]
  exact F.prod_edgePartialProduct_singletons_univ k

end MPOTensor.PhysicalSectorFactorization
