/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ListProduct
import TNLean.MPS.MPDO.PhysicalSectorBondTwoSite
import TNLean.MPS.MPDO.PhysicalSectorProductRealization

/-!
# Physical transport of the sector product realization

This file transports the cyclic neighboring-operator product from physical-sector
coordinates to the original physical coordinates.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, Proposition C.8, lines 1581--1593
-/

open scoped Matrix BigOperators Kronecker

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

/-- The sitewise product of the one-site physical coordinate matrix on a
chain of length `N`.

Source: arXiv:1606.00608, Appendix C.2, lines 1581--1583. -/
private noncomputable def physicalCoordinateMatrixN
    (F : PhysicalSectorFactorization K) (N : ℕ) :
    Matrix (Fin N → Fin (Fintype.card (SectorSiteIndex F)))
      (Fin N → Fin d) ℂ :=
  fun s t ↦ ∏ n : Fin N, F.physicalCoordinateMatrix (s n) (t n)

/-- The sitewise physical coordinate matrix is an isometry. -/
private theorem physicalCoordinateMatrixN_isometry
    (F : PhysicalSectorFactorization K) (N : ℕ) :
    (F.physicalCoordinateMatrixN N)ᴴ * F.physicalCoordinateMatrixN N = 1 := by
  classical
  ext x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    physicalCoordinateMatrixN]
  simp_rw [star_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.piFinset_univ]
  rw [← Finset.prod_univ_sum
    (fun _ : Fin N ↦
      (Finset.univ : Finset (Fin (Fintype.card (SectorSiteIndex F)))))
    (fun n a ↦ star (F.physicalCoordinateMatrix a (x n)) *
      F.physicalCoordinateMatrix a (y n))]
  have hentry : ∀ n : Fin N,
      (∑ a : Fin (Fintype.card (SectorSiteIndex F)),
        star (F.physicalCoordinateMatrix a (x n)) *
        F.physicalCoordinateMatrix a (y n)) =
      if x n = y n then 1 else 0 := by
    intro n
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply] using
      congrFun (congrFun F.physicalCoordinateMatrix_isometry (x n)) (y n)
  simp_rw [hentry]
  rw [Fintype.prod_boole]
  congr 1
  exact propext funext_iff.symm

/-- The sitewise physical coordinate matrix is a coisometry. -/
private theorem physicalCoordinateMatrixN_coisometry
    (F : PhysicalSectorFactorization K) (N : ℕ) :
    F.physicalCoordinateMatrixN N * (F.physicalCoordinateMatrixN N)ᴴ = 1 := by
  classical
  ext x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    physicalCoordinateMatrixN]
  simp_rw [star_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.piFinset_univ]
  rw [← Finset.prod_univ_sum
    (fun _ : Fin N ↦ (Finset.univ : Finset (Fin d)))
    (fun n a ↦ F.physicalCoordinateMatrix (x n) a *
      star (F.physicalCoordinateMatrix (y n) a))]
  have hentry : ∀ n : Fin N,
      (∑ a, F.physicalCoordinateMatrix (x n) a *
        star (F.physicalCoordinateMatrix (y n) a)) =
      if x n = y n then 1 else 0 := by
    intro n
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply] using
      congrFun (congrFun F.physicalCoordinateMatrix_coisometry (x n)) (y n)
  simp_rw [hentry]
  rw [Fintype.prod_boole]
  congr 1
  exact propext funext_iff.symm

private def braKetFunctionsEquiv {i a b : Type*} :
    ((i → b) × (i → a)) ≃ (i → a × b) :=
  (Equiv.prodComm _ _).trans (Equiv.arrowProdEquivProdArrow i (fun _ ↦ a) (fun _ ↦ b)).symm

private theorem evalWord_changePhysicalBasis_ofFn {e : ℕ}
    (V : Matrix (Fin e) (Fin d) ℂ) (M : MPOTensor d D) {N : ℕ}
    (s t : Fin N → Fin e) :
    MPOTensor.evalWord (changePhysicalBasis V M) (List.ofFn s) (List.ofFn t) =
      ∑ x : Fin N → Fin d × Fin d,
        (∏ i : Fin N, V (s i) (x i).1 * star (V (t i) (x i).2)) •
          MPOTensor.evalWord M
            (List.ofFn fun i : Fin N ↦ (x i).1)
            (List.ofFn fun i : Fin N ↦ (x i).2) := by
  rw [MPOTensor.evalWord_ofFn]
  simp_rw [changePhysicalBasis_apply_eq_sum]
  rw [List.prod_ofFn_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [List.prod_ofFn_smul, MPOTensor.evalWord_ofFn]

/-- The length-`N` MPO transforms by the sitewise physical coordinate
matrix.

Source: arXiv:1606.00608, Appendix C.2, lines 1581--1583. -/
private theorem physicalCoordinateMatrixN_mpo
    (F : PhysicalSectorFactorization K) (N : ℕ) :
    singleKrausMap (F.physicalCoordinateMatrixN N) (mpo K N) =
      mpo F.sectorCoordinateTensor N := by
  rw [F.sectorCoordinateTensor_eq_changePhysicalBasis]
  ext s t
  simp only [singleKrausMap_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    physicalCoordinateMatrixN, mpo_apply, mpoMatrixEntry,
    evalWord_changePhysicalBasis_ofFn, Matrix.trace_sum, Matrix.trace_smul,
    smul_eq_mul, star_prod]
  have hexpand :
      (∑ q : Fin N → Fin d,
        (∑ p : Fin N → Fin d,
          (∏ i : Fin N, F.physicalCoordinateMatrix (s i) (p i)) *
            Matrix.trace (MPOTensor.evalWord K (List.ofFn p) (List.ofFn q))) *
          (∏ i : Fin N, star (F.physicalCoordinateMatrix (t i) (q i)))) =
        ∑ q : Fin N → Fin d, ∑ p : Fin N → Fin d,
          ((∏ i : Fin N, F.physicalCoordinateMatrix (s i) (p i)) *
            Matrix.trace (MPOTensor.evalWord K (List.ofFn p) (List.ofFn q))) *
          (∏ i : Fin N, star (F.physicalCoordinateMatrix (t i) (q i))) := by
    apply Finset.sum_congr rfl
    intro q _
    simpa only using Finset.sum_mul Finset.univ
      (fun p : Fin N → Fin d ↦
        (∏ i : Fin N, F.physicalCoordinateMatrix (s i) (p i)) *
          Matrix.trace (MPOTensor.evalWord K (List.ofFn p) (List.ofFn q)))
      (∏ i : Fin N, star (F.physicalCoordinateMatrix (t i) (q i)))
  rw [hexpand]
  have h := Fintype.sum_equiv
    (braKetFunctionsEquiv (i := Fin N) (a := Fin d) (b := Fin d))
    (fun p : (Fin N → Fin d) × (Fin N → Fin d) ↦
      (∏ i : Fin N, F.physicalCoordinateMatrix (s i) (p.2 i)) *
        Matrix.trace (MPOTensor.evalWord K (List.ofFn p.2) (List.ofFn p.1)) *
        (∏ i : Fin N, star (F.physicalCoordinateMatrix (t i) (p.1 i))))
    (fun x : Fin N → Fin d × Fin d ↦
      (∏ i : Fin N,
        F.physicalCoordinateMatrix (s i) (x i).1 *
          star (F.physicalCoordinateMatrix (t i) (x i).2)) *
        Matrix.trace (MPOTensor.evalWord K
          (List.ofFn fun i : Fin N ↦ (x i).1)
          (List.ofFn fun i : Fin N ↦ (x i).2)))
    (fun p ↦ by
      dsimp
      change
        (∏ i : Fin N, F.physicalCoordinateMatrix (s i) (p.2 i)) *
              Matrix.trace (MPOTensor.evalWord K
                (List.ofFn p.2) (List.ofFn p.1)) *
            (∏ i : Fin N,
              star (F.physicalCoordinateMatrix (t i) (p.1 i))) =
          (∏ i : Fin N,
            F.physicalCoordinateMatrix (s i) (p.2 i) *
              star (F.physicalCoordinateMatrix (t i) (p.1 i))) *
            Matrix.trace (MPOTensor.evalWord K
              (List.ofFn p.2) (List.ofFn p.1))
      have hprod :
          (∏ i : Fin N,
            F.physicalCoordinateMatrix (s i) (p.2 i) *
              star (F.physicalCoordinateMatrix (t i) (p.1 i))) =
            (∏ i : Fin N, F.physicalCoordinateMatrix (s i) (p.2 i)) *
              (∏ i : Fin N,
                star (F.physicalCoordinateMatrix (t i) (p.1 i))) := by
        exact Finset.prod_mul_distrib
      rw [hprod]
      ring)
  rw [Fintype.sum_prod_type] at h
  exact h

private theorem reindex_physicalCoordinateMatrixN_windowComplement
    (F : PhysicalSectorFactorization K) {N : ℕ} (hN : 2 ≤ N) (i : Fin N) :
    Matrix.reindex
        (windowComplementEquiv
          (d := Fintype.card (SectorSiteIndex F)) 2 N hN i)
        (windowComplementEquiv (d := d) 2 N hN i)
        (F.physicalCoordinateMatrixN N) =
      F.physicalCoordinateMatrixN 2 ⊗ₖ F.physicalCoordinateMatrixN (N - 2) := by
  ext ⟨x, u⟩ ⟨y, v⟩
  let es := windowComplementEquiv
    (d := Fintype.card (SectorSiteIndex F)) 2 N hN i
  let ep := windowComplementEquiv (d := d) 2 N hN i
  let s := es.symm (x, u)
  let t := ep.symm (y, v)
  have hes : es s = (x, u) := es.apply_symm_apply (x, u)
  have het : ep t = (y, v) := ep.apply_symm_apply (y, v)
  have hx : MPSTensor.extractWindow 2 i s = x := congrArg Prod.fst hes
  have hy : MPSTensor.extractWindow 2 i t = y := congrArg Prod.fst het
  have hu : (fun r ↦ s ⟨(i.val + 2 + r.val) % N,
      Nat.mod_lt _ (Fin.pos i)⟩) = u := congrArg Prod.snd hes
  have hv : (fun r ↦ t ⟨(i.val + 2 + r.val) % N,
      Nat.mod_lt _ (Fin.pos i)⟩) = v := congrArg Prod.snd het
  change (∏ n : Fin N, F.physicalCoordinateMatrix (s n) (t n)) = _
  rw [MPSTensor.prod_cyclicWindow_complement 2 N hN i]
  simp only [MPSTensor.extractWindow] at hx hy
  simp only [physicalCoordinateMatrixN, Matrix.kroneckerMap_apply]
  apply congrArg₂ (fun a b : ℂ ↦ a * b)
  · apply Finset.prod_congr rfl
    intro r _
    rw [congrFun hx r, congrFun hy r]
  · apply Finset.prod_congr rfl
    intro r _
    rw [congrFun hu r, congrFun hv r]

private theorem physicalCoordinateMatrixN_two
    (F : PhysicalSectorFactorization K) :
    F.physicalCoordinateMatrixN 2 =
      Matrix.reindex
        (finTwoArrowEquiv
          (Fin (Fintype.card (SectorSiteIndex F)))).symm
        (finTwoArrowEquiv (Fin d)).symm F.physicalCoordinateMatrixTwo := by
  ext s t
  simp [physicalCoordinateMatrixN, physicalCoordinateMatrixTwo,
    Matrix.reindex_apply, Matrix.kroneckerMap_apply, finTwoArrowEquiv]

private theorem singleKrausMap_physicalCoordinateMatrixN_two_physicalBond
    (F : PhysicalSectorFactorization K) :
    singleKrausMap (F.physicalCoordinateMatrixN 2) F.physicalBond =
      F.sectorBond := by
  apply (Matrix.reindex
    (finTwoArrowEquiv (Fin (Fintype.card (SectorSiteIndex F))))
    (finTwoArrowEquiv (Fin (Fintype.card (SectorSiteIndex F))))).injective
  simp only [singleKrausMap_apply]
  change Matrix.reindexLinearEquiv ℂ ℂ
      (finTwoArrowEquiv (Fin (Fintype.card (SectorSiteIndex F))))
      (finTwoArrowEquiv (Fin (Fintype.card (SectorSiteIndex F))))
      (F.physicalCoordinateMatrixN 2 * F.physicalBond *
        (F.physicalCoordinateMatrixN 2)ᴴ) = _
  rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ
      (finTwoArrowEquiv (Fin (Fintype.card (SectorSiteIndex F))))
      (finTwoArrowEquiv (Fin d))
      (finTwoArrowEquiv (Fin (Fintype.card (SectorSiteIndex F)))),
    ← Matrix.reindexLinearEquiv_mul ℂ ℂ
      (finTwoArrowEquiv (Fin (Fintype.card (SectorSiteIndex F))))
      (finTwoArrowEquiv (Fin d))
      (finTwoArrowEquiv (Fin d))]
  simp only [Matrix.coe_reindexLinearEquiv]
  have hV : Matrix.reindex
      (finTwoArrowEquiv (Fin (Fintype.card (SectorSiteIndex F))))
      (finTwoArrowEquiv (Fin d)) (F.physicalCoordinateMatrixN 2) =
      F.physicalCoordinateMatrixTwo := by
    ext x y
    simp [physicalCoordinateMatrixN_two, Matrix.reindex_apply]
  have hB : Matrix.reindex (finTwoArrowEquiv (Fin d))
      (finTwoArrowEquiv (Fin d)) F.physicalBond = F.physicalPairBond := by
    ext x y
    simp [physicalBond, Matrix.reindex_apply]
  have hVH : Matrix.reindex (finTwoArrowEquiv (Fin d))
      (finTwoArrowEquiv (Fin (Fintype.card (SectorSiteIndex F))))
      (F.physicalCoordinateMatrixN 2)ᴴ = F.physicalCoordinateMatrixTwoᴴ := by
    simpa only [Matrix.conjTranspose_reindex] using
      congrArg Matrix.conjTranspose hV
  have hSector : Matrix.reindex
      (finTwoArrowEquiv (Fin (Fintype.card (SectorSiteIndex F))))
      (finTwoArrowEquiv (Fin (Fintype.card (SectorSiteIndex F)))) F.sectorBond =
      F.sectorCoordinateBond := by
    ext x y
    simp [sectorBond, Matrix.reindex_apply]
  rw [hV, hB, hVH, hSector]
  simp only [physicalPairBond, singleKrausMap_apply,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc F.physicalCoordinateMatrixTwo
    F.physicalCoordinateMatrixTwoᴴ,
    F.physicalCoordinateMatrixTwo_coisometry, Matrix.one_mul]
  exact Matrix.mul_one _

/-- A translated physical bond is carried to the corresponding
sector-coordinate bond by the sitewise physical coordinate matrix.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8, lines
1581--1593. -/
private theorem physicalCoordinateMatrixN_embedLocalOperator_physicalBond
    (F : PhysicalSectorFactorization K) {N : ℕ} (hN : 2 ≤ N) (i : Fin N) :
    singleKrausMap (F.physicalCoordinateMatrixN N)
        (embedLocalOperator (d := d) 2 N hN i F.physicalBond) =
      embedLocalOperator
        (d := Fintype.card (SectorSiteIndex F)) 2 N hN i F.sectorBond := by
  let es := windowComplementEquiv
    (d := Fintype.card (SectorSiteIndex F)) 2 N hN i
  let ep := windowComplementEquiv (d := d) 2 N hN i
  apply (Matrix.reindex es es).injective
  simp only [singleKrausMap_apply]
  change Matrix.reindexLinearEquiv ℂ ℂ es es
      (F.physicalCoordinateMatrixN N *
        embedLocalOperator (d := d) 2 N hN i F.physicalBond *
          (F.physicalCoordinateMatrixN N)ᴴ) = _
  rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ es ep es,
    ← Matrix.reindexLinearEquiv_mul ℂ ℂ es ep ep]
  simp only [Matrix.coe_reindexLinearEquiv]
  rw [F.reindex_physicalCoordinateMatrixN_windowComplement hN i,
    reindex_embedLocalOperator_windowComplement]
  have hVH : Matrix.reindex ep es (F.physicalCoordinateMatrixN N)ᴴ =
      (F.physicalCoordinateMatrixN 2)ᴴ ⊗ₖ
        (F.physicalCoordinateMatrixN (N - 2))ᴴ := by
    simpa only [Matrix.conjTranspose_reindex,
      Matrix.conjTranspose_kronecker] using congrArg Matrix.conjTranspose
        (F.reindex_physicalCoordinateMatrixN_windowComplement hN i)
  rw [hVH, reindex_embedLocalOperator_windowComplement]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp only [Matrix.mul_one]
  rw [← singleKrausMap_apply,
    F.singleKrausMap_physicalCoordinateMatrixN_two_physicalBond,
    F.physicalCoordinateMatrixN_coisometry]

private theorem singleKrausMap_list_prod
    {a b : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (V : Matrix a b ℂ)
    (hiso : Vᴴ * V = 1) (hcoiso : V * Vᴴ = 1)
    (l : List (Matrix b b ℂ)) :
    singleKrausMap V l.prod = (l.map (singleKrausMap V)).prod := by
  induction l with
  | nil =>
      simp only [List.prod_nil, List.map_nil, singleKrausMap_apply]
      simpa only [Matrix.mul_one] using hcoiso
  | cons A l ih =>
      simp only [List.prod_cons, List.map_cons, singleKrausMap_apply]
      rw [← ih]
      simp only [singleKrausMap_apply, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Vᴴ V, hiso, Matrix.one_mul]

private theorem physicalCoordinateMatrixN_product_physicalBond
    (F : PhysicalSectorFactorization K) {N : ℕ} (hN : 2 ≤ N) :
    singleKrausMap (F.physicalCoordinateMatrixN N)
        (List.ofFn fun i : Fin N ↦
          embedLocalOperator (d := d) 2 N hN i F.physicalBond).prod =
      (List.ofFn fun i : Fin N ↦
        embedLocalOperator
          (d := Fintype.card (SectorSiteIndex F)) 2 N hN i F.sectorBond).prod := by
  rw [singleKrausMap_list_prod _ (F.physicalCoordinateMatrixN_isometry N)
    (F.physicalCoordinateMatrixN_coisometry N)]
  congr 1
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  exact F.physicalCoordinateMatrixN_embedLocalOperator_physicalBond hN i

/-- For every length at least three, the MPO in the original physical
coordinates is the ordered product of the translated physical-sector bonds.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8, lines
1581--1593.

**Scope restriction (given physical-sector factorization):** The source
derives this factorization and positivity of the neighboring operators from
SAL. The theorem `MPOTensor.nonempty_etaLocalStructureData_of_isSAL` supplies that
factorization and the complete positive commuting product form from injectivity
and SAL; the present theorem records only the conditional product identity. -/
private theorem mpo_eq_product_physicalBond_of_three_le
    (F : PhysicalSectorFactorization K) {N : ℕ} [NeZero N] (hN : 3 ≤ N) :
    mpo K N =
      (List.ofFn fun i : Fin N ↦
        embedLocalOperator (d := d) 2 N (by omega) i F.physicalBond).prod := by
  let V := F.physicalCoordinateMatrixN N
  have htransport : singleKrausMap V (mpo K N) =
      singleKrausMap V
        (List.ofFn fun i : Fin N ↦
          embedLocalOperator (d := d) 2 N (by omega) i F.physicalBond).prod := by
    rw [F.physicalCoordinateMatrixN_mpo,
      F.mpo_sectorCoordinateTensor_eq_product_sectorBond hN,
      F.physicalCoordinateMatrixN_product_physicalBond (by omega)]
  have hiso : Vᴴ * V = 1 := F.physicalCoordinateMatrixN_isometry N
  calc
    mpo K N = singleKrausMap Vᴴ (singleKrausMap V (mpo K N)) := by
      simp only [singleKrausMap_apply, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc]
      rw [hiso, Matrix.mul_one, ← Matrix.mul_assoc, hiso, Matrix.one_mul]
    _ = singleKrausMap Vᴴ (singleKrausMap V
        (List.ofFn fun i : Fin N ↦
          embedLocalOperator (d := d) 2 N (by omega) i F.physicalBond).prod) := by
      rw [htransport]
    _ = (List.ofFn fun i : Fin N ↦
        embedLocalOperator (d := d) 2 N (by omega) i F.physicalBond).prod := by
      simp only [singleKrausMap_apply, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc]
      rw [hiso, Matrix.mul_one, ← Matrix.mul_assoc, hiso, Matrix.one_mul]

private theorem boundaryOperator_one_kronecker_neighboring_eq_mul_crossedSectorBond
    (F : PhysicalSectorFactorization K) (k h : Fin F.sectorCount) :
    F.boundaryOperator k h 1 ⊗ₖ F.neighboringOperator k h =
      ((1 : Matrix (BoundaryIndex F k h) (BoundaryIndex F k h) ℂ) ⊗ₖ
        F.neighboringOperator k h) * F.crossedSectorBond k h := by
  rw [crossedSectorBond, ← Matrix.mul_kronecker_mul]
  simp only [Matrix.one_mul, Matrix.mul_one]
  congr 1
  ext x y
  simp [boundaryOperator_apply, neighboringOperator_apply,
    Matrix.reindex_apply, Matrix.one_apply, mul_comm]

/-- The two-site sector-coordinate MPO is the product of the ordinary bond
and its oppositely oriented cyclic translate.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8, lines
1581--1593. -/
private theorem physClose2_sectorCoordinateTensor_one_eq_bond_mul_crossed
    (F : PhysicalSectorFactorization K) :
    physClose2 F.sectorCoordinateTensor 1 =
      F.sectorCoordinateBond * swapPairMatrix F.sectorCoordinateBond := by
  apply (Matrix.reindex F.twoSiteGlobalRegroupEquiv
    F.twoSiteGlobalRegroupEquiv).injective
  change Matrix.reindexLinearEquiv ℂ ℂ F.twoSiteGlobalRegroupEquiv
      F.twoSiteGlobalRegroupEquiv (physClose2 F.sectorCoordinateTensor 1) =
    Matrix.reindexLinearEquiv ℂ ℂ F.twoSiteGlobalRegroupEquiv
      F.twoSiteGlobalRegroupEquiv (_ * _)
  rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ
      F.twoSiteGlobalRegroupEquiv F.twoSiteGlobalRegroupEquiv
      F.twoSiteGlobalRegroupEquiv]
  change Matrix.reindex F.twoSiteGlobalRegroupEquiv
      F.twoSiteGlobalRegroupEquiv (physClose2 F.sectorCoordinateTensor 1) =
    Matrix.reindex F.twoSiteGlobalRegroupEquiv F.twoSiteGlobalRegroupEquiv
        F.sectorCoordinateBond *
      Matrix.reindex F.twoSiteGlobalRegroupEquiv F.twoSiteGlobalRegroupEquiv
        (swapPairMatrix F.sectorCoordinateBond)
  rw [F.twoSiteGlobalClosure_eq,
    F.reindex_swapPairMatrix_sectorCoordinateBond]
  have horiginal :
      Matrix.reindex F.twoSiteGlobalRegroupEquiv F.twoSiteGlobalRegroupEquiv
          F.sectorCoordinateBond =
        Matrix.blockDiagonal' fun kh :
            Fin F.sectorCount × Fin F.sectorCount ↦
          (1 : Matrix (BoundaryIndex F kh.1 kh.2)
            (BoundaryIndex F kh.1 kh.2) ℂ) ⊗ₖ
              F.neighboringOperator kh.1 kh.2 := by
    ext x y
    simp [sectorCoordinateBond, Matrix.reindex_apply]
  rw [horiginal, ← Matrix.blockDiagonal'_mul]
  congr 1
  funext kh
  exact F.boundaryOperator_one_kronecker_neighboring_eq_mul_crossedSectorBond
    kh.1 kh.2

/-- At length two, the original-coordinate closure is the product of the
physical pair bond and its oppositely oriented translate.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8, lines
1581--1593. -/
private theorem physClose2_one_eq_physicalPairBond_mul_crossed
    (F : PhysicalSectorFactorization K) :
    physClose2 K 1 =
      F.physicalPairBond * swapPairMatrix F.physicalPairBond := by
  rw [← F.physicalCoordinateMatrixTwo_conjTranspose_physClose2 1]
  rw [F.physClose2_sectorCoordinateTensor_one_eq_bond_mul_crossed]
  have hswap : swapPairMatrix F.physicalPairBond =
      singleKrausMap F.physicalCoordinateMatrixTwoᴴ
        (swapPairMatrix F.sectorCoordinateBond) := by
    simpa only [physicalPairBond, physicalCoordinateMatrixTwo] using
      swapPairMatrix_singleKraus_kronecker_self
        F.physicalCoordinateMatrix F.sectorCoordinateBond
  rw [hswap]
  simp only [physicalPairBond, singleKrausMap_apply,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc F.physicalCoordinateMatrixTwo
    F.physicalCoordinateMatrixTwoᴴ]
  rw [F.physicalCoordinateMatrixTwo_coisometry]
  simp only [Matrix.one_mul]

/-- Reindexing the length-two MPO by ordered pairs gives the two-site closure
with identity virtual boundary. -/
private theorem reindex_mpo_two_eq_physClose2_one (K : MPOTensor d D) :
    Matrix.reindex (finTwoArrowEquiv (Fin d)) (finTwoArrowEquiv (Fin d))
        (mpo K 2) =
      physClose2 K 1 := by
  ext i j
  simp [Matrix.reindex_apply, mpo_apply, mpoMatrixEntry,
    MPOTensor.evalWord, finTwoArrowEquiv, physClose2_apply]

/-- On a two-site periodic chain, the MPO is exactly the product of the two
oriented translates of the physical-sector bond.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8, lines
1581--1593. -/
private theorem mpo_two_eq_product_physicalBond
    (F : PhysicalSectorFactorization K) :
    mpo K 2 =
      (List.ofFn fun i : Fin 2 ↦
        embedLocalOperator (d := d) 2 2 (by decide) i F.physicalBond).prod := by
  have hprod :
      (List.ofFn fun i : Fin 2 ↦
        embedLocalOperator (d := d) 2 2 (by decide) i F.physicalBond).prod =
      embedLocalOperator (d := d) 2 2 (by decide)
          (0 : Fin 2) F.physicalBond *
        embedLocalOperator (d := d) 2 2 (by decide)
          (1 : Fin 2) F.physicalBond := by
    simp [List.ofFn_succ]
  rw [hprod]
  apply (Matrix.reindex (finTwoArrowEquiv (Fin d))
    (finTwoArrowEquiv (Fin d))).injective
  change Matrix.reindexLinearEquiv ℂ ℂ (finTwoArrowEquiv (Fin d))
      (finTwoArrowEquiv (Fin d)) (mpo K 2) =
    Matrix.reindexLinearEquiv ℂ ℂ (finTwoArrowEquiv (Fin d))
      (finTwoArrowEquiv (Fin d))
        (embedLocalOperator (d := d) 2 2 (by decide)
            (0 : Fin 2) F.physicalBond *
          embedLocalOperator (d := d) 2 2 (by decide)
            (1 : Fin 2) F.physicalBond)
  rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ
      (finTwoArrowEquiv (Fin d)) (finTwoArrowEquiv (Fin d))
      (finTwoArrowEquiv (Fin d))]
  simpa only [Matrix.coe_reindexLinearEquiv,
    reindex_mpo_two_eq_physClose2_one,
    F.reindex_embedLocalOperator_two_zero,
    F.reindex_embedLocalOperator_two_one] using
      F.physClose2_one_eq_physicalPairBond_mul_crossed

/-- At every length at least two, the MPO is exactly the ordered product of
the translated physical-sector bonds.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8, lines
1581--1593.

**Scope restriction (given physical-sector factorization):** The source
derives this factorization and positivity of the neighboring operators from
SAL. The theorem `MPOTensor.nonempty_etaLocalStructureData_of_isSAL` supplies that
factorization and the complete positive commuting product form from injectivity
and SAL; the present theorem records only the conditional product identity. -/
theorem mpo_eq_product_physicalBond
    (F : PhysicalSectorFactorization K) {N : ℕ} (hN : 2 ≤ N) :
    mpo K N =
      (List.ofFn fun i : Fin N ↦
        embedLocalOperator (d := d) 2 N hN i F.physicalBond).prod := by
  by_cases htwo : N = 2
  · subst N
    exact F.mpo_two_eq_product_physicalBond
  · letI : NeZero N := ⟨by omega⟩
    exact F.mpo_eq_product_physicalBond_of_three_le (by omega)

/-- The positive scalar in the physical-sector product realization may be
chosen to be exactly one.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8, lines
1581--1593.

**Scope restriction (given physical-sector factorization):** The source
derives this factorization and positivity of the neighboring operators from
SAL. The theorem `MPOTensor.nonempty_etaLocalStructureData_of_isSAL` supplies that
factorization and the complete positive commuting product form from injectivity
and SAL; the present theorem records only the conditional scalar formulation. -/
theorem exists_positive_scalar_mpo_eq_product_physicalBond
    (F : PhysicalSectorFactorization K) {N : ℕ} (hN : 2 ≤ N) :
    ∃ c : ℝ, 0 < c ∧
      mpo K N = (c : ℂ) •
        (List.ofFn fun i : Fin N ↦
          embedLocalOperator (d := d) 2 N hN i F.physicalBond).prod := by
  refine ⟨1, by norm_num, ?_⟩
  rw [F.mpo_eq_product_physicalBond hN]
  norm_num

end MPOTensor.PhysicalSectorFactorization
