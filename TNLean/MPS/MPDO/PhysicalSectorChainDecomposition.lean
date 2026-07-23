/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.PiSigmaEquiv
import TNLean.MPS.MPDO.PhysicalSectorFactorization
import TNLean.MPS.MPDO.SectorEtaOperator

/-!
# Finite-chain decomposition from a physical-sector factorization

A physical-sector factorization identifies each physical site with a direct
sum of left--right tensor factors. Applying this identification at every site
separates a periodic chain into sectors. Within a fixed cyclic sector, the MPO
is the product of the neighboring contractions. Matrix entries between
distinct sector configurations vanish.

No positivity, saturation of the area law, zero correlation length, or
injectivity hypothesis is used here.

## Main definitions

* `PhysicalSectorFactorization.SectorChainFiber`
* `PhysicalSectorFactorization.SectorChainIndex`
* `PhysicalSectorFactorization.sectorChainEquiv`
* `PhysicalSectorFactorization.cyclicNeighboringProduct`

## Main statements

* `PhysicalSectorFactorization.mpo_submatrix_sector_eq_cyclicNeighboringProduct`
* `PhysicalSectorFactorization.mpo_reindex_sectorChainEquiv_eq_blockDiagonal`

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, lines 1435--1450
-/

open scoped Matrix BigOperators

namespace MPOTensor.PhysicalSectorFactorization

variable {d D N : ℕ} {K : MPOTensor d D}

attribute [local instance] Classical.decEq Classical.propDecidable

/-- The physical indices within a fixed sector configuration of a finite
chain. At site `n`, the fiber is the product of the left and right factors in
sector `k n`.

Source: arXiv:1606.00608, Appendix C.2, lines 1435--1450. -/
abbrev SectorChainFiber (F : PhysicalSectorFactorization K)
    (k : Fin N → Fin F.sectorCount) :=
  (n : Fin N) → SectorIndex F (k n)

/-- A finite-chain physical index written as a sector configuration together
with an index in the corresponding left--right fiber.

Source: arXiv:1606.00608, Appendix C.2, lines 1435--1450. -/
abbrev SectorChainIndex (F : PhysicalSectorFactorization K) (N : ℕ) :=
  Σ k : Fin N → Fin F.sectorCount, SectorChainFiber F k

/-- Applying the one-site sector decomposition at every site identifies the
physical chain with the direct sum of its sector fibers.

Source: arXiv:1606.00608, Appendix C.2, lines 1435--1450. -/
def sectorChainEquiv (F : PhysicalSectorFactorization K) (N : ℕ) :
    (Fin N → Fin d) ≃ SectorChainIndex F N :=
  (Equiv.piCongrRight fun _ : Fin N ↦ F.sectorEquiv).trans Equiv.piSigmaEquiv

/-- The cyclic product of neighboring contractions in one sector fiber. Its
factor at site `n` acts on the right factor of sector `k n` and the left
factor of sector `k (n + 1)`.

Source: arXiv:1606.00608, Appendix C.2, lines 1441--1450. -/
noncomputable def cyclicNeighboringProduct (F : PhysicalSectorFactorization K)
    [NeZero N] (k : Fin N → Fin F.sectorCount) :
    Matrix (SectorChainFiber F k) (SectorChainFiber F k) ℂ :=
  fun x y ↦ ∏ n : Fin N,
    F.neighboringOperator (k n) (k (n + 1))
      ((x n).2, (x (n + 1)).1) ((y n).2, (y (n + 1)).1)

private theorem cyclic_contraction
    (F : PhysicalSectorFactorization K) [NeZero N]
    (k : Fin N → Fin F.sectorCount)
    (iL jL : (n : Fin N) → Fin (F.leftDim (k n)))
    (iR jR : (n : Fin N) → Fin (F.rightDim (k n))) :
    (∑ g : Fin N → Fin D, ∏ n : Fin N,
        F.leftTensor (k n) (g n) (iL n) (jL n) *
          F.rightTensor (k n) (g (n + 1)) (iR n) (jR n)) =
      ∏ n : Fin N,
        F.neighboringOperator (k n) (k (n + 1))
          (iR n, iL (n + 1)) (jR n, jL (n + 1)) := by
  simp_rw [neighboringOperator_apply]
  rw [Finset.prod_univ_sum
    (fun _ : Fin N ↦ (Finset.univ : Finset (Fin D)))
    (fun n a ↦
      F.rightTensor (k n) a (iR n) (jR n) *
        F.leftTensor (k (n + 1)) a (iL (n + 1)) (jL (n + 1)))]
  simp only [Fintype.piFinset_univ]
  refine Fintype.sum_equiv (rotateConfig N D) _ _ fun g ↦ ?_
  simp only [rotateConfig_apply, Function.comp_apply, finRotate_apply]
  let qL : Fin N → ℂ :=
    fun n ↦ F.leftTensor (k n) (g n) (iL n) (jL n)
  let qR : Fin N → ℂ :=
    fun n ↦ F.rightTensor (k n) (g (n + 1)) (iR n) (jR n)
  let qLs : Fin N → ℂ :=
    fun n ↦ F.leftTensor (k (n + 1)) (g (n + 1))
      (iL (n + 1)) (jL (n + 1))
  change (∏ n, qL n * qR n) = ∏ n, qR n * qLs n
  calc
    (∏ n, qL n * qR n) = (∏ n, qL n) * ∏ n, qR n := by
      simpa using (Finset.prod_mul_distrib
        (s := (Finset.univ : Finset (Fin N))) (f := qL) (g := qR))
    _ = (∏ n, qR n) * ∏ n, qL n := mul_comm _ _
    _ = (∏ n, qR n) * ∏ n, qLs n := by
      congr 1
      change (∏ n, qL n) = ∏ n, qL (n + 1)
      simpa only [finRotate_apply] using
        (Equiv.prod_comp (finRotate N) qL).symm
    _ = ∏ n, qR n * qLs n := by
      simpa using (Finset.prod_mul_distrib
        (s := (Finset.univ : Finset (Fin N))) (f := qR) (g := qLs)).symm

private theorem conjugatePhysical_apply_same
    (F : PhysicalSectorFactorization K) (k : Fin F.sectorCount)
    (x y : SectorIndex F k) (beta alpha : Fin D) :
    conjugatePhysical K F.physicalIsometry
        (F.sectorEquiv.symm ⟨k, x⟩) (F.sectorEquiv.symm ⟨k, y⟩) beta alpha =
      F.leftTensor k beta x.1 y.1 * F.rightTensor k alpha x.2 y.2 := by
  have h := congrFun (congrFun (F.factorization beta alpha) ⟨k, x⟩) ⟨k, y⟩
  simpa [conjugatePhysical, physicalSlice, Matrix.reindex_apply,
    Matrix.blockDiagonal'_apply_eq, Matrix.kroneckerMap_apply] using h

private theorem conjugatePhysical_apply_ne
    (F : PhysicalSectorFactorization K) {k h : Fin F.sectorCount}
    (hkh : k ≠ h) (x : SectorIndex F k) (y : SectorIndex F h)
    (beta alpha : Fin D) :
    conjugatePhysical K F.physicalIsometry
        (F.sectorEquiv.symm ⟨k, x⟩) (F.sectorEquiv.symm ⟨h, y⟩) beta alpha = 0 := by
  have hentry := congrFun (congrFun (F.factorization beta alpha) ⟨k, x⟩) ⟨h, y⟩
  simpa [conjugatePhysical, physicalSlice, Matrix.reindex_apply,
    Matrix.blockDiagonal'_apply_ne _ _ _ hkh] using hentry

/-- In a fixed sector configuration, the physically transformed finite-chain
MPO is the cyclic product of the neighboring contractions.

Source: arXiv:1606.00608, Appendix C.2, lines 1441--1450. -/
theorem mpo_submatrix_sector_eq_cyclicNeighboringProduct
    (F : PhysicalSectorFactorization K) [NeZero N]
    (k : Fin N → Fin F.sectorCount) :
    Matrix.submatrix (mpo (conjugatePhysical K F.physicalIsometry) N)
        (fun x n ↦ F.sectorEquiv.symm ⟨k n, x n⟩)
        (fun x n ↦ F.sectorEquiv.symm ⟨k n, x n⟩) =
      F.cyclicNeighboringProduct k := by
  ext x y
  simp only [Matrix.submatrix_apply, mpo_apply, mpoMatrixEntry,
    MPOTensor.evalWord_ofFn, cyclicNeighboringProduct]
  have hlocal : ∀ n : Fin N,
      conjugatePhysical K F.physicalIsometry
          (F.sectorEquiv.symm ⟨k n, x n⟩)
          (F.sectorEquiv.symm ⟨k n, y n⟩) =
        Matrix.of fun beta alpha ↦
          F.leftTensor (k n) beta (x n).1 (y n).1 *
            F.rightTensor (k n) alpha (x n).2 (y n).2 := by
    intro n
    ext beta alpha
    exact F.conjugatePhysical_apply_same (k n) (x n) (y n) beta alpha
  have htrace :
      Matrix.trace (MPSTensor.evalWord
          (fun n : Fin N ↦ Matrix.of fun beta alpha ↦
            F.leftTensor (k n) beta (x n).1 (y n).1 *
              F.rightTensor (k n) alpha (x n).2 (y n).2)
          (List.ofFn id)) =
        ∏ n : Fin N,
          F.neighboringOperator (k n) (k (n + 1))
            ((x n).2, (x (n + 1)).1) ((y n).2, (y (n + 1)).1) := by
    rw [MPSTensor.trace_evalWord_eq_sum_cyclic]
    simpa only [Matrix.of_apply, id_eq] using
      F.cyclic_contraction k (fun n ↦ (x n).1) (fun n ↦ (y n).1)
        (fun n ↦ (x n).2) (fun n ↦ (y n).2)
  rw [MPSTensor.evalWord_ofFn_eq_prod] at htrace
  simpa only [hlocal, Function.id_def] using htrace

private theorem mpo_entry_eq_zero_of_sector_ne
    (F : PhysicalSectorFactorization K) [NeZero N]
    (k h : Fin N → Fin F.sectorCount) (hne : k ≠ h)
    (x : SectorChainFiber F k) (y : SectorChainFiber F h) :
    mpo (conjugatePhysical K F.physicalIsometry) N
        (fun n ↦ F.sectorEquiv.symm ⟨k n, x n⟩)
        (fun n ↦ F.sectorEquiv.symm ⟨h n, y n⟩) = 0 := by
  obtain ⟨n, hn⟩ := Function.ne_iff.mp hne
  simp only [mpo_apply, mpoMatrixEntry, MPOTensor.evalWord_ofFn]
  have hzero : Matrix.trace (MPSTensor.evalWord
      (fun i : Fin N ↦
        conjugatePhysical K F.physicalIsometry
          (F.sectorEquiv.symm ⟨k i, x i⟩)
          (F.sectorEquiv.symm ⟨h i, y i⟩))
      (List.ofFn id)) = 0 := by
    rw [MPSTensor.trace_evalWord_eq_sum_cyclic]
    apply Finset.sum_eq_zero
    intro g _
    apply Finset.prod_eq_zero (Finset.mem_univ n)
    exact F.conjugatePhysical_apply_ne hn (x n) (y n) (g n) (g (n + 1))
  rw [MPSTensor.evalWord_ofFn_eq_prod] at hzero
  simpa only [id_eq] using hzero

/-- In the chain basis determined by a physical-sector factorization, the
physically transformed MPO is the direct sum of the cyclic products of the
neighboring contractions.

No positivity of the neighboring contractions is assumed.

Source: arXiv:1606.00608, Appendix C.2, lines 1435--1450. -/
theorem mpo_reindex_sectorChainEquiv_eq_blockDiagonal
    (F : PhysicalSectorFactorization K) [NeZero N] :
    Matrix.reindex (F.sectorChainEquiv N) (F.sectorChainEquiv N)
        (mpo (conjugatePhysical K F.physicalIsometry) N) =
      Matrix.blockDiagonal' fun k ↦ F.cyclicNeighboringProduct k := by
  ext s t
  obtain ⟨k, x⟩ := s
  obtain ⟨h, y⟩ := t
  have hx :
      (F.sectorChainEquiv N).symm ⟨k, x⟩ =
        fun n ↦ F.sectorEquiv.symm ⟨k n, x n⟩ := by
    funext n
    rfl
  have hy :
      (F.sectorChainEquiv N).symm ⟨h, y⟩ =
        fun n ↦ F.sectorEquiv.symm ⟨h n, y n⟩ := by
    funext n
    rfl
  by_cases hkh : k = h
  · subst h
    rw [Matrix.blockDiagonal'_apply_eq]
    change mpo (conjugatePhysical K F.physicalIsometry) N
        ((F.sectorChainEquiv N).symm ⟨k, x⟩)
        ((F.sectorChainEquiv N).symm ⟨k, y⟩) = _
    rw [hx, hy]
    exact congrFun (congrFun (F.mpo_submatrix_sector_eq_cyclicNeighboringProduct k) x) y
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hkh]
    change mpo (conjugatePhysical K F.physicalIsometry) N
        ((F.sectorChainEquiv N).symm ⟨k, x⟩)
        ((F.sectorChainEquiv N).symm ⟨h, y⟩) = 0
    rw [hx, hy]
    exact F.mpo_entry_eq_zero_of_sector_ne k h hkh x y

end MPOTensor.PhysicalSectorFactorization
