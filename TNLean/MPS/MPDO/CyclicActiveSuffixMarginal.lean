/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CyclicActiveFourthRegionContraction

/-!
# Adjacent cyclic-active suffix marginals

This file gives the physical-sector block expansions of the marginals
obtained by tracing one or two suffix sites.  After tracing the two surviving
outer boundary factors, these adjacent contractions have coefficients given
by the square and cube of the cyclic-active trace matrix.

## Reference

* arXiv:1606.00608, Appendix C.2, Proposition 4to2, lines 1606--1617.
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

/-- Trace the last site fiber of a fixed retained sector block of the cyclic
neighboring product, summing over its discarded sector label.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Local fix (adjacent marginal comparison):** This is the one-suffix side of
the source-adjacent comparison. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
noncomputable def oneSuffixSectorContraction
    (F : PhysicalSectorFactorization K) {L : ℕ}
    (k : Fin L → Fin F.sectorCount) :
    Matrix (F.SectorChainFiber k) (F.SectorChainFiber k) ℂ :=
  fun x y ↦
    ∑ t : Fin 1 → Fin F.sectorCount,
      ∑ z : F.SectorChainFiber t,
        F.cyclicNeighboringProduct (Fin.append k t)
          (F.appendSectorFiber x z) (F.appendSectorFiber y z)

/-- Trace the last two site fibers of a fixed retained sector block of the
cyclic neighboring product, summing over both discarded sector labels.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Local fix (adjacent marginal comparison):** Two suffix sites, rather than
one, give the coefficient adjacent to the existing three-suffix coefficient.
See `docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
noncomputable def twoSuffixSectorContraction
    (F : PhysicalSectorFactorization K) {L : ℕ}
    (k : Fin L → Fin F.sectorCount) :
    Matrix (F.SectorChainFiber k) (F.SectorChainFiber k) ℂ :=
  fun x y ↦
    ∑ t : Fin 2 → Fin F.sectorCount,
      ∑ z : F.SectorChainFiber t,
        F.cyclicNeighboringProduct (Fin.append k t)
          (F.appendSectorFiber x z) (F.appendSectorFiber y z)

/-- In complete physical-sector coordinates, the marginal obtained by
discarding one suffix site is the direct sum of the corresponding one-suffix
contractions of the cyclic neighboring products.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Local fix (adjacent marginal comparison):** This is the one-suffix side of
the comparison with the two-suffix expansion. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem reindex_reducedBlockState_add_one_eq_oneSuffixSectorContraction
    (F : PhysicalSectorFactorization K) (L : ℕ) :
    Matrix.reindex (F.sectorCoordinateChainEquiv L)
        (F.sectorCoordinateChainEquiv L)
        (F.sectorCoordinateTensor.reducedBlockState (L + 1) L (by omega)) =
      ((Matrix.trace (mpo F.sectorCoordinateTensor (L + 1)))⁻¹ : ℂ) •
        Matrix.blockDiagonal' (fun k ↦ F.oneSuffixSectorContraction k) := by
  classical
  letI : NeZero (L + 1) := ⟨by omega⟩
  have hblock :
      F.sectorCoordinateTensor.reducedBlockState (L + 1) L (by omega) =
        blockReducedState (Fintype.card (SectorSiteIndex F)) L 1
          (F.sectorCoordinateTensor.normalizedMPO (L + 1)) := by
    rw [MPOTensor.reducedBlockState]
    simpa only [blockReindexEquiv] using
      blockReducedState_submatrix_finCongr
        (show L + 1 = L + (L + 1 - L) by omega)
        (F.sectorCoordinateTensor.normalizedMPO (L + 1))
  rw [hblock]
  ext s t
  obtain ⟨k, x⟩ := s
  obtain ⟨h, y⟩ := t
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    blockReducedState, Matrix.partialTraceRight_apply,
    normalizedMPO, Matrix.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  congr 1
  simp only [blockSplitEquiv_symm_apply]
  change (∑ i : Fin 1 → Fin (Fintype.card (SectorSiteIndex F)),
      mpo F.sectorCoordinateTensor (L + 1)
        (Fin.append ((F.sectorCoordinateChainEquiv L).symm ⟨k, x⟩) i)
        (Fin.append ((F.sectorCoordinateChainEquiv L).symm ⟨h, y⟩) i)) = _
  have hconfig
      (p : Fin L → Fin F.sectorCount) (u : F.SectorChainFiber p)
      (q : Fin 1 → Fin F.sectorCount) (z : F.SectorChainFiber q) :
      Fin.append ((F.sectorCoordinateChainEquiv L).symm ⟨p, u⟩)
          ((F.sectorCoordinateChainEquiv 1).symm ⟨q, z⟩) =
        (F.sectorCoordinateChainEquiv (L + 1)).symm
          ⟨Fin.append p q, F.appendSectorFiber u z⟩ := by
    funext i
    refine Fin.addCases (motive := fun i' : Fin (L + 1) ↦
      Fin.append ((F.sectorCoordinateChainEquiv L).symm ⟨p, u⟩)
          ((F.sectorCoordinateChainEquiv 1).symm ⟨q, z⟩) i' =
        (F.sectorCoordinateChainEquiv (L + 1)).symm
          ⟨Fin.append p q, F.appendSectorFiber u z⟩ i')
      (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp [F.sectorCoordinateChainEquiv_symm_apply, appendSectorFiber]
    · simp [F.sectorCoordinateChainEquiv_symm_apply, appendSectorFiber]
  calc
    _ = ∑ s : F.SectorChainIndex 1,
        mpo F.sectorCoordinateTensor (L + 1)
          (Fin.append ((F.sectorCoordinateChainEquiv L).symm ⟨k, x⟩)
            ((F.sectorCoordinateChainEquiv 1).symm s))
          (Fin.append ((F.sectorCoordinateChainEquiv L).symm ⟨h, y⟩)
            ((F.sectorCoordinateChainEquiv 1).symm s)) := by
      apply Fintype.sum_equiv (F.sectorCoordinateChainEquiv 1)
      intro i
      rw [Equiv.symm_apply_apply]
    _ = _ := by
      rw [Fintype.sum_sigma]
      by_cases hkh : k = h
      · subst h
        rw [Matrix.blockDiagonal'_apply_eq]
        simp only [oneSuffixSectorContraction]
        apply Finset.sum_congr rfl
        intro q _
        apply Finset.sum_congr rfl
        intro z _
        rw [hconfig k x q z, hconfig k y q z]
        have hentry := congrFun (congrFun
          (F.reindex_mpo_sectorCoordinateTensor_eq_blockDiagonal
            (N := L + 1))
          ⟨Fin.append k q, F.appendSectorFiber x z⟩)
          ⟨Fin.append k q, F.appendSectorFiber y z⟩
        simpa only [Matrix.reindex_apply, Matrix.submatrix_apply,
          Matrix.blockDiagonal'_apply_eq] using hentry
      · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hkh]
        apply Finset.sum_eq_zero
        intro q _
        apply Finset.sum_eq_zero
        intro z _
        rw [hconfig k x q z, hconfig h y q z]
        have happend_ne : Fin.append k q ≠ Fin.append h q := by
          intro heq
          apply hkh
          funext i
          have hi := congrFun heq (Fin.castAdd 1 i)
          simpa using hi
        have hentry := congrFun (congrFun
          (F.reindex_mpo_sectorCoordinateTensor_eq_blockDiagonal
            (N := L + 1))
          ⟨Fin.append k q, F.appendSectorFiber x z⟩)
          ⟨Fin.append h q, F.appendSectorFiber y z⟩
        simpa only [Matrix.reindex_apply, Matrix.submatrix_apply,
          Matrix.blockDiagonal'_apply_ne _ _ _ happend_ne] using hentry

/-- In complete physical-sector coordinates, the marginal obtained by
discarding two suffix sites is the direct sum of the corresponding two-suffix
contractions of the cyclic neighboring products.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Local fix (adjacent marginal comparison):** This is the two-suffix side of
the comparison with the three-suffix expansion. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem reindex_reducedBlockState_add_two_eq_twoSuffixSectorContraction
    (F : PhysicalSectorFactorization K) (L : ℕ) :
    Matrix.reindex (F.sectorCoordinateChainEquiv L)
        (F.sectorCoordinateChainEquiv L)
        (F.sectorCoordinateTensor.reducedBlockState (L + 2) L (by omega)) =
      ((Matrix.trace (mpo F.sectorCoordinateTensor (L + 2)))⁻¹ : ℂ) •
        Matrix.blockDiagonal' (fun k ↦ F.twoSuffixSectorContraction k) := by
  classical
  letI : NeZero (L + 2) := ⟨by omega⟩
  have hblock :
      F.sectorCoordinateTensor.reducedBlockState (L + 2) L (by omega) =
        blockReducedState (Fintype.card (SectorSiteIndex F)) L 2
          (F.sectorCoordinateTensor.normalizedMPO (L + 2)) := by
    rw [MPOTensor.reducedBlockState]
    simpa only [blockReindexEquiv] using
      blockReducedState_submatrix_finCongr
        (show L + 2 = L + (L + 2 - L) by omega)
        (F.sectorCoordinateTensor.normalizedMPO (L + 2))
  rw [hblock]
  ext s t
  obtain ⟨k, x⟩ := s
  obtain ⟨h, y⟩ := t
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    blockReducedState, Matrix.partialTraceRight_apply,
    normalizedMPO, Matrix.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  congr 1
  simp only [blockSplitEquiv_symm_apply]
  change (∑ i : Fin 2 → Fin (Fintype.card (SectorSiteIndex F)),
      mpo F.sectorCoordinateTensor (L + 2)
        (Fin.append ((F.sectorCoordinateChainEquiv L).symm ⟨k, x⟩) i)
        (Fin.append ((F.sectorCoordinateChainEquiv L).symm ⟨h, y⟩) i)) = _
  have hconfig
      (p : Fin L → Fin F.sectorCount) (u : F.SectorChainFiber p)
      (q : Fin 2 → Fin F.sectorCount) (z : F.SectorChainFiber q) :
      Fin.append ((F.sectorCoordinateChainEquiv L).symm ⟨p, u⟩)
          ((F.sectorCoordinateChainEquiv 2).symm ⟨q, z⟩) =
        (F.sectorCoordinateChainEquiv (L + 2)).symm
          ⟨Fin.append p q, F.appendSectorFiber u z⟩ := by
    funext i
    refine Fin.addCases (motive := fun i' : Fin (L + 2) ↦
      Fin.append ((F.sectorCoordinateChainEquiv L).symm ⟨p, u⟩)
          ((F.sectorCoordinateChainEquiv 2).symm ⟨q, z⟩) i' =
        (F.sectorCoordinateChainEquiv (L + 2)).symm
          ⟨Fin.append p q, F.appendSectorFiber u z⟩ i')
      (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp [F.sectorCoordinateChainEquiv_symm_apply, appendSectorFiber]
    · simp [F.sectorCoordinateChainEquiv_symm_apply, appendSectorFiber]
  calc
    _ = ∑ s : F.SectorChainIndex 2,
        mpo F.sectorCoordinateTensor (L + 2)
          (Fin.append ((F.sectorCoordinateChainEquiv L).symm ⟨k, x⟩)
            ((F.sectorCoordinateChainEquiv 2).symm s))
          (Fin.append ((F.sectorCoordinateChainEquiv L).symm ⟨h, y⟩)
            ((F.sectorCoordinateChainEquiv 2).symm s)) := by
      apply Fintype.sum_equiv (F.sectorCoordinateChainEquiv 2)
      intro i
      rw [Equiv.symm_apply_apply]
    _ = _ := by
      rw [Fintype.sum_sigma]
      by_cases hkh : k = h
      · subst h
        rw [Matrix.blockDiagonal'_apply_eq]
        simp only [twoSuffixSectorContraction]
        apply Finset.sum_congr rfl
        intro q _
        apply Finset.sum_congr rfl
        intro z _
        rw [hconfig k x q z, hconfig k y q z]
        have hentry := congrFun (congrFun
          (F.reindex_mpo_sectorCoordinateTensor_eq_blockDiagonal
            (N := L + 2))
          ⟨Fin.append k q, F.appendSectorFiber x z⟩)
          ⟨Fin.append k q, F.appendSectorFiber y z⟩
        simpa only [Matrix.reindex_apply, Matrix.submatrix_apply,
          Matrix.blockDiagonal'_apply_eq] using hentry
      · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hkh]
        apply Finset.sum_eq_zero
        intro q _
        apply Finset.sum_eq_zero
        intro z _
        rw [hconfig k x q z, hconfig h y q z]
        have happend_ne : Fin.append k q ≠ Fin.append h q := by
          intro heq
          apply hkh
          funext i
          have hi := congrFun heq (Fin.castAdd 2 i)
          simpa using hi
        have hentry := congrFun (congrFun
          (F.reindex_mpo_sectorCoordinateTensor_eq_blockDiagonal
            (N := L + 2))
          ⟨Fin.append k q, F.appendSectorFiber x z⟩)
          ⟨Fin.append h q, F.appendSectorFiber y z⟩
        simpa only [Matrix.reindex_apply, Matrix.submatrix_apply,
          Matrix.blockDiagonal'_apply_ne _ _ _ happend_ne] using hentry

end MPOTensor.PhysicalSectorFactorization
