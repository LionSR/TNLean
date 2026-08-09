/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinSum
import TNLean.MPS.MPDO.CyclicActiveFourthRegionContraction

/-!
# The cyclic-active fourth-region formula

This file identifies every retained-sector block of the fourth-region marginal
and derives the normalized block-diagonal formula from source zero correlation
length.

## Reference

* arXiv:1606.00608, Appendix C.2, Proposition 4to2, lines 1606--1617.
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

private def cyclicActiveWordSubtypeEquiv
    (F : PhysicalSectorFactorization K) (N : ℕ) :
    {t : Fin N → Fin F.sectorCount // ∀ i, F.IsCyclicActiveSector (t i)} ≃
      (Fin N → F.CyclicActiveSector) where
  toFun t i :=
    ⟨t.1 i, (F.cyclicActiveWeight_ne_zero_iff (t.1 i)).2 (t.2 i)⟩
  invFun q :=
    ⟨fun i ↦ q i, fun i ↦ (F.cyclicActiveWeight_ne_zero_iff (q i)).1 (q i).2⟩
  left_inv t := by
    ext i
    rfl
  right_inv q := by
    funext i
    rfl

/-- The separated fourth-region block in a fixed retained sector word.  It
vanishes unless every retained sector is cyclic-active.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Scope restriction (cyclic-active restriction):** The boundary factors come from
$(\lambda^{-1}T_C)^2$ on the cyclic-active support.  Sectors outside that
support contribute zero rather than being identified with cyclic-active
sectors.  See `docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
noncomputable def cyclicActiveFourthRegionBlock
    (F : PhysicalSectorFactorization K) {n : ℕ}
    (lam : ℝ) (a b : F.CyclicActiveSector → ℝ)
    (k : Fin (n + 1) → Fin F.sectorCount) :
    Matrix (F.RetainedOpenEdgeIndex k) (F.RetainedOpenEdgeIndex k) ℂ := by
  classical
  exact if hk : F.IsCyclicActiveRetainedWord k then
      let kC := F.cyclicActiveRetainedWord hk
      ((lam : ℂ) ^ 2) •
        (F.retainedBulkProduct k ⊗ₖ
          F.cyclicActiveSeparatedBoundary a b
            (kC (Fin.last n + 1)) (kC (Fin.last n)))
    else 0

/-- A retained word outside cyclic-active support has zero three-suffix
contraction.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Scope restriction (cyclic-active restriction):** The vanishing follows from
deleting sector words outside positive-length cyclic support.  See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem threeSuffixSectorContraction_eq_zero_of_not_isCyclicActiveRetainedWord
    (F : PhysicalSectorFactorization K) {n : ℕ}
    (k : Fin (n + 1) → Fin F.sectorCount)
    (hk : ¬ F.IsCyclicActiveRetainedWord k) :
    F.threeSuffixSectorContraction k = 0 := by
  classical
  ext x y
  simp only [threeSuffixSectorContraction, suffixSectorContraction, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro t _
  apply Finset.sum_eq_zero
  intro z _
  have happend :
      ¬ ∀ i, F.IsCyclicActiveSector ((Fin.append k t) i) := by
    intro hall
    apply hk
    intro i
    simpa using hall (Fin.castAdd 3 i)
  rw [F.cyclicNeighboringProduct_eq_zero_of_not_forall_isCyclicActiveSector
    (Fin.append k t) happend]
  rfl

/-- On a cyclic-active retained word, tracing the three suffix sites gives the
retained bulk product tensored with the unnormalized two-step boundary
contraction.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Scope restriction (cyclic-active restriction):** The coefficient is the square of
the restricted cyclic-active trace matrix.  See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem reindex_threeSuffixSectorContraction_eq_cyclicActiveUnnormalized
    (F : PhysicalSectorFactorization K) {n : ℕ}
    (hpos : ∀ q h, (F.neighboringOperator q h).PosSemidef)
    (k : Fin (n + 1) → Fin F.sectorCount)
    (hk : F.IsCyclicActiveRetainedWord k) :
    Matrix.reindex (F.retainedOpenEdgeEquiv k) (F.retainedOpenEdgeEquiv k)
        (F.threeSuffixSectorContraction k) =
      F.retainedBulkProduct k ⊗ₖ
        F.cyclicActiveUnnormalizedTwoStepBoundaryContraction
          (F.cyclicActiveRetainedWord hk (Fin.last n + 1))
          (F.cyclicActiveRetainedWord hk (Fin.last n)) := by
  classical
  ext x y
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, threeSuffixSectorContraction,
    suffixSectorContraction, Matrix.kroneckerMap_apply]
  have hrestrict :
      (∑ t : Fin 3 → Fin F.sectorCount,
          ∑ z : F.SectorChainFiber t,
            F.cyclicNeighboringProduct (Fin.append k t)
              (F.appendSectorFiber ((F.retainedOpenEdgeEquiv k).symm x) z)
              (F.appendSectorFiber ((F.retainedOpenEdgeEquiv k).symm y) z)) =
        ∑ t : {t : Fin 3 → Fin F.sectorCount //
            ∀ i, F.IsCyclicActiveSector (t i)},
          ∑ z : F.SectorChainFiber t.1,
            F.cyclicNeighboringProduct (Fin.append k t.1)
              (F.appendSectorFiber ((F.retainedOpenEdgeEquiv k).symm x) z)
              (F.appendSectorFiber ((F.retainedOpenEdgeEquiv k).symm y) z) := by
    apply Finset.sum_congr_set
      {t : Fin 3 → Fin F.sectorCount | ∀ i, F.IsCyclicActiveSector (t i)}
    · intro t ht
      rfl
    intro t ht
    apply Finset.sum_eq_zero
    intro z hz
    have happend :
        ¬∀ j, F.IsCyclicActiveSector ((Fin.append k t) j) := by
      intro hall
      apply ht
      intro i
      simpa using hall (Fin.natAdd (n + 1) i)
    rw [F.cyclicNeighboringProduct_eq_zero_of_not_forall_isCyclicActiveSector
      (Fin.append k t) happend]
    rfl
  rw [hrestrict]
  calc
    _ = ∑ q : Fin 3 → F.CyclicActiveSector,
        ∑ z : F.SectorChainFiber (fun i ↦ (q i : Fin F.sectorCount)),
          F.cyclicNeighboringProduct
            (Fin.append k (fun i ↦ (q i : Fin F.sectorCount)))
            (F.appendSectorFiber ((F.retainedOpenEdgeEquiv k).symm x) z)
            (F.appendSectorFiber ((F.retainedOpenEdgeEquiv k).symm y) z) := by
      apply Fintype.sum_equiv (cyclicActiveWordSubtypeEquiv F 3)
      intro q
      rfl
    _ = ∑ qrh : F.CyclicActiveSector ×
          (F.CyclicActiveSector × F.CyclicActiveSector),
        ∑ z : F.SectorChainFiber
            (fun i ↦ (((_root_.finThreeArrowEquiv F.CyclicActiveSector).symm qrh) i :
              Fin F.sectorCount)),
          F.cyclicNeighboringProduct
            (Fin.append k (fun i ↦
              (((_root_.finThreeArrowEquiv F.CyclicActiveSector).symm qrh) i :
                Fin F.sectorCount)))
            (F.appendSectorFiber ((F.retainedOpenEdgeEquiv k).symm x) z)
            (F.appendSectorFiber ((F.retainedOpenEdgeEquiv k).symm y) z) := by
      apply Fintype.sum_equiv (_root_.finThreeArrowEquiv F.CyclicActiveSector)
      intro q
      rw [Equiv.symm_apply_apply]
    _ = ∑ q : F.CyclicActiveSector,
          ∑ r : F.CyclicActiveSector,
          ∑ h : F.CyclicActiveSector,
          ∑ z : F.SectorChainFiber (F.activeThreeSectorWord q r h),
            F.cyclicNeighboringProduct
              (Fin.append k (F.activeThreeSectorWord q r h))
              (F.appendSectorFiber ((F.retainedOpenEdgeEquiv k).symm x) z)
              (F.appendSectorFiber ((F.retainedOpenEdgeEquiv k).symm y) z) := by
      simp only [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro h hh
      have ht :
          (fun i ↦ (((_root_.finThreeArrowEquiv F.CyclicActiveSector).symm
            (q, r, h)) i : Fin F.sectorCount)) =
            F.activeThreeSectorWord q r h := by
        funext i
        fin_cases i <;> rfl
      rw [ht]
    _ = _ := by
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
        cyclicActiveUnnormalizedTwoStepBoundaryContraction]
      simp_rw [F.sum_threeSuffixFiber_cyclicNeighboringProduct_active]
      simp only [Matrix.kroneckerMap_apply]
      have sum_swap (g : F.CyclicActiveSector → F.CyclicActiveSector →
          F.CyclicActiveSector → ℂ) :
          (∑ q, ∑ r, ∑ h, g q r h) = ∑ q, ∑ h, ∑ r, g q r h := by
        congr 1 with q
        rw [Finset.sum_comm]
      rw [sum_swap]
      have factor_sum (A : ℂ)
          (u v : F.CyclicActiveSector → ℂ) :
          (∑ r, A * u r * v r) = A * ∑ r, u r * v r :=
        Fintype.sum_mul_mul_eq_mul_sum_mul A u v
      simp_rw [factor_sum]
      simp_rw [F.sum_cyclicActive_trace_mul_trace_eq_pow_two hpos]
      simp only [cyclicActiveRetainedWord]
      have distribute (B : ℂ) (R : F.CyclicActiveSector → ℂ)
          (L C : F.CyclicActiveSector → F.CyclicActiveSector → ℂ) :
          (∑ q, B * (R q * ∑ h, L q h * C q h)) =
            B * ∑ q, ∑ h, C q h * (R q * L q h) := by
        calc
          _ = B * ∑ q, R q * ∑ h, L q h * C q h := by
            simpa only [mul_assoc] using
              Fintype.sum_mul_mul_eq_mul_sum_mul B R
                (fun q => ∑ h, L q h * C q h)
          _ = _ := by
            congr 1
            apply Finset.sum_congr rfl
            intro q _
            simpa only [mul_comm, mul_left_comm, mul_assoc] using
              (Fintype.sum_mul_mul_eq_mul_sum_mul (R q) (L q) (C q)).symm
      exact distribute _ _ _ _

/-- Every retained sector block of the three-suffix contraction has the
separated fourth-region form, with blocks outside cyclic-active support equal
to zero.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Scope restriction (cyclic-active restriction):** The two boundary factors arise
from the normalized square of the restricted trace matrix.  See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem reindex_threeSuffixSectorContraction_eq_cyclicActiveFourthRegionBlock
    (F : PhysicalSectorFactorization K) {n : ℕ}
    (hpos : ∀ q h, (F.neighboringOperator q h).PosSemidef)
    (lam : ℝ) (hlam : 0 < lam)
    (a b : F.CyclicActiveSector → ℝ)
    (hab : (lam⁻¹ • F.cyclicActiveSectorTraceMatrix) ^ 2 =
      Matrix.vecMulVec a b)
    (k : Fin (n + 1) → Fin F.sectorCount) :
    Matrix.reindex (F.retainedOpenEdgeEquiv k) (F.retainedOpenEdgeEquiv k)
        (F.threeSuffixSectorContraction k) =
      F.cyclicActiveFourthRegionBlock lam a b k := by
  classical
  by_cases hk : F.IsCyclicActiveRetainedWord k
  · rw [F.reindex_threeSuffixSectorContraction_eq_cyclicActiveUnnormalized
      hpos k hk]
    rw [F.cyclicActiveUnnormalizedTwoStepBoundaryContraction_eq_smul
      lam hlam, F.cyclicActiveTwoStepBoundaryContraction_eq_separated
      lam a b hab]
    ext x y
    simp only [cyclicActiveFourthRegionBlock, dif_pos hk,
      Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  · rw [F.threeSuffixSectorContraction_eq_zero_of_not_isCyclicActiveRetainedWord
      k hk]
    ext x y
    simp [cyclicActiveFourthRegionBlock, hk]

/-- The marginal obtained by tracing three suffix sites is block diagonal in
retained open-edge coordinates, and every cyclic-active block has separated
left and right boundary factors.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Scope restriction (cyclic-active restriction):** The block formula uses the
normalized square of the restricted cyclic-active trace matrix.  See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem reindex_reducedBlockState_add_three_eq_cyclicActiveFourthRegionBlock
    (F : PhysicalSectorFactorization K) (n : ℕ)
    (hpos : ∀ q h, (F.neighboringOperator q h).PosSemidef)
    (lam : ℝ) (hlam : 0 < lam)
    (a b : F.CyclicActiveSector → ℝ)
    (hab : (lam⁻¹ • F.cyclicActiveSectorTraceMatrix) ^ 2 =
      Matrix.vecMulVec a b) :
    Matrix.reindex (F.retainedOpenEdgeChainEquiv n)
        (F.retainedOpenEdgeChainEquiv n)
        (F.sectorCoordinateTensor.reducedBlockState (n + 4) (n + 1) (by omega)) =
      ((Matrix.trace (mpo F.sectorCoordinateTensor (n + 4)))⁻¹ : ℂ) •
        Matrix.blockDiagonal'
          (fun k ↦ F.cyclicActiveFourthRegionBlock lam a b k) := by
  classical
  have hraw :=
    F.reindex_reducedBlockState_add_three_eq_threeSuffixSectorContraction (n + 1)
  ext sx sy
  obtain ⟨k, x⟩ := sx
  obtain ⟨h, y⟩ := sy
  have hentry := congrFun (congrFun hraw
    ⟨k, (F.retainedOpenEdgeEquiv k).symm x⟩)
    ⟨h, (F.retainedOpenEdgeEquiv h).symm y⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply] at hentry ⊢
  change _ = _ at hentry
  change _ = _
  by_cases hkh : k = h
  · subst h
    simp only [Matrix.blockDiagonal'_apply_eq] at hentry ⊢
    rw [← F.reindex_threeSuffixSectorContraction_eq_cyclicActiveFourthRegionBlock
      hpos lam hlam a b hab k]
    exact hentry
  · simp only [Matrix.blockDiagonal'_apply_ne _ _ _ hkh] at hentry ⊢
    exact hentry

/-- Source ZCL supplies positive normalized factors for the exact
fourth-region marginal with one discarded site.  The coefficient comes from
the three-site representative of the same marginal.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Scope restriction (cyclic-active restriction):** One additional source-ZCL
marginal replacement is used, so the separated coefficient is the normalized
square of the restricted cyclic-active trace matrix.  See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem exists_cyclicActiveFourthRegion_formula_of_isSourceZCL
    (F : PhysicalSectorFactorization K) [NeZero D]
    (hK : K.IsInjective)
    (hpos : ∀ q h, (F.neighboringOperator q h).PosSemidef)
    (hZCL : K.IsSourceZCL) (n : ℕ) :
    ∃ lam : ℝ, 0 < lam ∧
      ∃ a b : F.CyclicActiveSector → ℝ,
        (∀ q, 0 < a q) ∧ (∀ h, 0 < b h) ∧ a ⬝ᵥ b = 1 ∧
          Matrix.reindex (F.retainedOpenEdgeChainEquiv n)
              (F.retainedOpenEdgeChainEquiv n)
              (F.sectorCoordinateTensor.reducedBlockState
                (n + 2) (n + 1) (by omega)) =
            ((Matrix.trace (mpo F.sectorCoordinateTensor (n + 4)))⁻¹ : ℂ) •
              Matrix.blockDiagonal'
                (fun k ↦ F.cyclicActiveFourthRegionBlock lam a b k) := by
  obtain ⟨lam, hlam, a, b, ha, hb, hab, hdot⟩ :=
    F.exists_normalized_cyclicActiveSectorTraceMatrix_pos_factorization_of_isSourceZCL
      hK hpos hZCL
  refine ⟨lam, hlam, a, b, ha, hb, hdot, ?_⟩
  rw [← F.sectorCoordinateTensor_reducedBlockState_add_three_eq_succ_of_isSourceZCL
    hZCL (n + 1)]
  exact F.reindex_reducedBlockState_add_three_eq_cyclicActiveFourthRegionBlock
    n hpos lam hlam a b hab

end MPOTensor.PhysicalSectorFactorization
