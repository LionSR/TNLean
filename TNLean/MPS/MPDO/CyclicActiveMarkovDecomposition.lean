/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CyclicActiveCutRegrouping

/-!
# Hayashi decomposition in cyclic-active coordinates

This file assembles the normalized path factors and sector probabilities into
a Hayashi quantum-Markov decomposition at every one-site cut.

## Reference

* arXiv:1606.00608, Appendix C.2, Proposition 4to2, lines 1606--1617.
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

namespace MPOTensor.PhysicalSectorFactorization

universe u

variable {d D : ℕ} {K : MPOTensor d D}

/-- Reassociate the cut length `A + 1 + C` with the retained-chain length
`A + C + 1`.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Local fix (cyclic-active restriction):** This reassociation is used for the
retained cyclic-active chain after the additional marginal replacement. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
noncomputable def cyclicActiveCutLengthEquiv
    (F : PhysicalSectorFactorization K) (A C : ℕ) :
    (Fin (A + C + 1) → Fin (Fintype.card F.SectorSiteIndex)) ≃
      (Fin (A + 1 + C) → Fin (Fintype.card F.SectorSiteIndex)) :=
  Equiv.arrowCongr (finCongr (show A + C + 1 = A + 1 + C by omega))
    (Equiv.refl _)

/-- The complete coordinate equivalence for the Hayashi decomposition at a
one-site cut: reassociate the length, pass to retained open-edge coordinates,
and split at the middle sector.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Local fix (cyclic-active restriction):** The retained coordinates use only
positive-length cyclic sectors.  See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
noncomputable def cyclicActiveHayashiCutEquiv
    (F : PhysicalSectorFactorization K) (A C : ℕ) :
    (Fin (A + 1 + C) → Fin (Fintype.card F.SectorSiteIndex)) ≃
      Σ j : Fin F.sectorCount,
        (Fin (Fintype.card F.SectorSiteIndex ^ A) × Fin (F.leftDim j)) ×
          (Fin (F.rightDim j) × Fin (Fintype.card F.SectorSiteIndex ^ C)) :=
  (F.cyclicActiveCutLengthEquiv A C).symm.trans <|
    (F.retainedOpenEdgeChainEquiv (A + C)).trans
      (F.retainedCutEquiv A C)

/-- In direct physical coordinates, the complete cut equivalence is the
tripartite split followed by the middle-site sector decomposition.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617. -/
private theorem cyclicActiveHayashiCutEquiv_eq_direct
    (F : PhysicalSectorFactorization K) (A C : ℕ) :
    F.cyclicActiveHayashiCutEquiv A C =
      (tripartiteSplitEquiv
        (Fintype.card F.SectorSiteIndex) A 1 C).trans
        ((Equiv.prodCongr (Equiv.refl _)
          (Equiv.prodCongr F.sectorCoordinateMiddleEquiv
            (Equiv.refl _))).trans
          (HayashiMarkov.sigmaAssoc
            (dA := Fintype.card F.SectorSiteIndex ^ A)
            (dC := Fintype.card F.SectorSiteIndex ^ C)
            F.leftDim F.rightDim).symm) := by
  apply Equiv.ext
  intro z
  unfold cyclicActiveHayashiCutEquiv cyclicActiveCutLengthEquiv
    retainedOpenEdgeChainEquiv retainedCutEquiv
  simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl]
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  have hcast := (F.cyclicActiveCutLengthEquiv A C).apply_symm_apply z
  exact congrArg
    (fun w ↦ (HayashiMarkov.sigmaAssoc F.leftDim F.rightDim).symm <|
      Prod.map id (Prod.map (⇑F.sectorCoordinateMiddleEquiv) id)
        (tripartiteSplitEquiv
          (Fintype.card F.SectorSiteIndex) A 1 C w)) hcast

/-- The normalized fourth-region marginal is block diagonal at an arbitrary
one-site cut, with its blocks expressed as normalized left and right states.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Local fix (cyclic-active restriction):** The coefficient is restricted to
positive-length cyclic sectors and uses one additional marginal replacement.
See `docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
private theorem reindex_reducedBlockState_eq_cyclicActiveCut
    (F : PhysicalSectorFactorization K) [NeZero D]
    (hpos : ∀ q h, (F.neighboringOperator q h).PosSemidef)
    (hZCL : K.IsSourceZCL) (A C : ℕ) (lam : ℝ)
    (a b : F.CyclicActiveSector → ℝ)
    (ha : ∀ q, 0 < a q) (hb : ∀ h, 0 < b h)
    (hfour :
      Matrix.reindex (F.retainedOpenEdgeChainEquiv (A + C))
          (F.retainedOpenEdgeChainEquiv (A + C))
          (F.sectorCoordinateTensor.reducedBlockState
            (A + C + 2) (A + C + 1) (by omega)) =
        ((Matrix.trace
          (mpo F.sectorCoordinateTensor (A + C + 4)))⁻¹ : ℂ) •
          Matrix.blockDiagonal' (fun k ↦
            F.cyclicActiveFourthRegionBlock lam a b k)) :
    Matrix.reindex (F.cyclicActiveHayashiCutEquiv A C)
        (F.cyclicActiveHayashiCutEquiv A C)
        (F.sectorCoordinateTensor.reducedBlockState
          (A + C + 2) (A + 1 + C) (by omega)) =
      Matrix.blockDiagonal' (fun j : Fin F.sectorCount ↦
        (F.cyclicActiveCutProbability A C lam a b j : ℂ) •
          (F.cyclicActiveLeftCutState A lam b j ⊗ₖ
            F.cyclicActiveRightCutState C a j)) := by
  classical
  let L := fun j : Fin F.sectorCount ↦ F.cyclicActiveLeftCutRaw A lam b j
  let R := fun j : Fin F.sectorCount ↦ F.cyclicActiveRightCutRaw C a j
  have hL (j : Fin F.sectorCount) : (L j).PosSemidef :=
    F.cyclicActiveLeftCutRaw_posSemidef A hpos lam b (fun h ↦ (hb h).le) j
  have hR (j : Fin F.sectorCount) : (R j).PosSemidef :=
    F.cyclicActiveRightCutRaw_posSemidef C hpos a (fun q ↦ (ha q).le) j
  let xL := F.cyclicActiveLeftCutFallback A
  let xR := F.cyclicActiveRightCutFallback C
  let ρL := F.cyclicActiveLeftCutState A lam b
  let ρR := F.cyclicActiveRightCutState C a
  let t := F.cyclicActiveCutNormalization A C
  have htC : 0 < Matrix.trace
      (mpo F.sectorCoordinateTensor (A + C + 4)) :=
    F.trace_mpo_sectorCoordinateTensor_pos_of_isSourceZCL hpos hZCL (by omega)
  have htEq : Matrix.trace (mpo F.sectorCoordinateTensor (A + C + 4)) =
      (t : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa [t, cyclicActiveCutNormalization] using
        (Complex.lt_def.mp htC).2.symm
  let p := F.cyclicActiveCutProbability A C lam a b
  have hcast :
      Matrix.reindex (F.cyclicActiveCutLengthEquiv A C).symm
          (F.cyclicActiveCutLengthEquiv A C).symm
          (F.sectorCoordinateTensor.reducedBlockState
            (A + C + 2) (A + 1 + C) (by omega)) =
        F.sectorCoordinateTensor.reducedBlockState
          (A + C + 2) (A + C + 1) (by omega) := by
    ext W W'
    have h := reducedBlockState_cast F.sectorCoordinateTensor
      (N := A + C + 2) (k := A + C + 1) (k' := A + 1 + C)
      (h := show A + 1 + C = A + C + 1 by omega)
      (hk := by omega) W W'
    change F.sectorCoordinateTensor.reducedBlockState
        (A + C + 2) (A + 1 + C) _
          (F.cyclicActiveCutLengthEquiv A C W)
          (F.cyclicActiveCutLengthEquiv A C W') = _
    have hW : F.cyclicActiveCutLengthEquiv A C W = W ∘ Fin.cast
        (show A + 1 + C = A + C + 1 by omega) := by
      funext i
      rfl
    have hW' : F.cyclicActiveCutLengthEquiv A C W' = W' ∘ Fin.cast
        (show A + 1 + C = A + C + 1 by omega) := by
      funext i
      rfl
    rw [hW, hW']
    exact h.symm
  have hcut :
      Matrix.reindex (F.cyclicActiveHayashiCutEquiv A C)
          (F.cyclicActiveHayashiCutEquiv A C)
          (F.sectorCoordinateTensor.reducedBlockState
            (A + C + 2) (A + 1 + C) (by omega)) =
        ((Matrix.trace (mpo F.sectorCoordinateTensor (A + C + 4)))⁻¹ : ℂ) •
          Matrix.blockDiagonal' (fun j : Fin F.sectorCount ↦ L j ⊗ₖ R j) := by
    have hecomp :
        Matrix.reindex (F.cyclicActiveHayashiCutEquiv A C)
            (F.cyclicActiveHayashiCutEquiv A C)
            (F.sectorCoordinateTensor.reducedBlockState
              (A + C + 2) (A + 1 + C) (by omega)) =
          Matrix.reindex
            ((F.retainedOpenEdgeChainEquiv (A + C)).trans
              (F.retainedCutEquiv A C))
            ((F.retainedOpenEdgeChainEquiv (A + C)).trans
              (F.retainedCutEquiv A C))
            (Matrix.reindex (F.cyclicActiveCutLengthEquiv A C).symm
              (F.cyclicActiveCutLengthEquiv A C).symm
              (F.sectorCoordinateTensor.reducedBlockState
                (A + C + 2) (A + 1 + C) (by omega))) := by
      ext x y
      simp only [cyclicActiveHayashiCutEquiv, Matrix.reindex_apply]
      rfl
    rw [hecomp, hcast]
    have hraw := F.reindex_cyclicActiveFourthRegionBlock_eq_cutRaw
      A C lam a b
    ext x y
    have hf := congrFun (congrFun hfour
      ((F.retainedCutEquiv A C).symm x))
      ((F.retainedCutEquiv A C).symm y)
    calc
      _ = ((Matrix.trace
          (mpo F.sectorCoordinateTensor (A + C + 4)))⁻¹ : ℂ) *
          Matrix.reindex (F.retainedCutEquiv A C)
            (F.retainedCutEquiv A C)
            (Matrix.blockDiagonal' (fun k ↦
              F.cyclicActiveFourthRegionBlock lam a b k)) x y := by
        simpa [Matrix.reindex_apply] using hf
      _ = _ := by
        rw [hraw]
        rfl
  rw [hcut]
  ext ⟨j, x⟩ ⟨j', y⟩
  change ((Matrix.trace
      (mpo F.sectorCoordinateTensor (A + C + 4)))⁻¹ : ℂ) *
        Matrix.blockDiagonal' (fun j : Fin F.sectorCount ↦ L j ⊗ₖ R j)
          ⟨j, x⟩ ⟨j', y⟩ =
      Matrix.blockDiagonal' (fun j : Fin F.sectorCount ↦
        (p j : ℂ) • (ρL j ⊗ₖ ρR j)) ⟨j, x⟩ ⟨j', y⟩
  by_cases hj : j = j'
  · subst j'
    rw [Matrix.blockDiagonal'_apply_eq, Matrix.blockDiagonal'_apply_eq]
    have hkr := Matrix.kronecker_eq_trace_re_mul_normalized
      (xL j) (xR j) (hL j) (hR j)
    rw [hkr]
    dsimp only [ρL, ρR, p, t, L, R, xL, xR,
      cyclicActiveLeftCutState, cyclicActiveRightCutState,
      cyclicActiveCutProbability]
    rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
    rw [htEq]
    rw [← Complex.ofReal_inv]
    push_cast
    rw [show F.cyclicActiveCutNormalization A C = t by rfl]
    ring
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hj,
      Matrix.blockDiagonal'_apply_ne _ _ _ hj]
    exact mul_zero _

/-- Each normalized left cut block is a density matrix.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617. -/
private theorem cyclicActiveLeftCutState_isDensity
    (F : PhysicalSectorFactorization K)
    (hpos : ∀ q h, (F.neighboringOperator q h).PosSemidef)
    (A : ℕ) (lam : ℝ) (b : F.CyclicActiveSector → ℝ)
    (hb : ∀ h, 0 < b h) (j : Fin F.sectorCount) :
    (F.cyclicActiveLeftCutState A lam b j).PosSemidef ∧
      (F.cyclicActiveLeftCutState A lam b j).trace = 1 := by
  have hL := F.cyclicActiveLeftCutRaw_posSemidef
    A hpos lam b (fun h ↦ (hb h).le) j
  exact ⟨Matrix.normalizePosSemidef_posSemidef
      (F.cyclicActiveLeftCutFallback A j) hL,
    Matrix.normalizePosSemidef_trace
      (F.cyclicActiveLeftCutFallback A j) hL⟩

/-- Each normalized right cut block is a density matrix.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617. -/
private theorem cyclicActiveRightCutState_isDensity
    (F : PhysicalSectorFactorization K)
    (hpos : ∀ q h, (F.neighboringOperator q h).PosSemidef)
    (C : ℕ) (a : F.CyclicActiveSector → ℝ)
    (ha : ∀ q, 0 < a q) (j : Fin F.sectorCount) :
    (F.cyclicActiveRightCutState C a j).PosSemidef ∧
      (F.cyclicActiveRightCutState C a j).trace = 1 := by
  have hR := F.cyclicActiveRightCutRaw_posSemidef
    C hpos a (fun q ↦ (ha q).le) j
  exact ⟨Matrix.normalizePosSemidef_posSemidef
      (F.cyclicActiveRightCutFallback C j) hR,
    Matrix.normalizePosSemidef_trace
      (F.cyclicActiveRightCutFallback C j) hR⟩

/-- The cyclic-active cut coefficients are nonnegative.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617. -/
private theorem cyclicActiveCutProbability_nonneg
    (F : PhysicalSectorFactorization K) [NeZero D]
    (hpos : ∀ q h, (F.neighboringOperator q h).PosSemidef)
    (hZCL : K.IsSourceZCL) (A C : ℕ) (lam : ℝ)
    (a b : F.CyclicActiveSector → ℝ)
    (ha : ∀ q, 0 < a q) (hb : ∀ h, 0 < b h)
    (j : Fin F.sectorCount) :
    0 ≤ F.cyclicActiveCutProbability A C lam a b j := by
  have htC : 0 < Matrix.trace
      (mpo F.sectorCoordinateTensor (A + C + 4)) :=
    F.trace_mpo_sectorCoordinateTensor_pos_of_isSourceZCL hpos hZCL (by omega)
  have ht : 0 < F.cyclicActiveCutNormalization A C := by
    simpa [cyclicActiveCutNormalization] using (Complex.lt_def.mp htC).1
  have hL := F.cyclicActiveLeftCutRaw_posSemidef
    A hpos lam b (fun h ↦ (hb h).le) j
  have hR := F.cyclicActiveRightCutRaw_posSemidef
    C hpos a (fun q ↦ (ha q).le) j
  exact mul_nonneg
    (mul_nonneg (inv_nonneg.mpr ht.le)
      (Complex.nonneg_iff.mp hL.trace_nonneg).1)
    (Complex.nonneg_iff.mp hR.trace_nonneg).1

/-- The cyclic-active cut coefficients have total mass one.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Local fix (cyclic-active restriction):** The normalization is the trace of
the fourth-region marginal before the final restriction.  See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
private theorem sum_cyclicActiveCutProbability_eq_one
    (F : PhysicalSectorFactorization K) [NeZero D]
    (hpos : ∀ q h, (F.neighboringOperator q h).PosSemidef)
    (hZCL : K.IsSourceZCL) (A C : ℕ) (lam : ℝ)
    (a b : F.CyclicActiveSector → ℝ)
    (ha : ∀ q, 0 < a q) (hb : ∀ h, 0 < b h)
    (hnormalized :
      Matrix.reindex (F.cyclicActiveHayashiCutEquiv A C)
          (F.cyclicActiveHayashiCutEquiv A C)
          (F.sectorCoordinateTensor.reducedBlockState
            (A + C + 2) (A + 1 + C) (by omega)) =
        Matrix.blockDiagonal' (fun j : Fin F.sectorCount ↦
          (F.cyclicActiveCutProbability A C lam a b j : ℂ) •
            (F.cyclicActiveLeftCutState A lam b j ⊗ₖ
              F.cyclicActiveRightCutState C a j))) :
    ∑ j : Fin F.sectorCount,
      F.cyclicActiveCutProbability A C lam a b j = 1 := by
  have htraceShort : Matrix.trace
      (mpo F.sectorCoordinateTensor (A + C + 2)) ≠ 0 := by
    have hposShort := F.trace_mpo_sectorCoordinateTensor_pos_of_isSourceZCL
      hpos hZCL (N := A + C + 2) (by omega)
    exact ne_of_gt hposShort
  have hstateTrace : Matrix.trace
      (F.sectorCoordinateTensor.reducedBlockState
        (A + C + 2) (A + 1 + C) (by omega)) = 1 :=
    reducedBlockState_trace F.sectorCoordinateTensor
      (A + C + 2) (A + 1 + C) (by omega) htraceShort
  have htr := congrArg Matrix.trace hnormalized
  rw [Matrix.trace_reindex, hstateTrace, Matrix.trace_blockDiagonal'] at htr
  simp_rw [Matrix.trace_smul, Matrix.trace_kronecker,
    (F.cyclicActiveLeftCutState_isDensity hpos A lam b hb _).2,
    (F.cyclicActiveRightCutState_isDensity hpos C a ha _).2,
    mul_one] at htr
  have hpR := congrArg Complex.re htr.symm
  simpa using hpR

/-- After the direct middle-site sector decomposition, the cyclic-active cut
block matrix is the Hayashi block state.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Local fix (cyclic-active restriction):** This is the sector-coordinate
statement; transport to the original physical basis lies outside this
sector-coordinate result.  See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
private theorem cyclicActiveCut_transported_state_eq
    (F : PhysicalSectorFactorization K) (A C : ℕ) (lam : ℝ)
    (a b : F.CyclicActiveSector → ℝ)
    (hnormalized :
      Matrix.reindex (F.cyclicActiveHayashiCutEquiv A C)
          (F.cyclicActiveHayashiCutEquiv A C)
          (F.sectorCoordinateTensor.reducedBlockState
            (A + C + 2) (A + 1 + C) (by omega)) =
        Matrix.blockDiagonal' (fun j : Fin F.sectorCount ↦
          (F.cyclicActiveCutProbability A C lam a b j : ℂ) •
            (F.cyclicActiveLeftCutState A lam b j ⊗ₖ
              F.cyclicActiveRightCutState C a j))) :
    Matrix.reindex
        (HayashiMarkov.abcEquiv F.sectorCoordinateMiddleEquiv)
        (HayashiMarkov.abcEquiv F.sectorCoordinateMiddleEquiv)
        ((F.sectorCoordinateTensor.reducedBlockState
          (A + C + 2) (A + 1 + C) (by omega)).submatrix
            (tripartiteSplitEquiv
              (Fintype.card F.SectorSiteIndex) A 1 C).symm
            (tripartiteSplitEquiv
              (Fintype.card F.SectorSiteIndex) A 1 C).symm) =
      HayashiMarkov.blockState F.leftDim F.rightDim
        (F.cyclicActiveCutProbability A C lam a b)
        (F.cyclicActiveLeftCutState A lam b)
        (F.cyclicActiveRightCutState C a) := by
  have hassoc := congrArg
    (Matrix.reindex
      (HayashiMarkov.sigmaAssoc
        (dA := Fintype.card F.SectorSiteIndex ^ A)
        (dC := Fintype.card F.SectorSiteIndex ^ C)
        F.leftDim F.rightDim)
      (HayashiMarkov.sigmaAssoc
        (dA := Fintype.card F.SectorSiteIndex ^ A)
        (dC := Fintype.card F.SectorSiteIndex ^ C)
        F.leftDim F.rightDim)) hnormalized
  have heq :
      (⇑(F.cyclicActiveHayashiCutEquiv A C).symm ∘
        ⇑(HayashiMarkov.sigmaAssoc
          (dA := Fintype.card F.SectorSiteIndex ^ A)
          (dC := Fintype.card F.SectorSiteIndex ^ C)
          F.leftDim F.rightDim).symm) =
        (⇑(tripartiteSplitEquiv
          (Fintype.card F.SectorSiteIndex) A 1 C).symm ∘
          Prod.map id
            (Prod.map (⇑F.sectorCoordinateMiddleEquiv.symm) id)) := by
    have heDirect := F.cyclicActiveHayashiCutEquiv_eq_direct A C
    rw [heDirect]
    rfl
  ext x y
  have hxy := congrFun (congrFun hassoc x) y
  have hx := congrFun heq x
  have hy := congrFun heq y
  simp only [Function.comp_apply] at hx hy
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply] at hxy
  rw [hx, hy] at hxy
  simpa [HayashiMarkov.blockState, HayashiMarkov.abcEquiv] using hxy

/-- Source zero correlation length gives an explicit quantum-Markov
decomposition at every one-site cut of the fourth-region marginal.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Local fix (cyclic-active restriction):** The separating coefficient is the
normalized square of the trace matrix restricted to positive-length cyclic
sectors, and it is obtained after one additional marginal replacement.  See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem exists_hayashiMarkovDecomposition_cyclicActiveCut_of_isSourceZCL
    (F : PhysicalSectorFactorization K) [NeZero D]
    (hK : K.IsInjective)
    (hpos : ∀ q h, (F.neighboringOperator q h).PosSemidef)
    (hZCL : K.IsSourceZCL) (A C : ℕ) :
    let ρ_ABC :=
      (F.sectorCoordinateTensor.reducedBlockState
        (A + C + 2) (A + 1 + C) (by omega)).submatrix
          (tripartiteSplitEquiv
            (Fintype.card F.SectorSiteIndex) A 1 C).symm
          (tripartiteSplitEquiv
            (Fintype.card F.SectorSiteIndex) A 1 C).symm
    Nonempty (HayashiMarkovDecomposition ρ_ABC) := by
  classical
  dsimp only
  obtain ⟨lam, _, a, b, ha, hb, _, hfour⟩ :=
    F.exists_cyclicActiveFourthRegion_formula_of_isSourceZCL
      hK hpos hZCL (A + C)
  have hnormalized :=
    F.reindex_reducedBlockState_eq_cyclicActiveCut
      hpos hZCL A C lam a b ha hb hfour
  have hp_sum :=
    F.sum_cyclicActiveCutProbability_eq_one
      hpos hZCL A C lam a b ha hb hnormalized
  refine ⟨{
    m := F.sectorCount
    dL := F.leftDim
    dR := F.rightDim
    decompB := F.sectorCoordinateMiddleEquiv
    U_B := 1
    p := F.cyclicActiveCutProbability A C lam a b
    hp_nonneg := F.cyclicActiveCutProbability_nonneg
      hpos hZCL A C lam a b ha hb
    hp_sum := hp_sum
    ρ_left := F.cyclicActiveLeftCutState A lam b
    ρ_right := F.cyclicActiveRightCutState C a
    hρ_left_dm := F.cyclicActiveLeftCutState_isDensity hpos A lam b hb
    hρ_right_dm := F.cyclicActiveRightCutState_isDensity hpos C a ha
    h_state := ?_ }⟩
  simpa [HayashiMarkov.liftB] using
    F.cyclicActiveCut_transported_state_eq A C lam a b hnormalized

end MPOTensor.PhysicalSectorFactorization
