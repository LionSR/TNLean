/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CyclicActiveCutCoordinates

/-!
# Left and right states at cyclic-active cuts

This file defines the positive path factors, their standard coordinate forms,
the normalized conditional states, and the sector probabilities.

## Reference

* arXiv:1606.00608, Appendix C.2, Proposition 4to2, lines 1606--1617.
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

namespace MPOTensor.PhysicalSectorFactorization

universe u

variable {d D : ℕ} {K : MPOTensor d D}

/-- The unnormalized positive left path factor in fixed-sector open-edge
coordinates.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** This factor uses the left boundary
of the restricted two-step coefficient. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
noncomputable def cyclicActiveLeftOpenBlock
    (F : PhysicalSectorFactorization K) {A : ℕ}
    (lam : ℝ) (b : F.CyclicActiveSector → ℝ)
    (k : Fin (A + 1) → Fin F.sectorCount) :
    Matrix (F.LeftOpenEdgeIndex k) (F.LeftOpenEdgeIndex k) ℂ := by
  classical
  exact if hk : F.IsCyclicActiveRetainedWord k then
      let kC := F.cyclicActiveRetainedWord hk
      ((lam : ℂ) ^ 2) •
        (F.cyclicActiveLeftBoundary b (kC 0) ⊗ₖ
          Matrix.finKronecker (fun i : Fin A ↦
            F.neighboringOperator (k i.castSucc) (k i.succ)))
    else 0

/-- The unnormalized positive right path factor in fixed-sector open-edge
coordinates.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** This factor uses the right
boundary of the restricted two-step coefficient. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
noncomputable def cyclicActiveRightOpenBlock
    (F : PhysicalSectorFactorization K) {C : ℕ}
    (a : F.CyclicActiveSector → ℝ)
    (k : Fin (C + 1) → Fin F.sectorCount) :
    Matrix (F.RightOpenEdgeIndex k) (F.RightOpenEdgeIndex k) ℂ := by
  classical
  exact if hk : F.IsCyclicActiveRetainedWord k then
      let kC := F.cyclicActiveRetainedWord hk
      Matrix.finKronecker (fun i : Fin C ↦
          F.neighboringOperator (k i.castSucc) (k i.succ)) ⊗ₖ
        F.cyclicActiveRightBoundary a (kC (Fin.last C))
    else 0

/-- The left open-chain factor is positive semidefinite when the neighbouring
operators and left boundary weights are nonnegative.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** This is the left positive factor
for the restricted two-step coefficient. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem cyclicActiveLeftOpenBlock_posSemidef
    (F : PhysicalSectorFactorization K) {A : ℕ}
    (hpos : ∀ q h, (F.neighboringOperator q h).PosSemidef)
    (lam : ℝ) (b : F.CyclicActiveSector → ℝ) (hb : ∀ h, 0 ≤ b h)
    (k : Fin (A + 1) → Fin F.sectorCount) :
    (F.cyclicActiveLeftOpenBlock lam b k).PosSemidef := by
  classical
  by_cases hk : F.IsCyclicActiveRetainedWord k
  · rw [cyclicActiveLeftOpenBlock, dif_pos hk]
    apply Matrix.PosSemidef.smul
    · exact (F.cyclicActiveLeftBoundary_posSemidef hpos b hb _).kronecker
        (Matrix.finKronecker_posSemidef _ fun i ↦ hpos _ _)
    · have hs : 0 ≤ lam ^ 2 := sq_nonneg lam
      exact_mod_cast hs
  · rw [cyclicActiveLeftOpenBlock, dif_neg hk]
    exact Matrix.PosSemidef.zero

/-- The right open-chain factor is positive semidefinite when the neighbouring
operators and right boundary weights are nonnegative.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** This is the right positive factor
for the restricted two-step coefficient. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem cyclicActiveRightOpenBlock_posSemidef
    (F : PhysicalSectorFactorization K) {C : ℕ}
    (hpos : ∀ q h, (F.neighboringOperator q h).PosSemidef)
    (a : F.CyclicActiveSector → ℝ) (ha : ∀ q, 0 ≤ a q)
    (k : Fin (C + 1) → Fin F.sectorCount) :
    (F.cyclicActiveRightOpenBlock a k).PosSemidef := by
  classical
  by_cases hk : F.IsCyclicActiveRetainedWord k
  · rw [cyclicActiveRightOpenBlock, dif_pos hk]
    exact (Matrix.finKronecker_posSemidef _ fun i ↦ hpos _ _).kronecker
      (F.cyclicActiveRightBoundary_posSemidef hpos a ha _)
  · rw [cyclicActiveRightOpenBlock, dif_neg hk]
    exact Matrix.PosSemidef.zero

/-- The left path factor on the standard `A ⊗ B_jᴸ` coordinates.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** The direct sum ranges over left
paths retained by the cyclic-active restriction. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
noncomputable def cyclicActiveLeftCutRaw
    (F : PhysicalSectorFactorization K) (A : ℕ)
    (lam : ℝ) (b : F.CyclicActiveSector → ℝ)
    (j : Fin F.sectorCount) :
    Matrix
      (Fin (Fintype.card (SectorSiteIndex F) ^ A) × Fin (F.leftDim j))
      (Fin (Fintype.card (SectorSiteIndex F) ^ A) × Fin (F.leftDim j)) ℂ :=
  Matrix.reindex (F.leftSectorOpenEdgeEquiv A j).symm
    (F.leftSectorOpenEdgeEquiv A j).symm <|
      Matrix.blockDiagonal' fun k ↦
        F.cyclicActiveLeftOpenBlock lam b (F.leftSectorWord j k)

/-- The right path factor on the standard `B_jʳ ⊗ C` coordinates.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** The direct sum ranges over right
paths retained by the cyclic-active restriction. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
noncomputable def cyclicActiveRightCutRaw
    (F : PhysicalSectorFactorization K) (C : ℕ)
    (a : F.CyclicActiveSector → ℝ)
    (j : Fin F.sectorCount) :
    Matrix
      (Fin (F.rightDim j) × Fin (Fintype.card (SectorSiteIndex F) ^ C))
      (Fin (F.rightDim j) × Fin (Fintype.card (SectorSiteIndex F) ^ C)) ℂ :=
  Matrix.reindex (F.rightSectorOpenEdgeEquiv C j).symm
    (F.rightSectorOpenEdgeEquiv C j).symm <|
      Matrix.blockDiagonal' fun k ↦
        F.cyclicActiveRightOpenBlock a (F.rightSectorWord j k)

/-- The direct sum of the left open-chain factors is positive semidefinite in
the standard left-cut coordinates.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** The sum ranges over the retained
cyclic-active sectors. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem cyclicActiveLeftCutRaw_posSemidef
    (F : PhysicalSectorFactorization K) (A : ℕ)
    (hpos : ∀ q h, (F.neighboringOperator q h).PosSemidef)
    (lam : ℝ) (b : F.CyclicActiveSector → ℝ) (hb : ∀ h, 0 ≤ b h)
    (j : Fin F.sectorCount) :
    (F.cyclicActiveLeftCutRaw A lam b j).PosSemidef := by
  classical
  exact (Matrix.PosSemidef.blockDiagonal' _ fun k ↦
    F.cyclicActiveLeftOpenBlock_posSemidef hpos lam b hb _).submatrix _

/-- The direct sum of the right open-chain factors is positive semidefinite in
the standard right-cut coordinates.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** The sum ranges over the retained
cyclic-active sectors. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem cyclicActiveRightCutRaw_posSemidef
    (F : PhysicalSectorFactorization K) (C : ℕ)
    (hpos : ∀ q h, (F.neighboringOperator q h).PosSemidef)
    (a : F.CyclicActiveSector → ℝ) (ha : ∀ q, 0 ≤ a q)
    (j : Fin F.sectorCount) :
    (F.cyclicActiveRightCutRaw C a j).PosSemidef := by
  classical
  exact (Matrix.PosSemidef.blockDiagonal' _ fun k ↦
    F.cyclicActiveRightOpenBlock_posSemidef hpos a ha _).submatrix _

/-- The sector-coordinate periodic normalization is strictly positive at
every positive length under source zero correlation length.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** This positivity normalizes the
restricted cut probabilities after the additional marginal replacement. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem trace_mpo_sectorCoordinateTensor_pos_of_isSourceZCL
    (F : PhysicalSectorFactorization K) [NeZero D]
    (hpos : ∀ q h, (F.neighboringOperator q h).PosSemidef)
    (hZCL : K.IsSourceZCL) {N : ℕ} (hN : 0 < N) :
    0 < Matrix.trace (mpo F.sectorCoordinateTensor N) := by
  letI : NeZero N := ⟨ne_of_gt hN⟩
  have hpsd := F.mpo_sectorCoordinateTensor_posSemidef hpos (N := N)
  have htrace : Matrix.trace (mpo F.sectorCoordinateTensor N) ≠ 0 := by
    rw [F.sectorCoordinateTensor_eq_changePhysicalBasis,
      trace_mpo_changePhysicalBasis_of_isometry F.physicalCoordinateMatrix
        F.physicalCoordinateMatrix_isometry]
    exact trace_mpo_ne_zero_of_isSourceZCL K hZCL hN
  exact hpsd.trace_pos_of_ne_zero fun hzero ↦ htrace (by simp [hzero])

/-- A fixed index used only in the zero-trace fallback normalization of a
left cut block.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** Positive block traces make the
fallback mathematically inactive; it makes normalization total.  See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
noncomputable def cyclicActiveLeftCutFallback
    (F : PhysicalSectorFactorization K) (A : ℕ) (j : Fin F.sectorCount) :
    Fin (Fintype.card F.SectorSiteIndex ^ A) × Fin (F.leftDim j) :=
  (⟨0, by
    apply pow_pos
    exact Fintype.card_pos_iff.mpr ⟨⟨j,
      (⟨0, F.leftDim_pos j⟩, ⟨0, F.rightDim_pos j⟩)⟩⟩⟩,
    ⟨0, F.leftDim_pos j⟩)

/-- A fixed index used only in the zero-trace fallback normalization of a
right cut block.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** Positive block traces make the
fallback mathematically inactive; it makes normalization total.  See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
noncomputable def cyclicActiveRightCutFallback
    (F : PhysicalSectorFactorization K) (C : ℕ) (j : Fin F.sectorCount) :
    Fin (F.rightDim j) × Fin (Fintype.card F.SectorSiteIndex ^ C) :=
  (⟨0, F.rightDim_pos j⟩,
    ⟨0, by
      apply pow_pos
      exact Fintype.card_pos_iff.mpr ⟨⟨j,
        (⟨0, F.leftDim_pos j⟩, ⟨0, F.rightDim_pos j⟩)⟩⟩⟩)

/-- The normalized left path state in a cyclic-active cut block.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** The state normalizes the positive
left factor of the restricted two-step coefficient.  See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
noncomputable def cyclicActiveLeftCutState
    (F : PhysicalSectorFactorization K) (A : ℕ) (lam : ℝ)
    (b : F.CyclicActiveSector → ℝ) (j : Fin F.sectorCount) :=
  Matrix.normalizePosSemidef (F.cyclicActiveLeftCutFallback A j)
    (F.cyclicActiveLeftCutRaw A lam b j)

/-- The normalized right path state in a cyclic-active cut block.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** The state normalizes the positive
right factor of the restricted two-step coefficient.  See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
noncomputable def cyclicActiveRightCutState
    (F : PhysicalSectorFactorization K) (C : ℕ)
    (a : F.CyclicActiveSector → ℝ) (j : Fin F.sectorCount) :=
  Matrix.normalizePosSemidef (F.cyclicActiveRightCutFallback C j)
    (F.cyclicActiveRightCutRaw C a j)

/-- The real periodic normalization used by the cut probabilities.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Scope restriction (cyclic-active restriction):** Its length includes the additional
marginal replacement.  See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
noncomputable def cyclicActiveCutNormalization
    (F : PhysicalSectorFactorization K) (A C : ℕ) : ℝ :=
  (Matrix.trace (mpo F.sectorCoordinateTensor (A + C + 4))).re

/-- The probability of a middle sector in the cyclic-active cut
decomposition.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** The weight uses the normalized
restricted two-step coefficient.  See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
noncomputable def cyclicActiveCutProbability
    (F : PhysicalSectorFactorization K) (A C : ℕ) (lam : ℝ)
    (a b : F.CyclicActiveSector → ℝ) (j : Fin F.sectorCount) : ℝ :=
  (F.cyclicActiveCutNormalization A C)⁻¹ *
    (F.cyclicActiveLeftCutRaw A lam b j).trace.re *
    (F.cyclicActiveRightCutRaw C a j).trace.re

/-- Reassociate a retained chain of lengths `A, 1, C` into the index used by
the dependent blocks of the Hayashi decomposition.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** This identification separates the
retained cyclic-active chain at its distinguished middle site. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
noncomputable def retainedCutEquiv
    (F : PhysicalSectorFactorization K) (A C : ℕ) :
    (Σ k : Fin (A + C + 1) → Fin F.sectorCount,
      F.RetainedOpenEdgeIndex (n := A + C) k) ≃
      Σ j : Fin F.sectorCount,
        (Fin (Fintype.card (SectorSiteIndex F) ^ A) × Fin (F.leftDim j)) ×
          (Fin (F.rightDim j) × Fin (Fintype.card (SectorSiteIndex F) ^ C)) :=
  ((Equiv.sigmaCongrRight fun k ↦ F.retainedOpenEdgeEquiv k).symm.trans
    (F.sectorCoordinateChainEquiv (A + C + 1)).symm).trans <|
      (Equiv.arrowCongr (finCongr (by omega)) (Equiv.refl _)).trans <|
      (tripartiteSplitEquiv (Fintype.card (SectorSiteIndex F)) A 1 C).trans <|
        (Equiv.prodCongr (Equiv.refl _)
          (Equiv.prodCongr
            F.sectorCoordinateMiddleEquiv
            (Equiv.refl _))).trans <|
          (HayashiMarkov.sigmaAssoc
            (dA := Fintype.card (SectorSiteIndex F) ^ A)
            (dC := Fintype.card (SectorSiteIndex F) ^ C)
            F.leftDim F.rightDim).symm

/-- Under the inverse tripartite identification, the sector at the middle
site is the prescribed cut sector.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** This identity describes the
sector coordinates of the restricted decomposition. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
@[simp] theorem retainedCutEquiv_symm_middle_sector
    (F : PhysicalSectorFactorization K) (A C : ℕ)
    (j : Fin F.sectorCount)
    (l : Fin (Fintype.card (SectorSiteIndex F) ^ A) × Fin (F.leftDim j))
    (r : Fin (F.rightDim j) × Fin (Fintype.card (SectorSiteIndex F) ^ C)) :
    ((F.retainedCutEquiv A C).symm ⟨j, (l, r)⟩).1 ⟨A, by omega⟩ = j := by
  simp [retainedCutEquiv, sectorCoordinateMiddleEquiv,
    HayashiMarkov.sigmaAssoc, tripartiteSplitEquiv, blockSplitEquiv,
    show (⟨A, by omega⟩ : Fin (A + 1 + C)) =
      Fin.castAdd C (Fin.last A) by ext; simp,
    finSumFinEquiv_symm_apply_castAdd,
    Equiv.sumArrowEquivProdArrow_symm_apply_inl]

/-- Under the inverse tripartite identification, a sector to the left of the
cut is the corresponding sector in the left chain.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** This identity describes the
sector coordinates of the restricted decomposition. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
@[simp] theorem retainedCutEquiv_symm_left_sector
    (F : PhysicalSectorFactorization K) (A C : ℕ)
    (j : Fin F.sectorCount)
    (l : Fin (Fintype.card (SectorSiteIndex F) ^ A) × Fin (F.leftDim j))
    (r : Fin (F.rightDim j) × Fin (Fintype.card (SectorSiteIndex F) ^ C))
    (i : Fin A) :
    ((F.retainedCutEquiv A C).symm ⟨j, (l, r)⟩).1 ⟨i, by omega⟩ =
      (F.sectorCoordinateChainEquiv A (finFunctionFinEquiv.symm l.1)).1 i := by
  simp [retainedCutEquiv, sectorCoordinateMiddleEquiv,
    HayashiMarkov.sigmaAssoc, tripartiteSplitEquiv, blockSplitEquiv,
    show (⟨i, by omega⟩ : Fin (A + 1 + C)) =
      Fin.castAdd C (Fin.castAdd 1 i) by ext; simp,
    finSumFinEquiv_symm_apply_castAdd,
    Equiv.sumArrowEquivProdArrow_symm_apply_inl]

/-- Under the inverse tripartite identification, a sector to the right of the
cut is the corresponding sector in the right chain.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** This identity describes the
sector coordinates of the restricted decomposition. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
@[simp] theorem retainedCutEquiv_symm_right_sector
    (F : PhysicalSectorFactorization K) (A C : ℕ)
    (j : Fin F.sectorCount)
    (l : Fin (Fintype.card (SectorSiteIndex F) ^ A) × Fin (F.leftDim j))
    (r : Fin (F.rightDim j) × Fin (Fintype.card (SectorSiteIndex F) ^ C))
    (i : Fin C) :
    ((F.retainedCutEquiv A C).symm ⟨j, (l, r)⟩).1
        ⟨A + 1 + i, by omega⟩ =
      (F.sectorCoordinateChainEquiv C (finFunctionFinEquiv.symm r.2)).1 i := by
  simp [retainedCutEquiv, sectorCoordinateMiddleEquiv,
    HayashiMarkov.sigmaAssoc, tripartiteSplitEquiv, blockSplitEquiv,
    show (⟨A + 1 + i, by omega⟩ : Fin (A + 1 + C)) =
      Fin.natAdd (A + 1) i by ext; simp,
    finSumFinEquiv_symm_apply_natAdd,
    Equiv.sumArrowEquivProdArrow_symm_apply_inr]

/-- At a site to the left of the cut, the retained-chain fiber coordinate
agrees with the corresponding coordinate of the left open chain.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** This is the dependent-coordinate
identity for the restricted decomposition. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem retainedCutEquiv_symm_left_fiber_heq
    (F : PhysicalSectorFactorization K) (A C : ℕ)
    (j : Fin F.sectorCount)
    (l : Fin (Fintype.card (SectorSiteIndex F) ^ A) × Fin (F.leftDim j))
    (r : Fin (F.rightDim j) × Fin (Fintype.card (SectorSiteIndex F) ^ C))
    (i : Fin A) :
    let g := (F.retainedCutEquiv A C).symm ⟨j, (l, r)⟩
    let s := F.leftSectorOpenEdgeEquiv A j l
    ((F.retainedOpenEdgeEquiv g.1).symm g.2 ⟨i, by omega⟩) ≍
      ((F.leftFixedFiberOpenEdgeEquiv j s.1).symm s.2).1 i := by
  let xG : Fin (A + C + 1) → Fin (Fintype.card (SectorSiteIndex F)) :=
    ((finCongr (by omega)).arrowCongr (Equiv.refl _))
      ((tripartiteSplitEquiv (Fintype.card (SectorSiteIndex F)) A 1 C).symm
        (((Equiv.refl _).prodCongr
          (F.sectorCoordinateMiddleEquiv.symm.prodCongr (Equiv.refl _)))
            (HayashiMarkov.sigmaAssoc F.leftDim F.rightDim ⟨j, (l, r)⟩)))
  let xL := finFunctionFinEquiv.symm l.1
  let sG := F.sectorCoordinateChainEquiv (A + C + 1) xG
  let eG : F.SectorChainIndex (A + C + 1) ≃
      (Σ k : Fin (A + C + 1) → Fin F.sectorCount,
        F.RetainedOpenEdgeIndex (n := A + C) k) :=
    Equiv.sigmaCongrRight fun k ↦ F.retainedOpenEdgeEquiv k
  have hG0 := eG.symm_apply_apply sG
  have hG1heq :
      (F.retainedOpenEdgeEquiv (eG sG).1).symm (eG sG).2 ≍ sG.2 :=
    (Sigma.mk.inj_iff.mp hG0).2
  have hG1 :
      (F.retainedOpenEdgeEquiv (eG sG).1).symm (eG sG).2 = sG.2 := by
    simpa [eG] using eq_of_heq hG1heq
  have hG := congrFun hG1 ⟨i, by omega⟩
  have hG' :
      ((F.retainedOpenEdgeEquiv
        ((F.retainedCutEquiv A C).symm ⟨j, (l, r)⟩).1).symm
          ((F.retainedCutEquiv A C).symm ⟨j, (l, r)⟩).2 ⟨i, by omega⟩) ≍
        (F.sectorCoordinateChainEquiv (A + C + 1) xG).2 ⟨i, by omega⟩ := by
    apply heq_of_eq
    convert hG using 1 <;> simp [retainedCutEquiv, xG, sG, eG]; rfl
  dsimp only
  refine hG'.trans ?_
  have hL :
      ((F.leftFixedFiberOpenEdgeEquiv j
        (F.leftSectorOpenEdgeEquiv A j l).1).symm
          (F.leftSectorOpenEdgeEquiv A j l).2).1 i ≍
        (F.sectorCoordinateChainEquiv A xL).2 i := by
    let sL := F.sectorCoordinateChainEquiv A xL
    let tL : Σ k : Fin A → Fin F.sectorCount,
        F.SectorChainFiber k × Fin (F.leftDim j) := ⟨sL.1, (sL.2, l.2)⟩
    let eL : (Σ k : Fin A → Fin F.sectorCount,
        F.SectorChainFiber k × Fin (F.leftDim j)) ≃
        (Σ k : Fin A → Fin F.sectorCount,
          F.LeftOpenEdgeIndex (F.leftSectorWord j k)) :=
      Equiv.sigmaCongrRight fun k ↦ F.leftFixedFiberOpenEdgeEquiv j k
    have hL0 := eL.symm_apply_apply tL
    have hL1heq :
        (F.leftFixedFiberOpenEdgeEquiv j (eL tL).1).symm (eL tL).2 ≍
          tL.2 := (Sigma.mk.inj_iff.mp hL0).2
    have hL1 :
        (F.leftFixedFiberOpenEdgeEquiv j (eL tL).1).symm (eL tL).2 =
          tL.2 := by
      simpa [eL] using eq_of_heq hL1heq
    have hL2 := congrFun (congrArg Prod.fst hL1) i
    apply heq_of_eq
    convert hL2 using 1 <;>
      simp [leftSectorOpenEdgeEquiv, xL, sL, tL, eL] <;> rfl
  refine (F.sectorCoordinateChainEquiv_apply_snd_heq (A + C + 1) xG
    ⟨i, by omega⟩).trans ?_
  refine HEq.trans ?_ hL.symm
  have hx : xG ⟨i, by omega⟩ = xL i := by
    simp [xG, sectorCoordinateMiddleEquiv, HayashiMarkov.sigmaAssoc,
      tripartiteSplitEquiv, blockSplitEquiv,
      show (⟨i, by omega⟩ : Fin (A + 1 + C)) =
        Fin.castAdd C (Fin.castAdd 1 i) by ext; simp,
      finSumFinEquiv_symm_apply_castAdd,
      Equiv.sumArrowEquivProdArrow_symm_apply_inl, xL]
  have he := congrArg F.sectorFinEquiv hx
  exact (Sigma.mk.inj_iff.mp he).2.trans
    (F.sectorCoordinateChainEquiv_apply_snd_heq A xL i).symm

/-- At a site to the right of the cut, the retained-chain fiber coordinate
agrees with the corresponding coordinate of the right open chain.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** This is the dependent-coordinate
identity for the restricted decomposition. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem retainedCutEquiv_symm_right_fiber_heq
    (F : PhysicalSectorFactorization K) (A C : ℕ)
    (j : Fin F.sectorCount)
    (l : Fin (Fintype.card (SectorSiteIndex F) ^ A) × Fin (F.leftDim j))
    (r : Fin (F.rightDim j) × Fin (Fintype.card (SectorSiteIndex F) ^ C))
    (i : Fin C) :
    let g := (F.retainedCutEquiv A C).symm ⟨j, (l, r)⟩
    let s := F.rightSectorOpenEdgeEquiv C j r
    ((F.retainedOpenEdgeEquiv g.1).symm g.2 ⟨A + 1 + i, by omega⟩) ≍
      ((F.rightFixedFiberOpenEdgeEquiv j s.1).symm s.2).2 i := by
  let xG : Fin (A + C + 1) → Fin (Fintype.card (SectorSiteIndex F)) :=
    ((finCongr (by omega)).arrowCongr (Equiv.refl _))
      ((tripartiteSplitEquiv (Fintype.card (SectorSiteIndex F)) A 1 C).symm
        (((Equiv.refl _).prodCongr
          (F.sectorCoordinateMiddleEquiv.symm.prodCongr (Equiv.refl _)))
            (HayashiMarkov.sigmaAssoc F.leftDim F.rightDim ⟨j, (l, r)⟩)))
  let xR := finFunctionFinEquiv.symm r.2
  let sG := F.sectorCoordinateChainEquiv (A + C + 1) xG
  let eG : F.SectorChainIndex (A + C + 1) ≃
      (Σ k : Fin (A + C + 1) → Fin F.sectorCount,
        F.RetainedOpenEdgeIndex (n := A + C) k) :=
    Equiv.sigmaCongrRight fun k ↦ F.retainedOpenEdgeEquiv k
  have hG0 := eG.symm_apply_apply sG
  have hG1heq :
      (F.retainedOpenEdgeEquiv (eG sG).1).symm (eG sG).2 ≍ sG.2 :=
    (Sigma.mk.inj_iff.mp hG0).2
  have hG1 :
      (F.retainedOpenEdgeEquiv (eG sG).1).symm (eG sG).2 = sG.2 := by
    simpa [eG] using eq_of_heq hG1heq
  have hG := congrFun hG1 ⟨A + 1 + i, by omega⟩
  have hG' :
      ((F.retainedOpenEdgeEquiv
        ((F.retainedCutEquiv A C).symm ⟨j, (l, r)⟩).1).symm
          ((F.retainedCutEquiv A C).symm ⟨j, (l, r)⟩).2
            ⟨A + 1 + i, by omega⟩) ≍
        (F.sectorCoordinateChainEquiv (A + C + 1) xG).2
          ⟨A + 1 + i, by omega⟩ := by
    apply heq_of_eq
    convert hG using 1 <;> simp [retainedCutEquiv, xG, sG, eG]; rfl
  dsimp only
  refine hG'.trans ?_
  have hR :
      ((F.rightFixedFiberOpenEdgeEquiv j
        (F.rightSectorOpenEdgeEquiv C j r).1).symm
          (F.rightSectorOpenEdgeEquiv C j r).2).2 i ≍
        (F.sectorCoordinateChainEquiv C xR).2 i := by
    let sR := F.sectorCoordinateChainEquiv C xR
    let tR : Σ k : Fin C → Fin F.sectorCount,
        Fin (F.rightDim j) × F.SectorChainFiber k := ⟨sR.1, (r.1, sR.2)⟩
    let eR : (Σ k : Fin C → Fin F.sectorCount,
        Fin (F.rightDim j) × F.SectorChainFiber k) ≃
        (Σ k : Fin C → Fin F.sectorCount,
          F.RightOpenEdgeIndex (F.rightSectorWord j k)) :=
      Equiv.sigmaCongrRight fun k ↦ F.rightFixedFiberOpenEdgeEquiv j k
    have hR0 := eR.symm_apply_apply tR
    have hR1heq :
        (F.rightFixedFiberOpenEdgeEquiv j (eR tR).1).symm (eR tR).2 ≍
          tR.2 := (Sigma.mk.inj_iff.mp hR0).2
    have hR1 :
        (F.rightFixedFiberOpenEdgeEquiv j (eR tR).1).symm (eR tR).2 =
          tR.2 := by
      simpa [eR] using eq_of_heq hR1heq
    have hR2 := congrFun (congrArg Prod.snd hR1) i
    apply heq_of_eq
    convert hR2 using 1 <;>
      simp [rightSectorOpenEdgeEquiv, xR, sR, tR, eR] <;> rfl
  refine (F.sectorCoordinateChainEquiv_apply_snd_heq (A + C + 1) xG
    ⟨A + 1 + i, by omega⟩).trans ?_
  refine HEq.trans ?_ hR.symm
  have hx : xG ⟨A + 1 + i, by omega⟩ = xR i := by
    simp [xG, sectorCoordinateMiddleEquiv, HayashiMarkov.sigmaAssoc,
      tripartiteSplitEquiv, blockSplitEquiv,
      show (⟨A + 1 + i, by omega⟩ : Fin (A + 1 + C)) =
        Fin.natAdd (A + 1) i by ext; simp,
      finSumFinEquiv_symm_apply_natAdd,
      Equiv.sumArrowEquivProdArrow_symm_apply_inr, xR]
  have he := congrArg F.sectorFinEquiv hx
  exact (Sigma.mk.inj_iff.mp he).2.trans
    (F.sectorCoordinateChainEquiv_apply_snd_heq C xR i).symm

/-- At the cut site, the retained-chain fiber coordinate is the pair of the
left and right boundary indices.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** This is the middle
dependent-coordinate identity for the restricted decomposition. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem retainedCutEquiv_symm_middle_fiber_heq
    (F : PhysicalSectorFactorization K) (A C : ℕ)
    (j : Fin F.sectorCount)
    (l : Fin (Fintype.card (SectorSiteIndex F) ^ A) × Fin (F.leftDim j))
    (r : Fin (F.rightDim j) × Fin (Fintype.card (SectorSiteIndex F) ^ C)) :
    let g := (F.retainedCutEquiv A C).symm ⟨j, (l, r)⟩
    ((F.retainedOpenEdgeEquiv g.1).symm g.2 ⟨A, by omega⟩) ≍
      (l.2, r.1) := by
  let xG : Fin (A + C + 1) → Fin (Fintype.card (SectorSiteIndex F)) :=
    ((finCongr (by omega)).arrowCongr (Equiv.refl _))
      ((tripartiteSplitEquiv (Fintype.card (SectorSiteIndex F)) A 1 C).symm
        (((Equiv.refl _).prodCongr
          (F.sectorCoordinateMiddleEquiv.symm.prodCongr (Equiv.refl _)))
            (HayashiMarkov.sigmaAssoc F.leftDim F.rightDim ⟨j, (l, r)⟩)))
  let sG := F.sectorCoordinateChainEquiv (A + C + 1) xG
  let eG : F.SectorChainIndex (A + C + 1) ≃
      (Σ k : Fin (A + C + 1) → Fin F.sectorCount,
        F.RetainedOpenEdgeIndex (n := A + C) k) :=
    Equiv.sigmaCongrRight fun k ↦ F.retainedOpenEdgeEquiv k
  have hG0 := eG.symm_apply_apply sG
  have hG1heq :
      (F.retainedOpenEdgeEquiv (eG sG).1).symm (eG sG).2 ≍ sG.2 :=
    (Sigma.mk.inj_iff.mp hG0).2
  have hG1 :
      (F.retainedOpenEdgeEquiv (eG sG).1).symm (eG sG).2 = sG.2 := by
    simpa [eG] using eq_of_heq hG1heq
  have hG := congrFun hG1 ⟨A, by omega⟩
  have hG' :
      ((F.retainedOpenEdgeEquiv
        ((F.retainedCutEquiv A C).symm ⟨j, (l, r)⟩).1).symm
          ((F.retainedCutEquiv A C).symm ⟨j, (l, r)⟩).2
            ⟨A, by omega⟩) ≍
        (F.sectorCoordinateChainEquiv (A + C + 1) xG).2
          ⟨A, by omega⟩ := by
    apply heq_of_eq
    convert hG using 1 <;> simp [retainedCutEquiv, xG, sG, eG]; rfl
  dsimp only
  refine hG'.trans ?_
  refine (F.sectorCoordinateChainEquiv_apply_snd_heq (A + C + 1) xG
    ⟨A, by omega⟩).trans ?_
  have hx : xG ⟨A, by omega⟩ =
      F.sectorFinEquiv.symm ⟨j, (l.2, r.1)⟩ := by
    simp [xG, sectorCoordinateMiddleEquiv, HayashiMarkov.sigmaAssoc,
      tripartiteSplitEquiv, blockSplitEquiv,
      show (⟨A, by omega⟩ : Fin (A + 1 + C)) =
        Fin.castAdd C (Fin.last A) by ext; simp,
      finSumFinEquiv_symm_apply_castAdd,
      Equiv.sumArrowEquivProdArrow_symm_apply_inl]
  have he := congrArg F.sectorFinEquiv hx
  have he' : F.sectorFinEquiv (xG ⟨A, by omega⟩) =
      ⟨j, (l.2, r.1)⟩ := by
    simpa using he
  exact (Sigma.mk.inj_iff.mp he').2


end MPOTensor.PhysicalSectorFactorization
