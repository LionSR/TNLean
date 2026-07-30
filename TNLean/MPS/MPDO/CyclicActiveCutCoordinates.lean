/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.HayashiMarkovStructure
import TNLean.MPS.MPDO.CyclicActiveMarkovNormalization

/-!
# Coordinates for cyclic-active one-site cuts

This file constructs the dependent left, middle, and right coordinate
equivalences for separating a retained chain at an arbitrary one-site cut.

## Reference

* arXiv:1606.00608, Appendix C.2, Proposition 4to2, lines 1606--1617.
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

namespace MPOTensor.PhysicalSectorFactorization

universe u

variable {d D : ℕ} {K : MPOTensor d D}

/-- The left boundary factor produced by the separated two-step
coefficient.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** The sum is restricted to
cyclic-active sectors. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
noncomputable def cyclicActiveLeftBoundary
    (F : PhysicalSectorFactorization K)
    (b : F.CyclicActiveSector → ℝ) (kFirst : F.CyclicActiveSector) :
    Matrix (Fin (F.leftDim kFirst)) (Fin (F.leftDim kFirst)) ℂ :=
  ∑ h, ((b h : ℂ) •
    Matrix.partialTraceLeft (F.neighboringOperator h kFirst))

/-- The right boundary factor produced by the separated two-step
coefficient.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** The sum is restricted to
cyclic-active sectors. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
noncomputable def cyclicActiveRightBoundary
    (F : PhysicalSectorFactorization K)
    (a : F.CyclicActiveSector → ℝ) (kLast : F.CyclicActiveSector) :
    Matrix (Fin (F.rightDim kLast)) (Fin (F.rightDim kLast)) ℂ :=
  ∑ q, ((a q : ℂ) •
    Matrix.partialTraceRight (F.neighboringOperator kLast q))

/-- Nonnegative boundary weights make the left cyclic-active boundary factor
positive semidefinite.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** Positivity is proved after
restricting the boundary sum to cyclic-active sectors. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem cyclicActiveLeftBoundary_posSemidef
    (F : PhysicalSectorFactorization K)
    (hpos : ∀ q h, (F.neighboringOperator q h).PosSemidef)
    (b : F.CyclicActiveSector → ℝ) (hb : ∀ h, 0 ≤ b h)
    (kFirst : F.CyclicActiveSector) :
    (F.cyclicActiveLeftBoundary b kFirst).PosSemidef := by
  classical
  apply Matrix.posSemidef_sum Finset.univ
  intro h hh
  exact (hpos h kFirst).partialTraceLeft.smul
    (a := (b h : ℂ)) (by exact_mod_cast hb h)

/-- Nonnegative boundary weights make the right cyclic-active boundary factor
positive semidefinite.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** Positivity is proved after
restricting the boundary sum to cyclic-active sectors. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem cyclicActiveRightBoundary_posSemidef
    (F : PhysicalSectorFactorization K)
    (hpos : ∀ q h, (F.neighboringOperator q h).PosSemidef)
    (a : F.CyclicActiveSector → ℝ) (ha : ∀ q, 0 ≤ a q)
    (kLast : F.CyclicActiveSector) :
    (F.cyclicActiveRightBoundary a kLast).PosSemidef := by
  classical
  apply Matrix.posSemidef_sum Finset.univ
  intro q hq
  exact (hpos kLast q).partialTraceRight.smul
    (a := (a q : ℂ)) (by exact_mod_cast ha q)

/-- The separated cyclic-active boundary is the Kronecker product of its
right and left factors.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** Both factors come from the
restricted two-step coefficient. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem cyclicActiveSeparatedBoundary_eq_right_kronecker_left
    (F : PhysicalSectorFactorization K)
    (a b : F.CyclicActiveSector → ℝ)
    (kFirst kLast : F.CyclicActiveSector) :
    F.cyclicActiveSeparatedBoundary a b kFirst kLast =
      F.cyclicActiveRightBoundary a kLast ⊗ₖ
        F.cyclicActiveLeftBoundary b kFirst := by
  rfl

/-- Open-edge indices to the left of a distinguished final site.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** These coordinates describe the
retained left path in the restricted decomposition. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
abbrev LeftOpenEdgeIndex (F : PhysicalSectorFactorization K) {A : ℕ}
    (k : Fin (A + 1) → Fin F.sectorCount) :=
  Fin (F.leftDim (k 0)) ×
    ((i : Fin A) → F.NeighborIndex (k i.castSucc) (k i.succ))

/-- Regroup the site factors preceding a distinguished final site into its
left boundary coordinate and the intervening neighboring edges.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** This identification is used for
the retained left path in the restricted decomposition. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
def leftFiberOpenEdgeEquiv (F : PhysicalSectorFactorization K) {A : ℕ}
    (k : Fin (A + 1) → Fin F.sectorCount) :
    (((i : Fin A) → F.SectorIndex (k i.castSucc)) ×
      Fin (F.leftDim (k (Fin.last A)))) ≃ F.LeftOpenEdgeIndex k := by
  cases A with
  | zero =>
      exact {
        toFun := fun x ↦ (x.2, finZeroElim)
        invFun := fun z ↦ (finZeroElim, z.1)
        left_inv := by
          rintro ⟨x, l⟩
          apply Prod.ext
          · funext i; exact Fin.elim0 i
          · rfl
        right_inv := by
          rintro ⟨l, z⟩
          apply Prod.ext
          · rfl
          · funext i; exact Fin.elim0 i }
  | succ n =>
      exact {
        toFun := fun x ↦
          ((x.1 0).1, fun i ↦ ((x.1 i).2,
            Fin.lastCases x.2 (fun p ↦ (x.1 p.succ).1) i))
        invFun := fun z ↦
          (fun i ↦ (Fin.cases z.1 (fun p ↦ (z.2 p.castSucc).2) i, (z.2 i).1),
            (z.2 (Fin.last n)).2)
        left_inv := by
          rintro ⟨x, l⟩
          apply Prod.ext
          · funext i
            apply Prod.ext
            · apply Fin.ext
              cases i using Fin.cases <;> simp
            · rfl
          · apply Fin.ext
            simp
        right_inv := by
          rintro ⟨l, z⟩
          apply Prod.ext
          · apply Fin.ext
            simp
          · funext i
            apply Prod.ext
            · rfl
            · apply Fin.ext
              cases i using Fin.lastCases <;> simp }

/-- Open-edge indices to the right of a distinguished initial site.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** These coordinates describe the
retained right path in the restricted decomposition. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
abbrev RightOpenEdgeIndex (F : PhysicalSectorFactorization K) {C : ℕ}
    (k : Fin (C + 1) → Fin F.sectorCount) :=
  ((i : Fin C) → F.NeighborIndex (k i.castSucc) (k i.succ)) ×
    Fin (F.rightDim (k (Fin.last C)))

/-- Regroup the site factors following a distinguished initial site into the
intervening neighboring edges and its right boundary coordinate.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** This identification is used for
the retained right path in the restricted decomposition. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
def rightFiberOpenEdgeEquiv (F : PhysicalSectorFactorization K) {C : ℕ}
    (k : Fin (C + 1) → Fin F.sectorCount) :
    (Fin (F.rightDim (k 0)) ×
      ((i : Fin C) → F.SectorIndex (k i.succ))) ≃ F.RightOpenEdgeIndex k := by
  cases C with
  | zero =>
      exact {
        toFun := fun x ↦ (finZeroElim, x.1)
        invFun := fun z ↦ (z.2, finZeroElim)
        left_inv := by
          rintro ⟨r, x⟩
          apply Prod.ext
          · rfl
          · funext i; exact Fin.elim0 i
        right_inv := by
          rintro ⟨z, r⟩
          apply Prod.ext
          · funext i; exact Fin.elim0 i
          · rfl }
  | succ n =>
      exact {
        toFun := fun x ↦
          (fun i ↦ (Fin.cases x.1 (fun p ↦ (x.2 p.castSucc).2) i, (x.2 i).1),
            (x.2 (Fin.last n)).2)
        invFun := fun z ↦
          ((z.1 0).1, fun i ↦ ((z.1 i).2,
            Fin.lastCases z.2 (fun p ↦ (z.1 p.succ).1) i))
        left_inv := by
          rintro ⟨r, x⟩
          apply Prod.ext
          · apply Fin.ext
            simp
          · funext i
            apply Prod.ext
            · rfl
            · apply Fin.ext
              cases i using Fin.lastCases <;> simp
        right_inv := by
          rintro ⟨z, r⟩
          apply Prod.ext
          · funext i
            apply Prod.ext
            · apply Fin.ext
              cases i using Fin.cases <;> simp
            · rfl
          · apply Fin.ext
            simp }

/-- The one-site sector decomposition in the sector-coordinate physical
basis.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** The middle-site coordinates are
those of the retained sector decomposition. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
noncomputable def sectorCoordinateMiddleEquiv
    (F : PhysicalSectorFactorization K) :
    Fin (Fintype.card (SectorSiteIndex F) ^ 1) ≃
      Σ j : Fin F.sectorCount, Fin (F.leftDim j) × Fin (F.rightDim j) :=
  ((Equiv.funUnique (Fin 1) (Fin (Fintype.card (SectorSiteIndex F)))).symm.trans
    finFunctionFinEquiv).symm.trans F.sectorFinEquiv

/-- The sector component of a chain coordinate at a site is the sector of
the corresponding physical coordinate.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** This identity supplies the sector
coordinates for the retained decomposition. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
@[simp] theorem sectorCoordinateChainEquiv_apply_fst
    (F : PhysicalSectorFactorization K) (N : ℕ)
    (x : Fin N → Fin (Fintype.card (SectorSiteIndex F))) (i : Fin N) :
    (F.sectorCoordinateChainEquiv N x).1 i = (F.sectorFinEquiv (x i)).1 := by
  let s := F.sectorCoordinateChainEquiv N x
  have h := F.sectorCoordinateChainEquiv_symm_apply N s.1 s.2 i
  rw [show (F.sectorCoordinateChainEquiv N).symm s = x by
    exact (F.sectorCoordinateChainEquiv N).symm_apply_apply x] at h
  have he := congrArg F.sectorFinEquiv h
  simpa [s] using (congrArg Sigma.fst he).symm

/-- The fiber component of a chain coordinate at a site agrees with the fiber
of the corresponding physical coordinate.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** This identity supplies the
dependent fiber coordinates for the retained decomposition. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem sectorCoordinateChainEquiv_apply_snd_heq
    (F : PhysicalSectorFactorization K) (N : ℕ)
    (x : Fin N → Fin (Fintype.card (SectorSiteIndex F))) (i : Fin N) :
    (F.sectorCoordinateChainEquiv N x).2 i ≍
      (F.sectorFinEquiv (x i)).2 := by
  let s := F.sectorCoordinateChainEquiv N x
  have h := F.sectorCoordinateChainEquiv_symm_apply N s.1 s.2 i
  rw [show (F.sectorCoordinateChainEquiv N).symm s = x by
    exact (F.sectorCoordinateChainEquiv N).symm_apply_apply x] at h
  have he := congrArg F.sectorFinEquiv h
  have he' : F.sectorFinEquiv (x i) = ⟨s.1 i, s.2 i⟩ := by
    simpa using he
  change s.2 i ≍ (F.sectorFinEquiv (x i)).2
  exact (Sigma.mk.inj_iff.mp he').2.symm

/-- Adjoin a distinguished final sector to a sector word.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** The resulting word indexes a
retained left path in the restricted decomposition. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
def leftSectorWord (F : PhysicalSectorFactorization K) {A : ℕ}
    (j : Fin F.sectorCount) (k : Fin A → Fin F.sectorCount) :
    Fin (A + 1) → Fin F.sectorCount :=
  Fin.lastCases j k

/-- Adjoin a distinguished initial sector to a sector word.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** The resulting word indexes a
retained right path in the restricted decomposition. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
def rightSectorWord (F : PhysicalSectorFactorization K) {C : ℕ}
    (j : Fin F.sectorCount) (k : Fin C → Fin F.sectorCount) :
    Fin (C + 1) → Fin F.sectorCount :=
  Fin.cases j k

/-- Regroup a fixed left sector fiber and the distinguished middle-left factor
into left open-edge coordinates.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** This is the left fiber
identification for the retained decomposition. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
def leftFixedFiberOpenEdgeEquiv
    (F : PhysicalSectorFactorization K) {A : ℕ}
    (j : Fin F.sectorCount) (k : Fin A → Fin F.sectorCount) :
    (F.SectorChainFiber k × Fin (F.leftDim j)) ≃
      F.LeftOpenEdgeIndex (F.leftSectorWord j k) := by
  let eFiber : F.SectorChainFiber k ≃
      ((i : Fin A) → F.SectorIndex (F.leftSectorWord j k i.castSucc)) :=
    Equiv.piCongrRight fun i ↦ Equiv.cast <| by simp [leftSectorWord]
  exact (eFiber.prodCongr (Equiv.cast (by simp [leftSectorWord]))).trans
    (F.leftFiberOpenEdgeEquiv (A := A) (F.leftSectorWord j k))

/-- Regroup the distinguished middle-right factor and a fixed right sector
fiber into right open-edge coordinates.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** This is the right fiber
identification for the retained decomposition. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
def rightFixedFiberOpenEdgeEquiv
    (F : PhysicalSectorFactorization K) {C : ℕ}
    (j : Fin F.sectorCount) (k : Fin C → Fin F.sectorCount) :
    (Fin (F.rightDim j) × F.SectorChainFiber k) ≃
      F.RightOpenEdgeIndex (F.rightSectorWord j k) := by
  simpa only [SectorChainFiber, rightSectorWord, Fin.cases_zero,
    Fin.cases_succ] using
      F.rightFiberOpenEdgeEquiv (C := C) (F.rightSectorWord j k)

/-- The left physical configurations and the middle left factor, regrouped
as a direct sum of left open-edge configurations.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** The direct sum is the left side of
the retained cut decomposition. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
noncomputable def leftSectorOpenEdgeEquiv
    (F : PhysicalSectorFactorization K) (A : ℕ) (j : Fin F.sectorCount) :
    (Fin (Fintype.card (SectorSiteIndex F) ^ A) × Fin (F.leftDim j)) ≃
      Σ k : Fin A → Fin F.sectorCount, F.LeftOpenEdgeIndex (F.leftSectorWord j k) :=
  (finFunctionFinEquiv.symm.prodCongr (Equiv.refl _)).trans <|
    ((F.sectorCoordinateChainEquiv A).prodCongr (Equiv.refl _)).trans <|
      (Equiv.sigmaProdDistrib
        (fun k : Fin A → Fin F.sectorCount ↦ F.SectorChainFiber k)
        (Fin (F.leftDim j))).trans <|
        Equiv.sigmaCongrRight fun k : Fin A → Fin F.sectorCount ↦
          F.leftFixedFiberOpenEdgeEquiv j k

/-- The middle right factor and right physical configurations, regrouped as
a direct sum of right open-edge configurations.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** The direct sum is the right side
of the retained cut decomposition. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
noncomputable def rightSectorOpenEdgeEquiv
    (F : PhysicalSectorFactorization K) (C : ℕ) (j : Fin F.sectorCount) :
    (Fin (F.rightDim j) × Fin (Fintype.card (SectorSiteIndex F) ^ C)) ≃
      Σ k : Fin C → Fin F.sectorCount, F.RightOpenEdgeIndex (F.rightSectorWord j k) :=
  ((Equiv.refl _).prodCongr finFunctionFinEquiv.symm).trans <|
    ((Equiv.refl _).prodCongr (F.sectorCoordinateChainEquiv C)).trans <|
      (Equiv.prodComm _ _).trans <|
        (Equiv.sigmaProdDistrib
          (fun k : Fin C → Fin F.sectorCount ↦ F.SectorChainFiber k)
          (Fin (F.rightDim j))).trans <|
          (Equiv.sigmaCongrRight fun k : Fin C → Fin F.sectorCount ↦
            Equiv.prodComm (F.SectorChainFiber k) (Fin (F.rightDim j))).trans <|
            Equiv.sigmaCongrRight fun k : Fin C → Fin F.sectorCount ↦
              F.rightFixedFiberOpenEdgeEquiv j k

/-- The sector word of the left open-edge identification is the sector word
of the left physical chain.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** This projection identifies the
left retained-sector word. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
@[simp] theorem leftSectorOpenEdgeEquiv_apply_fst
    (F : PhysicalSectorFactorization K) (A : ℕ) (j : Fin F.sectorCount)
    (l : Fin (Fintype.card (SectorSiteIndex F) ^ A) × Fin (F.leftDim j)) :
    (F.leftSectorOpenEdgeEquiv A j l).1 =
      (F.sectorCoordinateChainEquiv A (finFunctionFinEquiv.symm l.1)).1 := by
  rfl

/-- The sector word of the right open-edge identification is the sector word
of the right physical chain.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** This projection identifies the
right retained-sector word. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
@[simp] theorem rightSectorOpenEdgeEquiv_apply_fst
    (F : PhysicalSectorFactorization K) (C : ℕ) (j : Fin F.sectorCount)
    (r : Fin (F.rightDim j) × Fin (Fintype.card (SectorSiteIndex F) ^ C)) :
    (F.rightSectorOpenEdgeEquiv C j r).1 =
      (F.sectorCoordinateChainEquiv C (finFunctionFinEquiv.symm r.2)).1 := by
  rfl

/-- The inverse left open-edge identification recovers the left chain fiber
and the middle-left boundary coordinate.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** This dependent-coordinate identity
is used in the retained cut decomposition. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem leftSectorOpenEdgeEquiv_symm_fiber_heq
    (F : PhysicalSectorFactorization K) (A : ℕ) (j : Fin F.sectorCount)
    (l : Fin (Fintype.card (SectorSiteIndex F) ^ A) × Fin (F.leftDim j)) :
    let s := F.leftSectorOpenEdgeEquiv A j l
    (F.leftFixedFiberOpenEdgeEquiv j s.1).symm s.2 ≍
      ((F.sectorCoordinateChainEquiv A (finFunctionFinEquiv.symm l.1)).2,
        l.2) := by
  let sL := F.sectorCoordinateChainEquiv A (finFunctionFinEquiv.symm l.1)
  let tL : Σ k : Fin A → Fin F.sectorCount,
      F.SectorChainFiber k × Fin (F.leftDim j) := ⟨sL.1, (sL.2, l.2)⟩
  let eL : (Σ k : Fin A → Fin F.sectorCount,
      F.SectorChainFiber k × Fin (F.leftDim j)) ≃
      (Σ k : Fin A → Fin F.sectorCount,
        F.LeftOpenEdgeIndex (F.leftSectorWord j k)) :=
    Equiv.sigmaCongrRight fun k ↦ F.leftFixedFiberOpenEdgeEquiv j k
  have hL0 := eL.symm_apply_apply tL
  have hL1 :
      (F.leftFixedFiberOpenEdgeEquiv j (eL tL).1).symm (eL tL).2 ≍
        tL.2 := (Sigma.mk.inj_iff.mp hL0).2
  convert hL1 using 1;
    simp [leftSectorOpenEdgeEquiv, sL, tL, eL]; rfl

/-- The inverse right open-edge identification recovers the middle-right
boundary coordinate and the right chain fiber.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** This dependent-coordinate identity
is used in the retained cut decomposition. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem rightSectorOpenEdgeEquiv_symm_fiber_heq
    (F : PhysicalSectorFactorization K) (C : ℕ) (j : Fin F.sectorCount)
    (r : Fin (F.rightDim j) ×
      Fin (Fintype.card (SectorSiteIndex F) ^ C)) :
    let s := F.rightSectorOpenEdgeEquiv C j r
    (F.rightFixedFiberOpenEdgeEquiv j s.1).symm s.2 ≍
      (r.1, (F.sectorCoordinateChainEquiv C
        (finFunctionFinEquiv.symm r.2)).2) := by
  let sR := F.sectorCoordinateChainEquiv C (finFunctionFinEquiv.symm r.2)
  let tR : Σ k : Fin C → Fin F.sectorCount,
      Fin (F.rightDim j) × F.SectorChainFiber k := ⟨sR.1, (r.1, sR.2)⟩
  let eR : (Σ k : Fin C → Fin F.sectorCount,
      Fin (F.rightDim j) × F.SectorChainFiber k) ≃
      (Σ k : Fin C → Fin F.sectorCount,
        F.RightOpenEdgeIndex (F.rightSectorWord j k)) :=
    Equiv.sigmaCongrRight fun k ↦ F.rightFixedFiberOpenEdgeEquiv j k
  have hR0 := eR.symm_apply_apply tR
  have hR1 :
      (F.rightFixedFiberOpenEdgeEquiv j (eR tR).1).symm (eR tR).2 ≍
        tR.2 := (Sigma.mk.inj_iff.mp hR0).2
  convert hR1 using 1;
    simp [rightSectorOpenEdgeEquiv, sR, tR, eR]; rfl

/-- The inverse left open-edge identification recovers the prescribed
middle-left boundary coordinate.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** This endpoint identity belongs to
the retained cut decomposition. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem leftSectorOpenEdgeEquiv_symm_last_eq
    (F : PhysicalSectorFactorization K) (A : ℕ) (j : Fin F.sectorCount)
    (l : Fin (Fintype.card (SectorSiteIndex F) ^ A) × Fin (F.leftDim j)) :
    let s := F.leftSectorOpenEdgeEquiv A j l
    ((F.leftFixedFiberOpenEdgeEquiv j s.1).symm s.2).2 = l.2 := by
  let sL := F.sectorCoordinateChainEquiv A (finFunctionFinEquiv.symm l.1)
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
        tL.2 := by simpa [eL] using eq_of_heq hL1heq
  have hL2 := congrArg Prod.snd hL1
  convert hL2 using 1;
    simp [leftSectorOpenEdgeEquiv, sL, tL, eL]; rfl

/-- The inverse right open-edge identification recovers the prescribed
middle-right boundary coordinate.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** This endpoint identity belongs to
the retained cut decomposition. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem rightSectorOpenEdgeEquiv_symm_first_eq
    (F : PhysicalSectorFactorization K) (C : ℕ) (j : Fin F.sectorCount)
    (r : Fin (F.rightDim j) ×
      Fin (Fintype.card (SectorSiteIndex F) ^ C)) :
    let s := F.rightSectorOpenEdgeEquiv C j r
    ((F.rightFixedFiberOpenEdgeEquiv j s.1).symm s.2).1 = r.1 := by
  let sR := F.sectorCoordinateChainEquiv C (finFunctionFinEquiv.symm r.2)
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
        tR.2 := by simpa [eR] using eq_of_heq hR1heq
  have hR2 := congrArg Prod.fst hR1
  convert hR2 using 1;
    simp [rightSectorOpenEdgeEquiv, sR, tR, eR]; rfl

/-- The site coordinate recovered from a left open edge agrees with the site
coordinate recovered in the fixed-sector fiber.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** This dependent-coordinate identity
is used for retained left paths. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem leftFiberOpenEdgeEquiv_symm_fst_heq
    (F : PhysicalSectorFactorization K) {A : ℕ}
    (j : Fin F.sectorCount) (k : Fin A → Fin F.sectorCount)
    (z : F.LeftOpenEdgeIndex (F.leftSectorWord j k)) (i : Fin A) :
    let u := (F.leftFiberOpenEdgeEquiv (F.leftSectorWord j k)).symm z
    let w := (F.leftFixedFiberOpenEdgeEquiv j k).symm z
    u.1 i ≍ w.1 i := by
  unfold leftFixedFiberOpenEdgeEquiv
  exact (cast_heq _ _).symm

/-- The final boundary coordinate recovered from a left open edge agrees with
the boundary coordinate in the fixed-sector fiber.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** This dependent-coordinate identity
is used for retained left paths. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem leftFiberOpenEdgeEquiv_symm_snd_heq
    (F : PhysicalSectorFactorization K) {A : ℕ}
    (j : Fin F.sectorCount) (k : Fin A → Fin F.sectorCount)
    (z : F.LeftOpenEdgeIndex (F.leftSectorWord j k)) :
    let u := (F.leftFiberOpenEdgeEquiv (F.leftSectorWord j k)).symm z
    let w := (F.leftFixedFiberOpenEdgeEquiv j k).symm z
    u.2 ≍ w.2 := by
  unfold leftFixedFiberOpenEdgeEquiv
  exact (cast_heq _ _).symm

/-- The initial boundary coordinate recovered from a right open edge agrees
with the boundary coordinate in the fixed-sector fiber.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** This dependent-coordinate identity
is used for retained right paths. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem rightFiberOpenEdgeEquiv_symm_fst_heq
    (F : PhysicalSectorFactorization K) {C : ℕ}
    (j : Fin F.sectorCount) (k : Fin C → Fin F.sectorCount)
    (z : F.RightOpenEdgeIndex (F.rightSectorWord j k)) :
    let u := (F.rightFiberOpenEdgeEquiv (F.rightSectorWord j k)).symm z
    let w := (F.rightFixedFiberOpenEdgeEquiv j k).symm z
    u.1 ≍ w.1 := by
  simp [rightFixedFiberOpenEdgeEquiv]
  rfl

/-- The site coordinate recovered from a right open edge agrees with the site
coordinate recovered in the fixed-sector fiber.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** This dependent-coordinate identity
is used for retained right paths. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem rightFiberOpenEdgeEquiv_symm_snd_heq
    (F : PhysicalSectorFactorization K) {C : ℕ}
    (j : Fin F.sectorCount) (k : Fin C → Fin F.sectorCount)
    (z : F.RightOpenEdgeIndex (F.rightSectorWord j k)) (i : Fin C) :
    let u := (F.rightFiberOpenEdgeEquiv (F.rightSectorWord j k)).symm z
    let w := (F.rightFixedFiberOpenEdgeEquiv j k).symm z
    u.2 i ≍ w.2 i := by
  simp [rightFixedFiberOpenEdgeEquiv]
  rfl

/-- Along a left open path, the left endpoint of an edge is the right site
coordinate at the same position.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** This projection describes retained
left-path coordinates. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
@[simp] theorem leftFiberOpenEdgeEquiv_symm_edge_fst
    (F : PhysicalSectorFactorization K) {A : ℕ}
    (k : Fin (A + 1) → Fin F.sectorCount)
    (z : F.LeftOpenEdgeIndex k) (i : Fin A) :
    (((F.leftFiberOpenEdgeEquiv k).symm z).1 i).2 = (z.2 i).1 := by
  cases A with
  | zero => exact Fin.elim0 i
  | succ A => simp [leftFiberOpenEdgeEquiv]

/-- A left path of zero length has its open-edge boundary as its sole boundary
coordinate.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** This endpoint identity covers the
empty retained left path. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
@[simp] theorem leftFiberOpenEdgeEquiv_symm_boundary_zero
    (F : PhysicalSectorFactorization K)
    (k : Fin 1 → Fin F.sectorCount) (z : F.LeftOpenEdgeIndex k) :
    ((F.leftFiberOpenEdgeEquiv k).symm z).2 = z.1 := by
  rfl

/-- For a nonempty left path, the open-edge boundary is its first left site
coordinate.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** This endpoint identity describes a
retained left path. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
@[simp] theorem leftFiberOpenEdgeEquiv_symm_boundary_succ
    (F : PhysicalSectorFactorization K) {A : ℕ}
    (k : Fin (A + 2) → Fin F.sectorCount) (z : F.LeftOpenEdgeIndex k) :
    (((F.leftFiberOpenEdgeEquiv k).symm z).1 0).1 = z.1 := by
  simp [leftFiberOpenEdgeEquiv]

/-- Before the last site of a left path, the right endpoint of an edge is the
next left site coordinate.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** This projection describes retained
left-path coordinates. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
@[simp] theorem leftFiberOpenEdgeEquiv_symm_edge_snd_castSucc
    (F : PhysicalSectorFactorization K) {A : ℕ}
    (k : Fin (A + 2) → Fin F.sectorCount)
    (z : F.LeftOpenEdgeIndex k) (i : Fin A) :
    (((F.leftFiberOpenEdgeEquiv k).symm z).1 i.succ).1 =
      (z.2 i.castSucc).2 := by
  simp [leftFiberOpenEdgeEquiv]

/-- At the last site of a left path, the right endpoint of the final edge is
the middle-left boundary coordinate.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** This endpoint identity describes a
retained left path. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
@[simp] theorem leftFiberOpenEdgeEquiv_symm_edge_snd_last
    (F : PhysicalSectorFactorization K) {A : ℕ}
    (k : Fin (A + 2) → Fin F.sectorCount)
    (z : F.LeftOpenEdgeIndex k) :
    ((F.leftFiberOpenEdgeEquiv k).symm z).2 =
      (z.2 (Fin.last A)).2 := by
  simp [leftFiberOpenEdgeEquiv]

/-- At the first site of a right path, the left endpoint of the first edge is
the middle-right boundary coordinate.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** This endpoint identity describes a
retained right path. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
@[simp] theorem rightFiberOpenEdgeEquiv_symm_edge_fst_zero
    (F : PhysicalSectorFactorization K) {C : ℕ}
    (k : Fin (C + 2) → Fin F.sectorCount)
    (z : F.RightOpenEdgeIndex k) :
    ((F.rightFiberOpenEdgeEquiv k).symm z).1 = (z.1 0).1 := by
  simp [rightFiberOpenEdgeEquiv]

/-- A right path of zero length has its open-edge boundary as its sole boundary
coordinate.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** This endpoint identity covers the
empty retained right path. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
@[simp] theorem rightFiberOpenEdgeEquiv_symm_boundary_zero
    (F : PhysicalSectorFactorization K)
    (k : Fin 1 → Fin F.sectorCount) (z : F.RightOpenEdgeIndex k) :
    ((F.rightFiberOpenEdgeEquiv k).symm z).1 = z.2 := by
  rfl

/-- For a nonempty right path, the open-edge boundary is its final right site
coordinate.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** This endpoint identity describes a
retained right path. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
@[simp] theorem rightFiberOpenEdgeEquiv_symm_boundary_succ
    (F : PhysicalSectorFactorization K) {C : ℕ}
    (k : Fin (C + 2) → Fin F.sectorCount) (z : F.RightOpenEdgeIndex k) :
    (((F.rightFiberOpenEdgeEquiv k).symm z).2 (Fin.last C)).2 = z.2 := by
  simp [rightFiberOpenEdgeEquiv]

/-- After the first site of a right path, the left endpoint of an edge is the
preceding right site coordinate.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** This projection describes retained
right-path coordinates. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
@[simp] theorem rightFiberOpenEdgeEquiv_symm_edge_fst_succ
    (F : PhysicalSectorFactorization K) {C : ℕ}
    (k : Fin (C + 2) → Fin F.sectorCount)
    (z : F.RightOpenEdgeIndex k) (i : Fin C) :
    (((F.rightFiberOpenEdgeEquiv k).symm z).2 i.castSucc).2 =
      (z.1 i.succ).1 := by
  simp [rightFiberOpenEdgeEquiv]

/-- Along a right open path, the right endpoint of an edge is the left site
coordinate at the same position.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** This projection describes retained
right-path coordinates. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
@[simp] theorem rightFiberOpenEdgeEquiv_symm_edge_snd
    (F : PhysicalSectorFactorization K) {C : ℕ}
    (k : Fin (C + 1) → Fin F.sectorCount)
    (z : F.RightOpenEdgeIndex k) (i : Fin C) :
    (((F.rightFiberOpenEdgeEquiv k).symm z).2 i).1 = (z.1 i).2 := by
  cases C with
  | zero => exact Fin.elim0 i
  | succ C => simp [rightFiberOpenEdgeEquiv]


end MPOTensor.PhysicalSectorFactorization
