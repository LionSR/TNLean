/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorBondCommutativity
import TNLean.MPS.ParentHamiltonian.CyclicWindow

/-!
# Transport of adjacent physical-sector bonds

This file transports the fixed-sector adjacent-bond calculation through the
dependent direct sum of three physical sectors and then to the original
three-site physical coordinates.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, Proposition C.8, lines 1589--1593
-/

open scoped Matrix Kronecker

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

private theorem extractWindow_two_eq_zero_of_three {N : ℕ}
    (i : Fin N) (σ : Fin N → Fin d) :
    MPSTensor.extractWindow 2 i σ =
      MPSTensor.extractWindow 2 (0 : Fin 3) (MPSTensor.extractWindow 3 i σ) := by
  funext r
  fin_cases r <;> simp [MPSTensor.extractWindow, Nat.mod_eq_of_lt i.isLt]

private theorem extractWindow_two_finRotate_eq_one_of_three {N : ℕ}
    (i : Fin N) (σ : Fin N → Fin d) :
    MPSTensor.extractWindow 2 (finRotate N i) σ =
      MPSTensor.extractWindow 2 (1 : Fin 3) (MPSTensor.extractWindow 3 i σ) := by
  have hrot : (finRotate N i).val = (i.val + 1) % N := by
    simp [finRotate_apply, Fin.add_def]
  funext r
  apply congrArg σ
  apply Fin.ext
  fin_cases r
  · simp [Fin.add_def]
  · simp only [Fin.val_one, hrot]
    rw [Nat.mod_add_mod]

private theorem agreesOutsideWindow_two_zero_three_iff
    (σ τ : Fin 3 → Fin d) :
    AgreesOutsideWindow (d := d) 2 (by decide) (0 : Fin 3) σ τ ↔
      τ 2 = σ 2 := by
  rw [agreesOutsideWindow_iff]
  constructor
  · intro h
    exact h 2 (by decide)
  · intro h k hk
    fin_cases k
    · simp at hk
    · simp at hk
    · exact h

private theorem agreesOutsideWindow_two_one_three_iff
    (σ τ : Fin 3 → Fin d) :
    AgreesOutsideWindow (d := d) 2 (by decide) (1 : Fin 3) σ τ ↔
      τ 0 = σ 0 := by
  rw [agreesOutsideWindow_iff]
  constructor
  · intro h
    exact h 0 (by decide)
  · intro h k hk
    fin_cases k
    · exact h
    · simp at hk
    · simp at hk

private theorem offset_from_finRotate {N : ℕ} (hN : 2 ≤ N) (i k : Fin N) :
    (k.val + N - (finRotate N i).val) % N =
      if (k.val + N - i.val) % N = 0 then N - 1
      else (k.val + N - i.val) % N - 1 := by
  let r := (k.val + N - i.val) % N
  have hrN : r < N := Nat.mod_lt _ (by omega)
  have hrot : (finRotate N i).val = (i.val + 1) % N := by
    simp [finRotate_apply, Fin.add_def]
  by_cases hr : r = 0
  · have hk : k = i := by
      have hk' := MPSTensor.eq_cyclic_site_of_offset_eq (Fin.pos i) hr
      simpa [Nat.mod_eq_of_lt i.isLt] using hk'
    subst k
    rw [if_pos hr]
    by_cases hi : i.val + 1 < N
    · rw [hrot, Nat.mod_eq_of_lt hi]
      have heq : i.val + N - (i.val + 1) = N - 1 := by omega
      rw [heq, Nat.mod_eq_of_lt (by omega)]
    · have hiN : i.val + 1 = N := by omega
      rw [hrot, hiN, Nat.mod_self]
      simp only [Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
      omega
  · rw [if_neg hr]
    change (k.val + N - (finRotate N i).val) % N = r - 1
    have hk : k = ⟨((finRotate N i).val + (r - 1)) % N,
        Nat.mod_lt _ (by omega)⟩ := by
      have hk' := MPSTensor.eq_cyclic_site_of_offset_eq (Fin.pos i)
        (i := i) (k := k) (r := r) rfl
      apply Fin.ext
      change k.val = ((finRotate N i).val + (r - 1)) % N
      calc
        k.val = (i.val + r) % N := congrArg Fin.val hk'
        _ = (i.val + 1 + (r - 1)) % N := by congr 1; omega
        _ = ((i.val + 1) % N + (r - 1)) % N := by rw [Nat.mod_add_mod]
        _ = ((finRotate N i).val + (r - 1)) % N := by rw [hrot]
    rw [hk, MPSTensor.offset_mod_eq (finRotate N i).isLt (by omega : r - 1 < N)]

private theorem embedLocalOperator_two_zero_nested {N : ℕ} (hN : 3 ≤ N)
    (i : Fin N) (B : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ) :
    embedLocalOperator (d := d) 3 N (by omega) i
        (embedLocalOperator (d := d) 2 3 (by decide) (0 : Fin 3) B) =
      embedLocalOperator (d := d) 2 N (by omega) i B := by
  ext σ τ
  have hAgree :
      (AgreesOutsideWindow (d := d) 3 (by omega) i σ τ ∧
        AgreesOutsideWindow (d := d) 2 (by decide) (0 : Fin 3)
          (MPSTensor.extractWindow 3 i σ) (MPSTensor.extractWindow 3 i τ)) ↔
        AgreesOutsideWindow (d := d) 2 (by omega) i σ τ := by
    rw [agreesOutsideWindow_two_zero_three_iff]
    constructor
    · rintro ⟨h3, h2⟩
      rw [agreesOutsideWindow_iff] at h3 ⊢
      intro k hk2
      by_cases hk3 : (k.val + N - i.val) % N < 3
      · have hoff : (k.val + N - i.val) % N = 2 := by omega
        have hk := MPSTensor.eq_cyclic_site_of_offset_eq (Fin.pos i) hoff
        subst k
        simpa [MPSTensor.extractWindow, Nat.mod_eq_of_lt (by omega : 2 < N)] using h2
      · exact h3 k hk3
    · intro h2
      rw [agreesOutsideWindow_iff] at h2
      constructor
      · rw [agreesOutsideWindow_iff]
        intro k hk3
        exact h2 k (by omega)
      · apply h2
        change ¬ (((i.val + 2) % N + N - i.val) % N < 2)
        rw [MPSTensor.offset_mod_eq i.isLt (by omega : 2 < N)]
        omega
  simp only [embedLocalOperator_apply]
  rw [extractWindow_two_eq_zero_of_three i σ,
    extractWindow_two_eq_zero_of_three i τ]
  by_cases h3 : AgreesOutsideWindow (d := d) 3 (by omega) i σ τ
  · rw [if_pos h3]
    by_cases h2 : AgreesOutsideWindow (d := d) 2 (by decide) (0 : Fin 3)
        (MPSTensor.extractWindow 3 i σ) (MPSTensor.extractWindow 3 i τ)
    · rw [if_pos h2, if_pos (hAgree.mp ⟨h3, h2⟩)]
    · rw [if_neg h2, if_neg (fun h ↦ h2 (hAgree.mpr h).2)]
  · rw [if_neg h3, if_neg (fun h ↦ h3 (hAgree.mpr h).1)]

private theorem embedLocalOperator_two_one_nested {N : ℕ} (hN : 3 ≤ N)
    (i : Fin N) (B : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ) :
    embedLocalOperator (d := d) 3 N (by omega) i
        (embedLocalOperator (d := d) 2 3 (by decide) (1 : Fin 3) B) =
      embedLocalOperator (d := d) 2 N (by omega) (finRotate N i) B := by
  ext σ τ
  have hAgree :
      (AgreesOutsideWindow (d := d) 3 (by omega) i σ τ ∧
        AgreesOutsideWindow (d := d) 2 (by decide) (1 : Fin 3)
          (MPSTensor.extractWindow 3 i σ) (MPSTensor.extractWindow 3 i τ)) ↔
        AgreesOutsideWindow (d := d) 2 (by omega) (finRotate N i) σ τ := by
    rw [agreesOutsideWindow_two_one_three_iff]
    constructor
    · rintro ⟨h3, hlocal⟩
      rw [agreesOutsideWindow_iff] at h3 ⊢
      intro k hk
      let r := (k.val + N - i.val) % N
      have hoff := offset_from_finRotate (by omega : 2 ≤ N) i k
      by_cases hr : r = 0
      · have hki := MPSTensor.eq_cyclic_site_of_offset_eq (Fin.pos i)
          (i := i) (k := k) (r := r) rfl
        have hki' : k = i := by simpa [hr, Nat.mod_eq_of_lt i.isLt] using hki
        have hiEq : τ i = σ i := by
          simpa [MPSTensor.extractWindow, Nat.mod_eq_of_lt i.isLt] using hlocal
        simpa [hki'] using hiEq
      · apply h3 k
        change ¬ r < 3
        change ¬ ((k.val + N - (finRotate N i).val) % N < 2) at hk
        rw [hoff, if_neg hr] at hk
        omega
    · intro h2
      rw [agreesOutsideWindow_iff] at h2
      constructor
      · rw [agreesOutsideWindow_iff]
        intro k hk3
        apply h2 k
        let r := (k.val + N - i.val) % N
        have hoff := offset_from_finRotate (by omega : 2 ≤ N) i k
        have hr : r ≠ 0 := by
          change ¬ r < 3 at hk3
          omega
        rw [hoff, if_neg hr]
        change ¬ r < 3 at hk3
        omega
      · have hi := h2 i
        have hoff := offset_from_finRotate (by omega : 2 ≤ N) i i
        have hzero : (i.val + N - i.val) % N = 0 := by
          rw [show i.val + N - i.val = N by omega, Nat.mod_self]
        specialize hi (by rw [hoff, if_pos hzero]; omega)
        simpa [MPSTensor.extractWindow, Nat.mod_eq_of_lt i.isLt] using hi
  simp only [embedLocalOperator_apply]
  rw [extractWindow_two_finRotate_eq_one_of_three i σ,
    extractWindow_two_finRotate_eq_one_of_three i τ]
  by_cases h3 : AgreesOutsideWindow (d := d) 3 (by omega) i σ τ
  · rw [if_pos h3]
    by_cases h2 : AgreesOutsideWindow (d := d) 2 (by decide) (1 : Fin 3)
        (MPSTensor.extractWindow 3 i σ) (MPSTensor.extractWindow 3 i τ)
    · rw [if_pos h2, if_pos (hAgree.mp ⟨h3, h2⟩)]
    · rw [if_neg h2, if_neg (fun h ↦ h2 (hAgree.mpr h).2)]
  · rw [if_neg h3, if_neg (fun h ↦ h3 (hAgree.mpr h).1)]

/-- The first two sites extracted from the inverse three-site regrouping have
the expected two-site outer and neighboring coordinates.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
@[simp] private theorem twoSiteGlobalRegroupEquiv_firstTwo_threeSiteGlobalRegroupEquiv_symm
    (F : PhysicalSectorFactorization K)
    (k l h : Fin F.sectorCount)
    (x : BoundaryIndex F k h ×
      (NeighborIndex F k l × NeighborIndex F l h)) :
    F.twoSiteGlobalRegroupEquiv
        ((F.threeSiteGlobalRegroupEquiv.symm ⟨(k, (l, h)), x⟩).1,
          (F.threeSiteGlobalRegroupEquiv.symm ⟨(k, (l, h)), x⟩).2.1) =
      ⟨(k, l), ((x.1.1, x.2.2.1), x.2.1)⟩ := by
  rw [threeSiteGlobalRegroupEquiv_symm_apply]
  apply F.twoSiteGlobalRegroupEquiv.symm.injective
  rw [Equiv.symm_apply_apply, twoSiteGlobalRegroupEquiv_symm_apply]
  rfl

/-- The third site extracted from the inverse three-site regrouping consists
of the last neighboring left factor and the outer right factor.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
@[simp] private theorem threeSiteGlobalRegroupEquiv_symm_third
    (F : PhysicalSectorFactorization K)
    (k l h : Fin F.sectorCount)
    (x : BoundaryIndex F k h ×
      (NeighborIndex F k l × NeighborIndex F l h)) :
    (F.threeSiteGlobalRegroupEquiv.symm ⟨(k, (l, h)), x⟩).2.2 =
      F.sectorFinEquiv.symm ⟨h, (x.2.2.2, x.1.2)⟩ := by
  rw [threeSiteGlobalRegroupEquiv_symm_apply]
  rfl

/-- The last two sites extracted from the inverse three-site regrouping have
the expected two-site outer and neighboring coordinates.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
@[simp] private theorem twoSiteGlobalRegroupEquiv_lastTwo_threeSiteGlobalRegroupEquiv_symm
    (F : PhysicalSectorFactorization K)
    (k l h : Fin F.sectorCount)
    (x : BoundaryIndex F k h ×
      (NeighborIndex F k l × NeighborIndex F l h)) :
    F.twoSiteGlobalRegroupEquiv
        ((F.threeSiteGlobalRegroupEquiv.symm ⟨(k, (l, h)), x⟩).2.1,
          (F.threeSiteGlobalRegroupEquiv.symm ⟨(k, (l, h)), x⟩).2.2) =
      ⟨(l, h), ((x.2.1.2, x.1.2), x.2.2)⟩ := by
  rw [threeSiteGlobalRegroupEquiv_symm_apply]
  apply F.twoSiteGlobalRegroupEquiv.symm.injective
  rw [Equiv.symm_apply_apply, twoSiteGlobalRegroupEquiv_symm_apply]
  rfl

/-- The first site extracted from the inverse three-site regrouping consists
of the outer left factor and the first neighboring right factor.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
@[simp] private theorem threeSiteGlobalRegroupEquiv_symm_first_apply
    (F : PhysicalSectorFactorization K)
    (k l h : Fin F.sectorCount)
    (x : BoundaryIndex F k h ×
      (NeighborIndex F k l × NeighborIndex F l h)) :
    (F.threeSiteGlobalRegroupEquiv.symm ⟨(k, (l, h)), x⟩).1 =
      F.sectorFinEquiv.symm ⟨k, (x.1.1, x.2.1.1)⟩ := by
  rw [threeSiteGlobalRegroupEquiv_symm_apply]
  rfl

/-- The dependent direct sum obtained by regrouping all three-sector
summands into their outer and two neighboring factors.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
private abbrev ThreeSiteSectorBondIndex (F : PhysicalSectorFactorization K) :=
  Σ klh : Fin F.sectorCount × (Fin F.sectorCount × Fin F.sectorCount),
    BoundaryIndex F klh.1 klh.2.2 ×
      (NeighborIndex F klh.1 klh.2.1 × NeighborIndex F klh.2.1 klh.2.2)

/-- The first adjacent bond on the dependent direct sum of three physical
sectors.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
private noncomputable def threeSiteSectorLeftBond (F : PhysicalSectorFactorization K) :
    Matrix (ThreeSiteSectorBondIndex F) (ThreeSiteSectorBondIndex F) ℂ :=
  Matrix.blockDiagonal' fun klh ↦
    (1 : Matrix (BoundaryIndex F klh.1 klh.2.2)
      (BoundaryIndex F klh.1 klh.2.2) ℂ) ⊗ₖ
        (F.neighboringOperator klh.1 klh.2.1 ⊗ₖ
          (1 : Matrix (NeighborIndex F klh.2.1 klh.2.2)
            (NeighborIndex F klh.2.1 klh.2.2) ℂ))

/-- The second adjacent bond on the dependent direct sum of three physical
sectors.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
private noncomputable def threeSiteSectorRightBond (F : PhysicalSectorFactorization K) :
    Matrix (ThreeSiteSectorBondIndex F) (ThreeSiteSectorBondIndex F) ℂ :=
  Matrix.blockDiagonal' fun klh ↦
    (1 : Matrix (BoundaryIndex F klh.1 klh.2.2)
      (BoundaryIndex F klh.1 klh.2.2) ℂ) ⊗ₖ
        ((1 : Matrix (NeighborIndex F klh.1 klh.2.1)
          (NeighborIndex F klh.1 klh.2.1) ℂ) ⊗ₖ
            F.neighboringOperator klh.2.1 klh.2.2)

/-- The two adjacent bonds commute on the dependent direct sum of all
three-sector summands.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
private theorem threeSiteSectorBonds_comm (F : PhysicalSectorFactorization K) :
    F.threeSiteSectorLeftBond * F.threeSiteSectorRightBond =
      F.threeSiteSectorRightBond * F.threeSiteSectorLeftBond := by
  rw [threeSiteSectorLeftBond, threeSiteSectorRightBond,
    ← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
  congr
  funext klh
  exact F.adjacentSectorBonds_comm klh.1 klh.2.1 klh.2.2

/-- Regrouping the lift of the first two-site sector bond gives the dependent
direct sum of its fixed-sector actions.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
private theorem reindex_leftPairMatrix_sectorCoordinateBond
    (F : PhysicalSectorFactorization K) :
    Matrix.reindex F.threeSiteGlobalRegroupEquiv F.threeSiteGlobalRegroupEquiv
        (leftPairMatrix F.sectorCoordinateBond) =
      F.threeSiteSectorLeftBond := by
  ext ⟨klh, x⟩ ⟨pqr, y⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, leftPairMatrix]
  simp only [Matrix.kroneckerMap_apply, Equiv.prodAssoc_symm_apply]
  simp only [sectorCoordinateBond, Matrix.reindex_apply, Matrix.submatrix_apply]
  simp only [Equiv.symm_symm]
  rw [twoSiteGlobalRegroupEquiv_firstTwo_threeSiteGlobalRegroupEquiv_symm,
    twoSiteGlobalRegroupEquiv_firstTwo_threeSiteGlobalRegroupEquiv_symm,
    threeSiteGlobalRegroupEquiv_symm_third,
    threeSiteGlobalRegroupEquiv_symm_third]
  rcases klh with ⟨k, l, h⟩
  rcases pqr with ⟨p, q, r⟩
  by_cases hk : k = p
  · subst p
    by_cases hl : l = q
    · subst q
      by_cases hh : h = r
      · subst r
        simp [threeSiteSectorLeftBond, Matrix.one_apply, Prod.ext_iff]
        split_ifs <;> simp_all
      · simp [threeSiteSectorLeftBond, Matrix.blockDiagonal'_apply, hh,
          Matrix.one_apply]
    · simp [threeSiteSectorLeftBond, Matrix.blockDiagonal'_apply, hl]
  · simp [threeSiteSectorLeftBond, Matrix.blockDiagonal'_apply, hk]

/-- Regrouping the lift of the last two-site sector bond gives the dependent
direct sum of its fixed-sector actions.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
private theorem reindex_rightPairMatrix_sectorCoordinateBond
    (F : PhysicalSectorFactorization K) :
    Matrix.reindex F.threeSiteGlobalRegroupEquiv F.threeSiteGlobalRegroupEquiv
        (rightPairMatrix F.sectorCoordinateBond) =
      F.threeSiteSectorRightBond := by
  ext ⟨klh, x⟩ ⟨pqr, y⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, rightPairMatrix,
    Matrix.kroneckerMap_apply]
  simp only [sectorCoordinateBond, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm]
  rw [twoSiteGlobalRegroupEquiv_lastTwo_threeSiteGlobalRegroupEquiv_symm,
    twoSiteGlobalRegroupEquiv_lastTwo_threeSiteGlobalRegroupEquiv_symm,
    threeSiteGlobalRegroupEquiv_symm_first_apply,
    threeSiteGlobalRegroupEquiv_symm_first_apply]
  rcases klh with ⟨k, l, h⟩
  rcases pqr with ⟨p, q, r⟩
  by_cases hl : l = q
  · subst q
    by_cases hh : h = r
    · subst r
      by_cases hk : k = p
      · subst p
        simp [threeSiteSectorRightBond, Matrix.one_apply, Prod.ext_iff]
        split_ifs <;> simp_all
      · simp [threeSiteSectorRightBond, Matrix.blockDiagonal'_apply, hk,
          Matrix.one_apply]
    · simp [threeSiteSectorRightBond, Matrix.blockDiagonal'_apply, hh]
  · simp [threeSiteSectorRightBond, Matrix.blockDiagonal'_apply, hl]

/-- The first and second lifts of the complete two-site bond commute in
physical-sector coordinates.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
private theorem sectorCoordinatePairMatrices_comm
    (F : PhysicalSectorFactorization K) :
    leftPairMatrix F.sectorCoordinateBond *
        rightPairMatrix F.sectorCoordinateBond =
      rightPairMatrix F.sectorCoordinateBond *
        leftPairMatrix F.sectorCoordinateBond := by
  apply (Matrix.reindex F.threeSiteGlobalRegroupEquiv
    F.threeSiteGlobalRegroupEquiv).injective
  change (Matrix.reindexLinearEquiv ℂ ℂ F.threeSiteGlobalRegroupEquiv
      F.threeSiteGlobalRegroupEquiv)
        (leftPairMatrix F.sectorCoordinateBond *
          rightPairMatrix F.sectorCoordinateBond) =
    (Matrix.reindexLinearEquiv ℂ ℂ F.threeSiteGlobalRegroupEquiv
      F.threeSiteGlobalRegroupEquiv)
        (rightPairMatrix F.sectorCoordinateBond *
          leftPairMatrix F.sectorCoordinateBond)
  rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ F.threeSiteGlobalRegroupEquiv
      F.threeSiteGlobalRegroupEquiv F.threeSiteGlobalRegroupEquiv,
    ← Matrix.reindexLinearEquiv_mul ℂ ℂ F.threeSiteGlobalRegroupEquiv
      F.threeSiteGlobalRegroupEquiv F.threeSiteGlobalRegroupEquiv,
    Matrix.coe_reindexLinearEquiv,
    F.reindex_leftPairMatrix_sectorCoordinateBond,
    F.reindex_rightPairMatrix_sectorCoordinateBond,
    F.threeSiteSectorBonds_comm]

/-- The right-associated three-site product of the physical coordinate
matrix.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
private noncomputable def physicalCoordinateMatrixThree
    (F : PhysicalSectorFactorization K) :
    Matrix
      (Fin (Fintype.card (SectorSiteIndex F)) ×
        (Fin (Fintype.card (SectorSiteIndex F)) ×
          Fin (Fintype.card (SectorSiteIndex F))))
      (Fin d × (Fin d × Fin d)) ℂ :=
  F.physicalCoordinateMatrix ⊗ₖ
    (F.physicalCoordinateMatrix ⊗ₖ F.physicalCoordinateMatrix)

/-- The three-site physical coordinate matrix is a coisometry.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
private theorem physicalCoordinateMatrixThree_coisometry
    (F : PhysicalSectorFactorization K) :
    F.physicalCoordinateMatrixThree * F.physicalCoordinateMatrixThreeᴴ = 1 := by
  simp [physicalCoordinateMatrixThree, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, F.physicalCoordinateMatrix_coisometry]

/-- The second lifted physical bond is the three-site unitary transport of
the corresponding sector-coordinate lift.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
private theorem rightPairMatrix_physicalPairBond
    (F : PhysicalSectorFactorization K) :
    rightPairMatrix F.physicalPairBond =
      sandwichMap F.physicalCoordinateMatrixThreeᴴ
        (rightPairMatrix F.sectorCoordinateBond) := by
  simp [rightPairMatrix, physicalPairBond, sandwichMap_apply,
    physicalCoordinateMatrixTwo, physicalCoordinateMatrixThree,
    Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    F.physicalCoordinateMatrix_isometry, Matrix.mul_assoc]

/-- The first lifted physical bond is the three-site unitary transport of
the corresponding sector-coordinate lift.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
private theorem leftPairMatrix_physicalPairBond
    (F : PhysicalSectorFactorization K) :
    leftPairMatrix F.physicalPairBond =
      sandwichMap F.physicalCoordinateMatrixThreeᴴ
        (leftPairMatrix F.sectorCoordinateBond) := by
  ext x y
  simp only [sandwichMap_apply, Matrix.conjTranspose_conjTranspose]
  simp only [leftPairMatrix, physicalPairBond, physicalCoordinateMatrixTwo,
    physicalCoordinateMatrixThree, Matrix.conjTranspose_kronecker,
    Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.prodAssoc_symm_apply,
    Matrix.mul_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type]
  simp only [sandwichMap_apply, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_apply,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type]
  simp only [Matrix.one_apply]
  simp_rw [mul_ite, mul_one, mul_zero]
  simp only [Matrix.conjTranspose_apply, RCLike.star_def, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]
  let S : ℂ := ∑ a, ∑ b,
    (∑ c, ∑ e,
      star (F.physicalCoordinateMatrix c x.1) *
          star (F.physicalCoordinateMatrix e x.2.1) *
        F.sectorCoordinateBond (c, e) (a, b)) *
      (F.physicalCoordinateMatrix a y.1 *
        F.physicalCoordinateMatrix b y.2.1)
  have hthird :
      (∑ s, star (F.physicalCoordinateMatrix s x.2.2) *
        F.physicalCoordinateMatrix s y.2.2) =
        if x.2.2 = y.2.2 then 1 else 0 := by
    have h := congrFun (congrFun F.physicalCoordinateMatrix_isometry x.2.2) y.2.2
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using h
  have hfactor :
      (∑ a, ∑ b, ∑ s,
        (∑ c, ∑ e,
          star (F.physicalCoordinateMatrix c x.1) *
              (star (F.physicalCoordinateMatrix e x.2.1) *
                star (F.physicalCoordinateMatrix s x.2.2)) *
            F.sectorCoordinateBond (c, e) (a, b)) *
          (F.physicalCoordinateMatrix a y.1 *
            (F.physicalCoordinateMatrix b y.2.1 *
              F.physicalCoordinateMatrix s y.2.2))) =
        S * (∑ s, star (F.physicalCoordinateMatrix s x.2.2) *
          F.physicalCoordinateMatrix s y.2.2) := by
    dsimp [S]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    simp_rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro e _
    ring
  change (if x.2.2 = y.2.2 then S else 0) = _
  calc
    _ = S * (∑ s, star (F.physicalCoordinateMatrix s x.2.2) *
        F.physicalCoordinateMatrix s y.2.2) := by
      rw [hthird]
      by_cases hxy : x.2.2 = y.2.2 <;> simp [hxy]
    _ = _ := hfactor.symm

/-- The first and second lifts of the transported two-site bond commute on
the three-site physical tensor product.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
private theorem physicalPairBonds_comm (F : PhysicalSectorFactorization K) :
    leftPairMatrix F.physicalPairBond * rightPairMatrix F.physicalPairBond =
      rightPairMatrix F.physicalPairBond * leftPairMatrix F.physicalPairBond := by
  rw [F.leftPairMatrix_physicalPairBond, F.rightPairMatrix_physicalPairBond]
  simp only [sandwichMap_apply, Matrix.conjTranspose_conjTranspose]
  calc
    _ = F.physicalCoordinateMatrixThreeᴴ *
        leftPairMatrix F.sectorCoordinateBond *
        (F.physicalCoordinateMatrixThree * F.physicalCoordinateMatrixThreeᴴ) *
        rightPairMatrix F.sectorCoordinateBond *
        F.physicalCoordinateMatrixThree := by simp only [Matrix.mul_assoc]
    _ = F.physicalCoordinateMatrixThreeᴴ *
        (leftPairMatrix F.sectorCoordinateBond *
          rightPairMatrix F.sectorCoordinateBond) *
        F.physicalCoordinateMatrixThree := by
      rw [F.physicalCoordinateMatrixThree_coisometry]
      simp [Matrix.mul_assoc]
    _ = F.physicalCoordinateMatrixThreeᴴ *
        (rightPairMatrix F.sectorCoordinateBond *
          leftPairMatrix F.sectorCoordinateBond) *
        F.physicalCoordinateMatrixThree := by
      rw [F.sectorCoordinatePairMatrices_comm]
    _ = F.physicalCoordinateMatrixThreeᴴ *
        rightPairMatrix F.sectorCoordinateBond *
        (F.physicalCoordinateMatrixThree * F.physicalCoordinateMatrixThreeᴴ) *
        leftPairMatrix F.sectorCoordinateBond *
        F.physicalCoordinateMatrixThree := by
      rw [F.physicalCoordinateMatrixThree_coisometry]
      simp [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

/-- The two adjacent translates of the physical bond commute on a three-site
window.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
theorem physicalBond_zero_one_comm (F : PhysicalSectorFactorization K) :
    embedLocalOperator (d := d) 2 3 (by decide) (0 : Fin 3) F.physicalBond *
        embedLocalOperator (d := d) 2 3 (by decide) (1 : Fin 3) F.physicalBond =
      embedLocalOperator (d := d) 2 3 (by decide) (1 : Fin 3) F.physicalBond *
        embedLocalOperator (d := d) 2 3 (by decide) (0 : Fin 3) F.physicalBond := by
  apply (Matrix.reindex (_root_.finThreeArrowEquiv (Fin d))
    (_root_.finThreeArrowEquiv (Fin d))).injective
  change (Matrix.reindexLinearEquiv ℂ ℂ (_root_.finThreeArrowEquiv (Fin d))
      (_root_.finThreeArrowEquiv (Fin d))) (_ * _) =
    (Matrix.reindexLinearEquiv ℂ ℂ (_root_.finThreeArrowEquiv (Fin d))
      (_root_.finThreeArrowEquiv (Fin d))) (_ * _)
  rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ (_root_.finThreeArrowEquiv (Fin d))
      (_root_.finThreeArrowEquiv (Fin d)) (_root_.finThreeArrowEquiv (Fin d)),
    ← Matrix.reindexLinearEquiv_mul ℂ ℂ (_root_.finThreeArrowEquiv (Fin d))
      (_root_.finThreeArrowEquiv (Fin d)) (_root_.finThreeArrowEquiv (Fin d)),
    Matrix.coe_reindexLinearEquiv, F.reindex_embedLocalOperator_zero,
    F.reindex_embedLocalOperator_one, F.physicalPairBonds_comm]

/-- Adjacent translates of the physical bond commute on every periodic chain
of length at least three, including the pair crossing the periodic boundary.

The two-site chain is excluded because its two translated windows have the
same support with opposite cyclic order, rather than forming the three-site
configuration used in the source calculation.

**Scope restriction (N ≥ 3):** This theorem treats the three-site local
configuration and its embeddings.  The crossed-order case at `N = 2` is
supplied separately by `physicalBond_two_zero_one_comm`, as documented in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8, lines 1571--1593. -/
theorem physicalBond_adjacent_comm (F : PhysicalSectorFactorization K)
    {N : ℕ} (hN : 3 ≤ N) (i : Fin N) :
    embedLocalOperator (d := d) 2 N (by omega) i F.physicalBond *
        embedLocalOperator (d := d) 2 N (by omega) (finRotate N i) F.physicalBond =
      embedLocalOperator (d := d) 2 N (by omega) (finRotate N i) F.physicalBond *
        embedLocalOperator (d := d) 2 N (by omega) i F.physicalBond := by
  let P := embedLocalOperator (d := d) 2 3 (by decide) (0 : Fin 3) F.physicalBond
  let Q := embedLocalOperator (d := d) 2 3 (by decide) (1 : Fin 3) F.physicalBond
  calc
    _ = embedLocalOperator (d := d) 3 N (by omega) i P *
        embedLocalOperator (d := d) 3 N (by omega) i Q := by
      rw [embedLocalOperator_two_zero_nested, embedLocalOperator_two_one_nested]
    _ = embedLocalOperator (d := d) 3 N (by omega) i (P * Q) := by
      rw [embedLocalOperator_mul]
    _ = embedLocalOperator (d := d) 3 N (by omega) i (Q * P) := by
      rw [F.physicalBond_zero_one_comm]
    _ = embedLocalOperator (d := d) 3 N (by omega) i Q *
        embedLocalOperator (d := d) 3 N (by omega) i P := by
      rw [embedLocalOperator_mul]
    _ = _ := by
      rw [embedLocalOperator_two_zero_nested, embedLocalOperator_two_one_nested]

/-- Translates of the physical bond with disjoint cyclic supports commute.

This is the locality part of the pairwise commutation assertion in the source.
It requires no property of the sector factorization beyond the existence of its
two-site physical bond.  The adjacent, overlapping case is the separate content
of `physicalBond_adjacent_comm`.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8, lines
1571--1593. -/
theorem physicalBond_disjoint_comm (F : PhysicalSectorFactorization K)
    {N : ℕ} (hN : 2 ≤ N) {i j : Fin N}
    (hij : ¬ MPSTensor.cyclicWindowsOverlap N 2 i j) :
    embedLocalOperator (d := d) 2 N hN i F.physicalBond *
        embedLocalOperator (d := d) 2 N hN j F.physicalBond =
      embedLocalOperator (d := d) 2 N hN j F.physicalBond *
        embedLocalOperator (d := d) 2 N hN i F.physicalBond :=
  embedLocalOperator_commute_of_not_cyclicWindowsOverlap 2 N hN hij
    F.physicalBond F.physicalBond

end MPOTensor.PhysicalSectorFactorization
