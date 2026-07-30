/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CommutingOverlappingDecomp
import TNLean.Algebra.FinTupleEquiv
import TNLean.MPS.MPDO.CommutingFormBridge

/-!
# Three-site coordinates for overlapping translates of a commuting bond

This file places the first two adjacent translates of one fixed positive commuting bond in the
abstract three-factor coordinates of the
Bravyi--Vyalyi decomposition.  One common equivalence identifies a three-site physical
configuration with a left-associated triple.  Under this equivalence, the translate on
sites zero and one is `Matrix.leftOverlappingLift`, while the translate on sites one and
two is `Matrix.rightOverlappingLift`, both formed from the same two-site bond matrix.

Positivity of the bond gives Hermiticity, and transporting the length-three bond
commutation through the common equivalence gives the remaining hypothesis of
`Matrix.exists_unitary_blockActions_of_overlappingLifts_commute`.

## Main declarations

* `MPOTensor.threeSiteOverlappingEquiv`
* `MPOTensor.pairBondMatrix`
* `MPOTensor.reindex_embedLocalOperator_zero_eq_leftOverlappingLift`
* `MPOTensor.reindex_embedLocalOperator_one_eq_rightOverlappingLift`
* `MPOTensor.TranslationInvariantBondData.overlappingLifts_pairBond_comm`
* `MPOTensor.EtaLocalStructureData.reindex_bondAt_zero_eq_leftOverlappingLift`
* `MPOTensor.EtaLocalStructureData.reindex_bondAt_one_eq_rightOverlappingLift`
* `MPOTensor.EtaLocalStructureData.overlappingLifts_pairBond_comm`

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, Proposition `4to2`, lines 1599--1605
* [Beigi 2012] J. Phys. A 45 (2012) 025306, Lemma 2.1 (`lem:comm`), pages 2--3
-/

open scoped Matrix ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

private theorem two_le_three : 2 ≤ 3 := by decide

/-- The common left-associated coordinates for three consecutive physical sites.  The
equivalence sends a configuration `x` to `((x 0, x 1), x 2)`, which is the index order
used simultaneously by `Matrix.leftOverlappingLift` and `Matrix.rightOverlappingLift`.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines 1599--1605;
Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1 (`lem:comm`), pages 2--3. -/
def threeSiteOverlappingEquiv (n : Type*) :
    (Fin 3 → n) ≃ ((n × n) × n) :=
  (_root_.finThreeArrowEquiv n).trans (Equiv.prodAssoc n n n).symm

/-- A two-site bond written on the product of its two physical indices.

Source: arXiv:1606.00608, Appendix C.2, equation `expression` and Proposition
`4to2`, lines 1571--1576 and 1599--1605. -/
def pairBondMatrix (B : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.reindex (finTwoArrowEquiv (Fin d)) (finTwoArrowEquiv (Fin d)) B

/-- In the common left-associated three-site coordinates, a two-site operator embedded
at site zero is its left overlapping lift.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines 1599--1605;
Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1 (`lem:comm`), pages 2--3. -/
theorem reindex_embedLocalOperator_zero_eq_leftOverlappingLift
    (B : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ) :
    Matrix.reindex (threeSiteOverlappingEquiv (Fin d))
        (threeSiteOverlappingEquiv (Fin d))
        (embedLocalOperator (d := d) 2 3 two_le_three (0 : Fin 3) B) =
      Matrix.leftOverlappingLift (pairBondMatrix B) := by
  ext ⟨⟨i, j⟩, k⟩ ⟨⟨i', j'⟩, k'⟩
  have hAgree :
      AgreesOutsideWindow (d := d) 2 two_le_three (0 : Fin 3)
          ((threeSiteOverlappingEquiv (Fin d)).symm ((i, j), k))
          ((threeSiteOverlappingEquiv (Fin d)).symm ((i', j'), k')) ↔
        k' = k := by
    constructor
    · intro ha
      have h := congrFun ha (2 : Fin 3)
      simpa [AgreesOutsideWindow, threeSiteOverlappingEquiv,
        MPSTensor.replaceWindow, MPSTensor.extractWindow] using h
    · intro hk
      funext r
      fin_cases r <;>
        simp [threeSiteOverlappingEquiv, MPSTensor.replaceWindow,
          MPSTensor.extractWindow, hk]
  by_cases h : k' = k
  · have ha := hAgree.mpr h
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
      embedLocalOperator_apply]
    rw [if_pos ha]
    subst k'
    simp only [MPSTensor.extractWindow, threeSiteOverlappingEquiv,
      Equiv.symm_trans, Equiv.symm_symm, Fin.isValue,
      Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add, Equiv.trans_apply,
      Equiv.prodAssoc_apply, finThreeArrowEquiv_symm_apply,
      Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.leftOverlappingLift,
      pairBondMatrix, finTwoArrowEquiv, Equiv.toFun_as_coe,
      piFinTwoEquiv_apply, Matrix.reindex_apply, Equiv.symm_mk,
      Equiv.coe_fn_mk, Matrix.submatrix_apply, Matrix.one_apply_eq, mul_one]
    have hx : (fun r : Fin 2 => ![i, j, k]
        ⟨r.val % 3, Nat.mod_lt _ (by decide)⟩) = ![i, j] := by
      funext r
      fin_cases r <;> rfl
    have hy : (fun r : Fin 2 => ![i', j', k]
        ⟨r.val % 3, Nat.mod_lt _ (by decide)⟩) = ![i', j'] := by
      funext r
      fin_cases r <;> rfl
    rw [hx, hy]
  · have ha : ¬ AgreesOutsideWindow (d := d) 2 two_le_three (0 : Fin 3)
        ((threeSiteOverlappingEquiv (Fin d)).symm ((i, j), k))
        ((threeSiteOverlappingEquiv (Fin d)).symm ((i', j'), k')) :=
      fun ha ↦ h (hAgree.mp ha)
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
      embedLocalOperator_apply]
    rw [if_neg ha]
    have hk : k ≠ k' := fun hk ↦ h hk.symm
    simp [Matrix.leftOverlappingLift, hk]

/-- In the same common left-associated three-site coordinates, a two-site operator
embedded at site one is its right overlapping lift.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines 1599--1605;
Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1 (`lem:comm`), pages 2--3. -/
theorem reindex_embedLocalOperator_one_eq_rightOverlappingLift
    (B : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ) :
    Matrix.reindex (threeSiteOverlappingEquiv (Fin d))
        (threeSiteOverlappingEquiv (Fin d))
        (embedLocalOperator (d := d) 2 3 two_le_three (1 : Fin 3) B) =
      Matrix.rightOverlappingLift (pairBondMatrix B) := by
  ext ⟨⟨i, j⟩, k⟩ ⟨⟨i', j'⟩, k'⟩
  have hAgree :
      AgreesOutsideWindow (d := d) 2 two_le_three (1 : Fin 3)
          ((threeSiteOverlappingEquiv (Fin d)).symm ((i, j), k))
          ((threeSiteOverlappingEquiv (Fin d)).symm ((i', j'), k')) ↔
        i' = i := by
    constructor
    · intro ha
      have h := congrFun ha (0 : Fin 3)
      simpa [AgreesOutsideWindow, threeSiteOverlappingEquiv,
        MPSTensor.replaceWindow, MPSTensor.extractWindow] using h
    · intro hi
      funext r
      fin_cases r <;>
        simp [threeSiteOverlappingEquiv, MPSTensor.replaceWindow,
          MPSTensor.extractWindow, hi]
  by_cases h : i' = i
  · have ha := hAgree.mpr h
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
      embedLocalOperator_apply]
    rw [if_pos ha]
    subst i'
    simp only [MPSTensor.extractWindow, threeSiteOverlappingEquiv,
      Equiv.symm_trans, Equiv.symm_symm, Fin.isValue,
      Fin.coe_ofNat_eq_mod, Nat.one_mod, Equiv.trans_apply,
      Equiv.prodAssoc_apply, finThreeArrowEquiv_symm_apply,
      Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.rightOverlappingLift,
      Matrix.one_apply_eq, pairBondMatrix, finTwoArrowEquiv,
      Equiv.toFun_as_coe, piFinTwoEquiv_apply, Matrix.reindex_apply,
      Equiv.symm_mk, Equiv.coe_fn_mk, Matrix.submatrix_apply, one_mul]
    have hx : (fun r : Fin 2 => ![i, j, k]
        ⟨(1 + r.val) % 3, Nat.mod_lt _ (by decide)⟩) = ![j, k] := by
      funext r
      fin_cases r <;> rfl
    have hy : (fun r : Fin 2 => ![i, j', k']
        ⟨(1 + r.val) % 3, Nat.mod_lt _ (by decide)⟩) = ![j', k'] := by
      funext r
      fin_cases r <;> rfl
    rw [hx, hy]
  · have ha : ¬ AgreesOutsideWindow (d := d) 2 two_le_three (1 : Fin 3)
        ((threeSiteOverlappingEquiv (Fin d)).symm ((i, j), k))
        ((threeSiteOverlappingEquiv (Fin d)).symm ((i', j'), k')) :=
      fun ha ↦ h (hAgree.mp ha)
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
      embedLocalOperator_apply]
    rw [if_neg ha]
    have hi : i ≠ i' := fun hi ↦ h hi.symm
    simp [Matrix.rightOverlappingLift, hi]

namespace TranslationInvariantBondData

variable {d : ℕ}

/-- A fixed two-site bond written on an ordered pair of physical indices.

Source: arXiv:1606.00608, Appendix C.2, equation `expression` and Proposition
`4to2`, lines 1571--1576 and 1599--1605. -/
def pairBond (data : TranslationInvariantBondData d) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  pairBondMatrix data.bond

/-- The pair-indexed bond is Hermitian because the fixed bond is positive semidefinite.

Source: arXiv:1606.00608, Appendix C.2, equation `expression`, lines 1571--1576. -/
theorem pairBond_isHermitian (data : TranslationInvariantBondData d) :
    data.pairBond.IsHermitian := by
  exact data.bond_pos.isHermitian.reindex (finTwoArrowEquiv (Fin d))

/-- The first adjacent translate is the left overlapping lift under the common three-site
equivalence.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines 1599--1605;
Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1 (`lem:comm`), pages 2--3. -/
theorem reindex_bondAt_zero_eq_leftOverlappingLift
    (data : TranslationInvariantBondData d) :
    Matrix.reindex (threeSiteOverlappingEquiv (Fin d))
        (threeSiteOverlappingEquiv (Fin d))
        ((data.toCommutingFormData two_le_three).bondAt (0 : Fin 3)) =
      Matrix.leftOverlappingLift data.pairBond := by
  exact reindex_embedLocalOperator_zero_eq_leftOverlappingLift data.bond

/-- The second adjacent translate is the right overlapping lift under the same three-site
equivalence.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines 1599--1605;
Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1 (`lem:comm`), pages 2--3. -/
theorem reindex_bondAt_one_eq_rightOverlappingLift
    (data : TranslationInvariantBondData d) :
    Matrix.reindex (threeSiteOverlappingEquiv (Fin d))
        (threeSiteOverlappingEquiv (Fin d))
        ((data.toCommutingFormData two_le_three).bondAt (1 : Fin 3)) =
      Matrix.rightOverlappingLift data.pairBond := by
  exact reindex_embedLocalOperator_one_eq_rightOverlappingLift data.bond

/-- The two abstract overlapping lifts of the pair-indexed fixed bond commute. Thus, together
with Hermiticity, they satisfy the hypotheses of Beigi's spatial decomposition.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines 1599--1605;
Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1 (`lem:comm`), pages 2--3. -/
theorem overlappingLifts_pairBond_comm (data : TranslationInvariantBondData d) :
    Matrix.leftOverlappingLift data.pairBond *
        Matrix.rightOverlappingLift data.pairBond =
      Matrix.rightOverlappingLift data.pairBond *
        Matrix.leftOverlappingLift data.pairBond := by
  rw [← data.reindex_bondAt_zero_eq_leftOverlappingLift,
    ← data.reindex_bondAt_one_eq_rightOverlappingLift]
  change (Matrix.reindexLinearEquiv ℂ ℂ (threeSiteOverlappingEquiv (Fin d))
      (threeSiteOverlappingEquiv (Fin d)))
        ((data.toCommutingFormData two_le_three).bondAt 0) *
      (Matrix.reindexLinearEquiv ℂ ℂ (threeSiteOverlappingEquiv (Fin d))
        (threeSiteOverlappingEquiv (Fin d)))
          ((data.toCommutingFormData two_le_three).bondAt 1) =
    (Matrix.reindexLinearEquiv ℂ ℂ (threeSiteOverlappingEquiv (Fin d))
      (threeSiteOverlappingEquiv (Fin d)))
        ((data.toCommutingFormData two_le_three).bondAt 1) *
      (Matrix.reindexLinearEquiv ℂ ℂ (threeSiteOverlappingEquiv (Fin d))
        (threeSiteOverlappingEquiv (Fin d)))
          ((data.toCommutingFormData two_le_three).bondAt 0)
  rw [Matrix.reindexLinearEquiv_mul ℂ ℂ (threeSiteOverlappingEquiv (Fin d))
      (threeSiteOverlappingEquiv (Fin d)) (threeSiteOverlappingEquiv (Fin d)),
    Matrix.reindexLinearEquiv_mul ℂ ℂ (threeSiteOverlappingEquiv (Fin d))
      (threeSiteOverlappingEquiv (Fin d)) (threeSiteOverlappingEquiv (Fin d))]
  exact congrArg (Matrix.reindex (threeSiteOverlappingEquiv (Fin d))
    (threeSiteOverlappingEquiv (Fin d)))
    (data.bond_comm two_le_three (0 : Fin 3) (1 : Fin 3))

end TranslationInvariantBondData

namespace EtaLocalStructureData

variable {M : MPOTensor d D}

/-- The chain-independent bond of an eta-local structure, written on an ordered pair of
physical indices.

Source: arXiv:1606.00608, Appendix C.2, equation `expression` and Proposition
`4to2`, lines 1571--1576 and 1599--1605. -/
def pairBond (data : EtaLocalStructureData M) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  data.bondData.pairBond

/-- The pair-indexed bond is Hermitian because the source bond is positive semidefinite.

Source: arXiv:1606.00608, Appendix C.2, equation `expression`, lines 1571--1576. -/
theorem pairBond_isHermitian (data : EtaLocalStructureData M) :
    data.pairBond.IsHermitian := by
  exact data.bondData.pairBond_isHermitian

/-- The first adjacent translate of the eta-local bond is the left overlapping lift under
the common three-site equivalence.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines 1599--1605;
Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1 (`lem:comm`), pages 2--3. -/
theorem reindex_bondAt_zero_eq_leftOverlappingLift
    (data : EtaLocalStructureData M) :
    Matrix.reindex (threeSiteOverlappingEquiv (Fin d))
        (threeSiteOverlappingEquiv (Fin d))
        ((data.formAt 3 two_le_three).bondAt (0 : Fin 3)) =
      Matrix.leftOverlappingLift data.pairBond := by
  exact data.bondData.reindex_bondAt_zero_eq_leftOverlappingLift

/-- The second adjacent translate of the eta-local bond is the right overlapping lift
under the same three-site equivalence.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines 1599--1605;
Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1 (`lem:comm`), pages 2--3. -/
theorem reindex_bondAt_one_eq_rightOverlappingLift
    (data : EtaLocalStructureData M) :
    Matrix.reindex (threeSiteOverlappingEquiv (Fin d))
        (threeSiteOverlappingEquiv (Fin d))
        ((data.formAt 3 two_le_three).bondAt (1 : Fin 3)) =
      Matrix.rightOverlappingLift data.pairBond := by
  exact data.bondData.reindex_bondAt_one_eq_rightOverlappingLift

/-- The two abstract overlapping lifts of the pair-indexed eta-local bond commute.  Thus,
together with `pairBond_isHermitian`, they satisfy exactly the hypotheses of
`Matrix.exists_unitary_blockActions_of_overlappingLifts_commute`.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines 1599--1605;
Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1 (`lem:comm`), pages 2--3. -/
theorem overlappingLifts_pairBond_comm (data : EtaLocalStructureData M) :
    Matrix.leftOverlappingLift data.pairBond *
        Matrix.rightOverlappingLift data.pairBond =
      Matrix.rightOverlappingLift data.pairBond *
        Matrix.leftOverlappingLift data.pairBond := by
  exact data.bondData.overlappingLifts_pairBond_comm

end EtaLocalStructureData
end MPOTensor
