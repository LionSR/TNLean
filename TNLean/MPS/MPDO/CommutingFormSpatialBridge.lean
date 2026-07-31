/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CommutingOverlappingCoordinates

/-!
# Unitary block actions for a fixed commuting bond

This file applies the spatial decomposition of Beigi's lemma to the pair-indexed bond
of a positive translation-invariant commuting family.

## Main declarations

* `MPOTensor.TranslationInvariantBondData.exists_unitary_blockActions_of_pairBond`
* `MPOTensor.EtaLocalStructureData.exists_unitary_blockActions_of_pairBond`

## References

* S. Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1.
* arXiv:1606.00608, Appendix C.2, lines 1597--1610.
-/

open scoped ComplexOrder Kronecker Matrix

namespace MPOTensor.TranslationInvariantBondData

variable {d : ℕ}

/-- The pair-indexed fixed bond admits the explicit unitary
block-action decomposition of Beigi's lemma.

Under the common three-site identification, the two abstract overlapping lifts are
precisely the first two adjacent translates of the original bond.

Source: arXiv:1606.00608, Appendix C.2, lines 1597--1610; Beigi,
J. Phys. A 45 (2012) 025306, Lemma 2.1. -/
theorem exists_unitary_blockActions_of_pairBond
    (data : TranslationInvariantBondData d) :
    ∃ (K : ℕ) (dl dr : Fin K → ℕ)
      (e : ((q : Fin K) × (Fin (dr q) × Fin (dl q))) ≃ Fin d)
      (U : Matrix (Fin d) (Fin d) ℂ)
      (R : ∀ q, Matrix (Fin d × Fin (dl q)) (Fin d × Fin (dl q)) ℂ)
      (S : ∀ q, Matrix (Fin (dr q) × Fin d) (Fin (dr q) × Fin d) ℂ),
      U ∈ Matrix.unitaryGroup (Fin d) ℂ ∧
        (∀ q, 0 < dl q) ∧ (∀ q, 0 < dr q) ∧
        (∀ q, (R q).IsHermitian) ∧ (∀ q, (S q).IsHermitian) ∧
        Matrix.reindex (Matrix.leftSpatialBlockEquiv e).symm
            (Matrix.leftSpatialBlockEquiv e).symm
            (star ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ U) * data.pairBond *
              ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ U)) =
          (Matrix.blockDiagonal' fun q =>
            R q ⊗ₖ (1 : Matrix (Fin (dr q)) (Fin (dr q)) ℂ)) ∧
        Matrix.reindex (Matrix.rightSpatialBlockEquiv e).symm
            (Matrix.rightSpatialBlockEquiv e).symm
            (star (U ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) * data.pairBond *
              (U ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ))) =
          (Matrix.blockDiagonal' fun q =>
            (1 : Matrix (Fin (dl q)) (Fin (dl q)) ℂ) ⊗ₖ S q) := by
  apply Matrix.exists_unitary_blockActions_of_overlappingLifts_commute
  · exact data.pairBond_isHermitian
  · exact data.pairBond_isHermitian
  · exact data.overlappingLifts_pairBond_comm

end MPOTensor.TranslationInvariantBondData

namespace MPOTensor.EtaLocalStructureData

variable {d D : ℕ} {M : MPOTensor d D}

/-- The pair-indexed bond carried by an eta-local structure admits the unitary block-action
decomposition of Beigi's lemma.

Source: arXiv:1606.00608, Appendix C.2, lines 1597--1610; Beigi,
J. Phys. A 45 (2012) 025306, Lemma 2.1. -/
theorem exists_unitary_blockActions_of_pairBond
    (data : EtaLocalStructureData M) :
    ∃ (K : ℕ) (dl dr : Fin K → ℕ)
      (e : ((q : Fin K) × (Fin (dr q) × Fin (dl q))) ≃ Fin d)
      (U : Matrix (Fin d) (Fin d) ℂ)
      (R : ∀ q, Matrix (Fin d × Fin (dl q)) (Fin d × Fin (dl q)) ℂ)
      (S : ∀ q, Matrix (Fin (dr q) × Fin d) (Fin (dr q) × Fin d) ℂ),
      U ∈ Matrix.unitaryGroup (Fin d) ℂ ∧
        (∀ q, 0 < dl q) ∧ (∀ q, 0 < dr q) ∧
        (∀ q, (R q).IsHermitian) ∧ (∀ q, (S q).IsHermitian) ∧
        Matrix.reindex (Matrix.leftSpatialBlockEquiv e).symm
            (Matrix.leftSpatialBlockEquiv e).symm
            (star ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ U) * data.pairBond *
              ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ U)) =
          (Matrix.blockDiagonal' fun q ↦
            R q ⊗ₖ (1 : Matrix (Fin (dr q)) (Fin (dr q)) ℂ)) ∧
        Matrix.reindex (Matrix.rightSpatialBlockEquiv e).symm
            (Matrix.rightSpatialBlockEquiv e).symm
            (star (U ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) * data.pairBond *
              (U ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ))) =
          (Matrix.blockDiagonal' fun q ↦
            (1 : Matrix (Fin (dl q)) (Fin (dl q)) ℂ) ⊗ₖ S q) := by
  exact data.bondData.exists_unitary_blockActions_of_pairBond

end MPOTensor.EtaLocalStructureData
