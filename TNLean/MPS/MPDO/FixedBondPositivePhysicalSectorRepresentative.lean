/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.FixedBondProductEtaTensor

/-!
# Positive physical sectors of the selected fixed bond-product tensor

This file records the positive physical-sector factorization of the exact
fixed tensor selected for a positive translation-invariant commuting bond.
The reconstructed physical bond is the original bond, and every neighboring
operator is positive semidefinite.

No zero-correlation-length, saturation-of-the-area-law, normality, or blocking
statement is asserted.

## Main statement

* `TranslationInvariantBondData.exists_positive_physicalSectorFactorization_fixedProductTensorData`
  gives the factorization of the exact selected fixed-product tensor.

## References

* arXiv:1606.00608, Appendix C.2, equation `sigmaNK2`, lines 1581--1605.
* S. Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1 and Section III.
-/

open scoped ComplexOrder

namespace MPOTensor.TranslationInvariantBondData

variable {d : ℕ}

/-- The exact selected fixed-product tensor has a physical-sector
factorization whose reconstructed bond is the input bond and whose neighboring
operators are positive semidefinite.

This concerns the selected tensor itself, not merely another tensor with the
same closed operators.

**Scope restriction (fixed representative):** This does not construct a
factorization of an original MPDO tensor that is only proportional to the bond
product, and it does not compare normality or blocking.  The remaining
comparison is recorded in
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNK2`, lines
1581--1605; Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1 and Section III. -/
theorem exists_positive_physicalSectorFactorization_fixedProductTensorData
    (data : TranslationInvariantBondData d) :
    ∃ F : PhysicalSectorFactorization data.fixedProductTensorData.tensor,
      F.physicalBond = data.bond ∧
        ∀ q h, (F.neighboringOperator q h).PosSemidef :=
  ⟨data.fixedProductTensorDataPhysicalSectorFactorization,
    data.fixedProductTensorDataPhysicalSectorFactorization_physicalBond_eq,
    data.fixedProductTensorDataPhysicalSectorFactorization_neighboring_pos⟩

end MPOTensor.TranslationInvariantBondData
