/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CommutingFormBridge
import TNLean.MPS.MPDO.PhysicalSectorProductTransport

/-!
# Eta-local structure from a positive physical-sector factorization

A physical-sector factorization with positive neighboring contractions
determines the positive translation-invariant bond of Proposition C.8. The
exact finite-chain product identity realizes every periodic MPO with scalar
one, and hence gives `MPOTensor.EtaLocalStructureData`.

## Main declaration

* `PhysicalSectorFactorization.etaLocalStructureData`

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, Proposition C.8, lines 1571--1593
-/

open scoped ComplexOrder

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

/-- A physical-sector factorization whose neighboring contractions are
positive semidefinite determines the eta-local commuting product structure.
The normalization scalar at every chain length is one.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1571--1593.

**Scope restriction (given physical-sector factorization):** Proposition
`3to4` assumes SAL (arXiv:1606.00608, Appendix C.2, Proposition C.8, lines
1571--1593); positivity of the neighboring operators is obtained in the
preceding Lemma `propSN`, lines 1441--1450. The present declaration instead
takes both the physical-sector factorization and this positivity as
hypotheses. The source-faithful implication is
`MPOTensor.nonempty_etaLocalStructureData_of_isSAL`; see
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`. -/
noncomputable def etaLocalStructureData
    (F : PhysicalSectorFactorization K)
    (hη : ∀ k h, (F.neighboringOperator k h).PosSemidef) :
    EtaLocalStructureData K where
  bondData := F.translationInvariantBondData hη
  realizes_mpo := by
    intro N hN
    refine ⟨1, by norm_num, ?_⟩
    norm_num
    change mpo K N =
      (List.ofFn fun i : Fin N ↦
        embedLocalOperator (d := d) 2 N hN i F.physicalBond).prod
    exact F.mpo_eq_product_physicalBond hN

end MPOTensor.PhysicalSectorFactorization
