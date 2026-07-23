/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.RFP.NNCPHMultiSector
import TNLean.MPS.RFP.ResidualFamilyCommutation

/-!
# Nearest-neighbor commuting parent ground spaces for distinct RFP sectors

This file proves the forward nearest-neighbor commuting parent-Hamiltonian
ground-space condition for the multiplicity-one direct sum of the distinct
basis sectors of a BNT canonical form.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, Definition 3.9
  and Theorem 3.10, lines 517--541.
* Perez-Garcia--Verstraete--Wolf--Cirac, arXiv:quant-ph/0608197, Theorem 12,
  proof lines 1430--1456.
-/

namespace MPSTensor

namespace IsBNTCanonicalForm

variable {d : ℕ} {P : SectorDecomposition d}

/-- The multiplicity-one direct sum of the distinct sectors of an RFP BNT
canonical form satisfies the all-chain nearest-neighbor commuting
parent-Hamiltonian ground-space condition.

Source: arXiv:1606.00608, Definition 3.9 and Theorem 3.10, lines 517--541.
The ground-space spanning argument follows arXiv:quant-ph/0608197, Theorem 12,
proof lines 1430--1456.

**Scope restriction (multiplicity-one distinct sectors):** the theorem treats
the direct sum of the BNT basis tensors, with one copy of each distinct sector.
Repeated copies and arbitrary raw sector weights remain outside this statement;
see `docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`. -/
theorem rfp_implies_hasNNCPHGroundSpaces_basisDirectSum
    (hCF : IsBNTCanonicalForm P)
    (hRFP : IsTransferIdempotent (directSumTensor P.basis)) :
    HasNNCPHGroundSpaces (directSumTensor P.basis) P.basis := by
  rw [hasNNCPHGroundSpaces_iff_forall_isNNCPH_and_groundSpaceSpanning]
  exact
    ⟨fun N hN ↦ hCF.rfp_implies_nncph_basisDirectSum hRFP N hN,
      hCF.rfp_hasParentHamiltonianGroundSpaceSpanning_basisDirectSum hRFP⟩

end IsBNTCanonicalForm

end MPSTensor
