/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.RFP.NNCPHGroundSpacesMultiSector
import TNLean.MPS.RFP.ZCLReverse

/-!
# Conditional zero-correlation-length implication for commuting parent ground spaces

This file proves the corrected positive-gap implication from zero correlation
length to nearest-neighbor commuting parent-Hamiltonian ground spaces for the
multiplicity-one unit-weight representative.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, Theorem 3.10,
  lines 534--541, and its proof in Appendix B, lines 1248--1268.
-/

namespace MPSTensor

namespace IsBNTCanonicalForm

variable {d : ℕ} {P : SectorDecomposition d}

/-- Positive-gap BNT zero correlation length implies the all-chain
nearest-neighbor commuting parent-Hamiltonian ground-space condition at the
multiplicity-one representative, under the normalized nonzero subleading
spectral-pair assertion used in CPSV16.

This is the conditional corrected implication (ii) to (iii) of
arXiv:1606.00608, Theorem `thm:main-MPS`, lines 534--541. It first applies the
conditional reverse argument of lines 1248--1268 and then the fixed-point
ground-space theorem.

**Scope restriction (multiplicity-one unit weights and CPSV16 line 1250):**
the tensor is the direct sum of the distinct BNT basis tensors with one
unit-weight copy each, and every non-idempotent block is assumed to have the
normalized nonzero subleading left/right eigenpair asserted at line 1250. The
theorem does not derive that assertion or establish the printed three-way
equivalence. See
`docs/paper-gaps/cpsv16_pure_zcl_local_orthogonality_scope.tex`. -/
theorem isPositiveGapBNTZCL_implies_hasNNCPHGroundSpaces_basisDirectSum_of_spectral_pair
    (hCF : IsBNTCanonicalForm P)
    (hspectral : ∀ j : Fin P.basisCount,
      ¬ IsTransferIdempotent (P.basis j) →
        ∃ (ν : ℂ) (r l : Matrix (Fin (P.basisDim j)) (Fin (P.basisDim j)) ℂ),
          ν ≠ 0 ∧ ‖ν‖ < 1 ∧
          Module.End.HasEigenvector (transferMap (P.basis j)) ν r ∧
          Module.End.HasEigenvector
            (Matrix.traceAdjointMap (transferMap (P.basis j))) ν l ∧
          Matrix.trace (l * r) = 1)
    (hZCL : IsPositiveGapBNTZCL (directSumTensor P.basis) P.basis) :
    HasNNCPHGroundSpaces (directSumTensor P.basis) P.basis :=
  hCF.rfp_implies_hasNNCPHGroundSpaces_basisDirectSum
    (hCF.isTransferIdempotent_basisDirectSum_of_isPositiveGapBNTZCL_of_spectral_pair
      hspectral hZCL)

end IsBNTCanonicalForm

end MPSTensor
