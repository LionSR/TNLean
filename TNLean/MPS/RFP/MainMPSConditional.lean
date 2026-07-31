/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.RFP.NNCPHGroundSpacesMultiSector
import TNLean.MPS.RFP.BeigiLoopBNTIdentification
import TNLean.MPS.RFP.ZCLReverse

/-!
# Fixed-point, zero-correlation-length, and commuting-ground-space equivalences

This file proves the corrected equivalences among transfer idempotence,
positive-gap BNT zero correlation length, and nearest-neighbor commuting
parent-Hamiltonian ground spaces for the multiplicity-one unit-weight
representative. It also retains the conditional spectral-pair implication.

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

/-- Positive-gap BNT zero correlation length implies the all-chain
nearest-neighbor commuting parent-Hamiltonian ground-space condition at the
multiplicity-one, unit-weight representative.

**Local fix (arXiv:1606.00608, line 1250):** the implication first uses the
eigenvalue-free trace-pairing repair to obtain transfer idempotence and then
applies the multiplicity-one fixed-point ground-space theorem. It does not
establish the printed three-way equivalence, treat raw weighted repeated
copies, or include adjacent complementary gaps. See
`docs/paper-gaps/cpsv16_pure_zcl_local_orthogonality_scope.tex`. -/
theorem isPositiveGapBNTZCL_implies_hasNNCPHGroundSpaces_basisDirectSum
    (hCF : IsBNTCanonicalForm P)
    (hZCL : IsPositiveGapBNTZCL (directSumTensor P.basis) P.basis) :
    HasNNCPHGroundSpaces (directSumTensor P.basis) P.basis :=
  hCF.rfp_implies_hasNNCPHGroundSpaces_basisDirectSum
    (hCF.isTransferIdempotent_basisDirectSum_of_isPositiveGapBNTZCL hZCL)

/-- Transfer idempotence is equivalent to the all-chain nearest-neighbor
commuting parent-Hamiltonian ground-space condition for the direct sum of the
distinct BNT basis tensors.

This is the corrected representative-level equivalence between conditions
(i) and (iii) of CPSV16, Theorem `thm:main-MPS`, lines 534--541; the reverse
argument is at lines 1305--1307.

**Scope restriction (multiplicity-one unit weights):** the tensor is
`directSumTensor P.basis`, with one unit-weight copy of each distinct BNT
basis tensor. The statement does not cover repeated copies or arbitrary raw
weights. See `docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`. -/
theorem isTransferIdempotent_basisDirectSum_iff_hasNNCPHGroundSpaces
    (hCF : IsBNTCanonicalForm P) :
    IsTransferIdempotent (directSumTensor P.basis) ↔
      HasNNCPHGroundSpaces (directSumTensor P.basis) P.basis :=
  ⟨hCF.rfp_implies_hasNNCPHGroundSpaces_basisDirectSum,
    hCF.isTransferIdempotent_basisDirectSum_of_hasNNCPHGroundSpaces⟩

/-- Positive-gap BNT zero correlation length is equivalent to the all-chain
nearest-neighbor commuting parent-Hamiltonian ground-space condition for the
direct sum of the distinct BNT basis tensors.

This is the corrected representative-level equivalence between conditions
(ii) and (iii) of CPSV16, Theorem `thm:main-MPS`, lines 534--541; the
positive-gap repair concerns lines 1248--1268, and the reverse NNCPH argument
is at lines 1305--1307.

**Scope restriction (multiplicity-one unit weights and positive gaps):** the
tensor is `directSumTensor P.basis`, with one unit-weight copy of each distinct
BNT basis tensor, and the correlation condition excludes adjacent
complementary regions. The statement does not cover repeated copies or
arbitrary raw weights. See
`docs/paper-gaps/cpsv16_pure_zcl_local_orthogonality_scope.tex` and
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`. -/
theorem isPositiveGapBNTZCL_basisDirectSum_iff_hasNNCPHGroundSpaces
    (hCF : IsBNTCanonicalForm P) :
    IsPositiveGapBNTZCL (directSumTensor P.basis) P.basis ↔
      HasNNCPHGroundSpaces (directSumTensor P.basis) P.basis :=
  hCF.isPositiveGapBNTZCL_basisDirectSum_iff_isTransferIdempotent.trans
    hCF.isTransferIdempotent_basisDirectSum_iff_hasNNCPHGroundSpaces

end IsBNTCanonicalForm

end MPSTensor
