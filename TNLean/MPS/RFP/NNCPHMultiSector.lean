/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockDiagonalOneSiteSpan
import TNLean.MPS.RFP.BNTDirectSumBasis
import TNLean.MPS.RFP.ResidualWordSpan

/-!
# Nearest-neighbor ground spaces for multiplicity-one RFP sectors

This file applies the general simultaneous one-site span theorem to a
multiplicity-one family of distinct normal sectors whose direct sum is a
renormalization fixed point.
-/

namespace MPSTensor.IsBNTCanonicalForm

variable {d : ℕ} {P : SectorDecomposition d}

/-- A multiplicity-one BNT family whose direct sum is a renormalization fixed
point has its nearest-neighbor parent-Hamiltonian ground space spanned by the
periodic matrix product vectors of its distinct basis sectors.

Source: arXiv:1606.00608, Definition 3.9, lines 517--524, and Theorem 3.10,
lines 534--541.

**Scope restriction (multiplicity-one distinct sectors):** the theorem treats
the direct sum of the BNT basis tensors, with one copy of each distinct sector.
Repeated copies and arbitrary raw sector weights remain outside this statement;
see docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex. -/
theorem rfp_hasParentHamiltonianGroundSpaceSpanning_basisDirectSum
    (hCF : IsBNTCanonicalForm P)
    (hRFP : IsTransferIdempotent (directSumTensor P.basis)) :
    HasParentHamiltonianGroundSpaceSpanning
      (directSumTensor P.basis) 2 P.basis := by
  by_cases hd : d = 0
  · subst d
    intro N hN
    ext ψ
    have hψ : ψ = 0 := by
      funext σ
      exact Fin.elim0 (σ ⟨0, by omega⟩)
    subst ψ
    simp
  · let : NeZero d := ⟨hd⟩
    let : ∀ j : Fin P.basisCount, NeZero (P.basisDim j) :=
      fun j ↦ ⟨(hCF.basis_dim_pos j).ne'⟩
    have hnormal : ∀ j : Fin P.basisCount, Kraus.IsNormal (P.basis j) :=
      hCF.basis_isNormal
    have hOne : WordTupleSpanTop P.basis 1 :=
      wordTupleSpanTop_one_of_isTransferIdempotent_directSum P.basis
        hnormal hCF.basis_irreducible hCF.basis_left_canonical
          hCF.basis_distinct hRFP
    rw [← toTensorFromBlocks_one_eq_directSumTensor P.basis]
    exact
      hasParentHamiltonianGroundSpaceSpanning_toTensorFromBlocks_of_wordTupleSpanTop_one
        (fun _ ↦ 1) P.basis (by simp) hOne

/-- **Corrected forward direction of the main MPS theorem (RFP ⟹ ZCL) at the
multiplicity-one representative.**

Let $P$ be a BNT canonical form. If the direct sum of its distinct basis
tensors $\bigoplus_j A_j$ is a renormalization fixed point, i.e. its transfer
matrix satisfies $\mathbb E^2=\mathbb E$, then it has zero correlation length
in the positive-gap form: the physical correlations are independent of the
separation whenever both complementary gaps are positive (CID), and the mixed
transfer matrices of distinct BNT components vanish,
$\mathbb E_{j,j'}=0$ for $j\neq j'$ (local orthogonality).

This is the implication (i) ⟹ (ii) of Theorem `thm:main-MPS` at
arXiv:1606.00608, lines 534--541, for the explicit multiplicity-one
unit-weight direct-sum representative, with the corrections forced by the
raw-weight counterexample
`halvedWeightTensor_counterexample_to_unrestricted_zcl_iff_rfp`, recorded in
docs/paper-gaps/cpsv16_pure_zcl_raw_weight_counterexample.tex: the source CID
quantifies over all disjoint regions, including adjacent ones, and the source
theorem permits raw sector weights and repeated copies. Both restrictions are
recorded in docs/paper-gaps/cpsv16_pure_zcl_local_orthogonality_scope.tex. -/
theorem isTransferIdempotent_basisDirectSum_isPositiveGapBNTZCL
    (hCF : IsBNTCanonicalForm P)
    (hRFP : IsTransferIdempotent (directSumTensor P.basis)) :
    IsPositiveGapBNTZCL (directSumTensor P.basis) P.basis := by
  let : ∀ j : Fin P.basisCount, NeZero (P.basisDim j) :=
    fun j ↦ ⟨(hCF.basis_dim_pos j).ne'⟩
  exact isPositiveGapBNTZCL_of_isTransferIdempotent_directSum P.basis
    hCF.isCPSVBasisOfNormalTensors_basisDirectSum
    hCF.basis_irreducible hCF.basis_left_canonical hCF.basis_distinct hRFP

end MPSTensor.IsBNTCanonicalForm
