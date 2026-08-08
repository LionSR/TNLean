/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.InverseMapActiveSectorPrimitivity
import TNLean.MPS.MPDO.ActiveSectorTraceMatrixZCL

/-!
# Zero correlation length on the active inverse-map trace matrix

The positive normalization furnished by source zero correlation length gives
the square--cube and positive-power trace relations on the same active,
positively rephased trace matrix that is primitive under the strong area law.

The argument writes the physical-trace transfer as a rectangular product
indexed only by sectors of nonzero Hayashi weight.  The opposite rectangular
product is the complexification of the active trace matrix because its
neighboring operators are positive semidefinite.

## Main results

* `exists_rephased_inverseMap_activeSectorTraceMatrix_normalized_relations`:
  the inverse-map construction has one rephasing for which positivity,
  primitivity, and both normalized relations hold.
* `exists_activeTraceMatrix_relations_of_isSAL_of_isSourceZCL`:
  the corresponding existence statement from the strong area law and source
  zero correlation length.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, Lemmas C.4--C.5, lines 1406--1497
-/

open scoped Matrix ComplexOrder BigOperators

namespace MPOTensor

variable {d D : ℕ}
  {rho : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}

/-- The inverse-map physical-sector factorization admits one coherent
rephasing for which the neighboring operators are positive semidefinite, the
active trace matrix is primitive, and a common positive source normalization
gives the square--cube and positive-power trace relations.

**Local fix (inactive sectors):** the physical factorization retains the
zero-weight sectors; the trace matrix is restricted to the nonzero-weight
subtype.  See
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

**Local fix (periodicity):** primitivity uses closed walks of lengths two and
three in place of blocking periodic components.  See the same paper-gap note.

Source: arXiv:1606.00608, Appendix C.2, Lemmas C.4--C.5 (`propSN` and
`SALZCL`), lines 1406--1497.  No idempotence, rank-one, or semisimplicity
conclusion is made. -/
theorem exists_rephased_inverseMap_activeSectorTraceMatrix_normalized_relations
    (K : MPOTensor d D) (hK : K.IsInjective)
    (R : Matrix (Fin D) (Fin D) ℂ) (hρ : IsThreeSiteClosure K R rho)
    (hη : EtaStructure rho) (alpha beta : Fin D) (hm : R beta alpha ≠ 0)
    (hM : IsMPDO K) (hZCL : IsSourceZCL K) :
    let F := zeroWeightReparameterizedInverseMapPhysicalSectorFactorization
      K hK R hρ hη alpha beta hm
    ∃ (z : Fin F.sectorCount → Circle) (lam : ℝ), 0 < lam ∧
      (∀ k h, ((F.rephase z).neighboringOperator k h).PosSemidef) ∧
        Matrix.IsPrimitive ((F.rephase z).activeSectorTraceMatrix hη.p) ∧
          let T := (F.rephase z).activeSectorTraceMatrix hη.p
          ((lam⁻¹ • T) ^ 2 = (lam⁻¹ • T) ^ 3) ∧
            ∀ N : ℕ, 0 < N →
              Matrix.trace ((lam⁻¹ • T) ^ N) = Matrix.trace (lam⁻¹ • T) := by
  let F := zeroWeightReparameterizedInverseMapPhysicalSectorFactorization
    K hK R hρ hη alpha beta hm
  change ∃ (z : Fin F.sectorCount → Circle) (lam : ℝ), 0 < lam ∧
    (∀ k h, ((F.rephase z).neighboringOperator k h).PosSemidef) ∧
      Matrix.IsPrimitive ((F.rephase z).activeSectorTraceMatrix hη.p) ∧
        let T := (F.rephase z).activeSectorTraceMatrix hη.p
        ((lam⁻¹ • T) ^ 2 = (lam⁻¹ • T) ^ 3) ∧
          ∀ N : ℕ, 0 < N →
            Matrix.trace ((lam⁻¹ • T) ^ N) = Matrix.trace (lam⁻¹ • T)
  obtain ⟨z, hpos, hspan, hnonzero, htriangle, hinactive, _⟩ :=
    exists_rephased_inverseMap_activeSectorTraceMatrix_primitivity_witnesses
      K hK R hρ hη alpha beta hm hM
  have hprim : Matrix.IsPrimitive ((F.rephase z).activeSectorTraceMatrix hη.p) :=
    (F.rephase z).activeSectorTraceMatrix_isPrimitive
      hη.p hpos hspan hnonzero htriangle
  obtain ⟨lam, hlam, hrel⟩ :=
    (F.rephase z).activeSectorTraceMatrix_normalized_relations_of_isSourceZCL
      hη.p hinactive hpos hZCL
  exact ⟨z, lam, hlam, hpos, hprim, hrel⟩

/-- Every injective MPO tensor satisfying the strong area law and source zero
correlation length admits a positive physical-sector factorization whose
active trace matrix is primitive and whose common positive normalization
satisfies the square--cube and positive-power trace relations.

The weights are nonnegative and sum to one.  Zero-weight sectors remain in
the physical factorization and are omitted only from the auxiliary trace
matrix.

**Local fix (inactive sectors):** see
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

**Local fix (periodicity):** the primitivity proof uses closed walks of lengths
two and three in place of blocking periodic components.  See the same
paper-gap note.

Source: arXiv:1606.00608, Appendix C.2, Lemmas C.4--C.5 (`propSN` and
`SALZCL`), lines 1406--1497.  The conclusion does not include the invalid
rank-one inference at lines 1498--1499. -/
theorem exists_activeTraceMatrix_relations_of_isSAL_of_isSourceZCL
    (K : MPOTensor d D) (hK : K.IsInjective) (hSAL : IsSAL K)
    (hZCL : IsSourceZCL K) :
    ∃ (F : PhysicalSectorFactorization K) (p : Fin F.sectorCount → ℝ) (lam : ℝ),
      0 < lam ∧
        (∀ k, 0 ≤ p k) ∧
          (∑ k, p k) = 1 ∧
            (∀ k h, (F.neighboringOperator k h).PosSemidef) ∧
              Matrix.IsPrimitive (F.activeSectorTraceMatrix p) ∧
                let T := F.activeSectorTraceMatrix p
                ((lam⁻¹ • T) ^ 2 = (lam⁻¹ • T) ^ 3) ∧
                  ∀ N : ℕ, 0 < N →
                    Matrix.trace ((lam⁻¹ • T) ^ N) =
                      Matrix.trace (lam⁻¹ • T) := by
  obtain ⟨hη⟩ := exists_etaStructure_reducedBlockState_of_isSAL K hSAL
  obtain ⟨beta, alpha, hm⟩ :=
    exists_normalizedFourSiteTail_entry_ne_zero
      K ((Classical.choose_spec hSAL).1 4 (by omega))
  let F₀ := zeroWeightReparameterizedInverseMapPhysicalSectorFactorization
    K hK (normalizedFourSiteTail K)
      (isThreeSiteClosure_reducedBlockState K) hη alpha beta hm
  obtain ⟨z, lam, hlam, hpos, hprim, hrel⟩ :=
    exists_rephased_inverseMap_activeSectorTraceMatrix_normalized_relations
      K hK (normalizedFourSiteTail K)
        (isThreeSiteClosure_reducedBlockState K) hη alpha beta hm
          (Classical.choose hSAL) hZCL
  exact ⟨F₀.rephase z, hη.p, lam, hlam, hη.hp_nonneg, hη.hp_sum,
    hpos, hprim, hrel⟩

end MPOTensor
