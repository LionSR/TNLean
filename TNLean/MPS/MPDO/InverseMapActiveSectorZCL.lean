/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.InverseMapActiveSectorPrimitivity
import TNLean.MPS.MPDO.SectorPairingTransfer

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

* `PhysicalSectorFactorization.activeSectorTraceMatrix_normalized_relations_of_isSourceZCL`:
  source zero correlation length gives normalized square--cube and trace-power
  relations on the active trace matrix of a positive sector factorization.
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

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

/-- Suppose that the left tensor vanishes in every sector of zero weight and
that all neighboring operators are positive semidefinite.  If the original
tensor has source zero correlation length, then one positive normalization of
the active trace matrix satisfies
\[
  \widehat T^2=\widehat T^3,
  \qquad
  \operatorname{tr}(\widehat T^N)=\operatorname{tr}(\widehat T)
  \quad (N\geq 1).
\]

The proof restricts the rectangular decomposition of the physical-trace
transfer to the nonzero-weight sectors.  Positivity identifies the opposite
rectangular product with the complexification of the real active trace
matrix.

Source: arXiv:1606.00608, Appendix C.2, equations `Tkn` and `SALZCL`,
lines 1473--1497.  The conclusion does not assert idempotence, rank one, or
semisimplicity of the trace matrix. -/
theorem activeSectorTraceMatrix_normalized_relations_of_isSourceZCL
    (F : PhysicalSectorFactorization K) (p : Fin F.sectorCount → ℝ)
    (hinactive : ∀ k, p k = 0 → ∀ beta, F.leftTensor k beta = 0)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    (hZCL : K.IsSourceZCL) :
    ∃ lam : ℝ, 0 < lam ∧
      let T := F.activeSectorTraceMatrix p
      ((lam⁻¹ • T) ^ 2 = (lam⁻¹ • T) ^ 3) ∧
        ∀ N : ℕ, 0 < N →
          Matrix.trace ((lam⁻¹ • T) ^ N) = Matrix.trace (lam⁻¹ • T) := by
  classical
  obtain ⟨lam, hlam, hidem⟩ := hZCL.normalized_idempotent
  let L : Matrix (Fin D) (F.ActiveSector p) ℂ :=
    fun beta h ↦ (F.leftTensor h beta).trace
  let Q : Matrix (F.ActiveSector p) (Fin D) ℂ :=
    fun k alpha ↦ (F.rightTensor k alpha).trace
  have hphys : MPOTensor.physTraceTransfer K = L * Q := by
    let U : Matrix.unitaryGroup (Fin d) ℂ := ⟨F.physicalIsometry, by
      rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
      exact F.physicalIsometry_isometry⟩
    have hfactor : ∀ beta alpha,
        Matrix.reindex F.sectorEquiv F.sectorEquiv
            ((U : Matrix (Fin d) (Fin d) ℂ) * MPOTensor.physicalSlice K beta alpha *
              (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) =
          Matrix.blockDiagonal' fun q ↦
            Matrix.kroneckerMap (· * ·) (F.leftTensor q beta) (F.rightTensor q alpha) := by
      simpa [U] using F.factorization
    rw [MPOTensor.physTraceTransfer_eq_sum_closedSector K F.sectorEquiv U
      F.leftTensor F.rightTensor hfactor]
    ext beta alpha
    simp only [MPOTensor.closedSectorPairingOperator, Matrix.sum_apply,
      Matrix.vecMulVec_apply, Matrix.mul_apply, L, Q]
    rw [← Finset.sum_subtype (Finset.univ.filter (fun k ↦ p k ≠ 0)) (by simp)
      (fun k ↦ (F.leftTensor k beta).trace * (F.rightTensor k alpha).trace)]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : p k ≠ 0
    · simp [hk]
    · rw [if_neg hk, hinactive k (not_ne_iff.mp hk) beta, Matrix.trace_zero, zero_mul]
  have hrect : IsIdempotentElem (((lam : ℂ)⁻¹ • L) * Q) := by
    simpa only [Matrix.smul_mul, ← hphys] using hidem
  let TC : Matrix (F.ActiveSector p) (F.ActiveSector p) ℂ := Q * L
  have hTC : TC = Matrix.map (F.activeSectorTraceMatrix p) Complex.ofReal := by
    ext k h
    simp only [TC, Matrix.mul_apply, Q, L, Matrix.map_apply]
    change (∑ j, (F.rightTensor (k : Fin F.sectorCount) j).trace *
      (F.leftTensor (h : Fin F.sectorCount) j).trace) =
        ((F.neighboringOperator k h).trace.re : ℂ)
    rw [← (hpos k h).isHermitian.trace_eq_ofReal_re]
    simp only [neighboringOperator, Matrix.trace, Matrix.diag, Matrix.of_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    rw [Fintype.sum_prod_type]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
  refine ⟨lam, hlam, ?_⟩
  dsimp only
  have hmap : Matrix.map (lam⁻¹ • F.activeSectorTraceMatrix p) Complex.ofReal =
      (lam : ℂ)⁻¹ • TC := by
    rw [hTC]
    ext k h
    simp [Matrix.smul_apply, Matrix.map_apply]
  have hmapHom :
      Matrix.map (lam⁻¹ • F.activeSectorTraceMatrix p) (⇑Complex.ofRealHom) =
        (lam : ℂ)⁻¹ • TC := hmap
  constructor
  · apply Matrix.map_injective Complex.ofReal_injective
    change Matrix.map ((lam⁻¹ • F.activeSectorTraceMatrix p) ^ 2) (⇑Complex.ofRealHom) =
      Matrix.map ((lam⁻¹ • F.activeSectorTraceMatrix p) ^ 3) (⇑Complex.ofRealHom)
    rw [Matrix.map_pow, Matrix.map_pow, hmapHom]
    simpa only [Matrix.mul_smul, TC] using
      (Matrix.pow_two_eq_pow_three_of_rectangular_idempotent
        ((lam : ℂ)⁻¹ • L) Q hrect)
  · intro N hN
    apply Complex.ofReal_injective
    change Complex.ofRealHom (Matrix.trace ((lam⁻¹ • F.activeSectorTraceMatrix p) ^ N)) =
      Complex.ofRealHom (Matrix.trace (lam⁻¹ • F.activeSectorTraceMatrix p))
    rw [AddMonoidHom.map_trace Complex.ofRealHom,
      AddMonoidHom.map_trace Complex.ofRealHom, Matrix.map_pow, hmapHom]
    simpa only [Matrix.mul_smul, TC] using
      (Matrix.trace_pow_eq_trace_of_rectangular_idempotent
        ((lam : ℂ)⁻¹ • L) Q hrect N hN)

end MPOTensor.PhysicalSectorFactorization

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
  obtain ⟨z, hpos, hprim⟩ :=
    exists_rephased_inverseMap_activeSectorTraceMatrix_isPrimitive
      K hK R hρ hη alpha beta hm hM
  have hinactive : ∀ k, hη.p k = 0 →
      ∀ gamma, (F.rephase z).leftTensor k gamma = 0 := by
    intro k hk gamma
    change (z k : ℂ) • sectorTensorL K hK hη R alpha beta k gamma = 0
    rw [sectorTensorL_eq_zero_of_weight_eq_zero K hK hη R alpha beta k gamma hk,
      smul_zero]
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
      K ((Classical.choose_spec hSAL).1 4)
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
