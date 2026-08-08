/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.InverseMapActiveSectorPrimitivity
import TNLean.MPS.MPDO.LemmaC5CaseI

/-!
# The literal normal Case-I coefficient theorem from the strong area law

The strong area law supplies the Hayashi decomposition and its MPDO positivity.
The inverse-map construction retains one positive rephasing together with the
active spanning, nonvanishing, recurrence, inactive-sector, and nonemptiness
witnesses. Literal zero correlation length and normality then give the
normalized rank-one coefficients on the active sector.

**Scope restriction (active Hayashi/Case I):** this module proves only the
active-Hayashi normal Case-I conclusion. It does not replace literal zero
correlation length by a scale-invariant condition and does not pass to Case II.
See `docs/paper-gaps/cpgsv17_pf_rank_one.tex`.

Source: arXiv:1606.00608, Appendix C.2, Case I, Lemmas C.4--C.5 and the
corollary, lines 1374--1505.
-/

open scoped Matrix ComplexOrder BigOperators

namespace MPOTensor

variable {d D : ℕ}

/-- An injective normal MPO tensor satisfying the strong area law and literal
zero correlation length admits normalized rank-one coefficients for the active
inverse-map trace matrix.

The factorization, normalized nonnegative Hayashi weights, and all active-sector
witnesses come from the same rephased inverse-map construction. The MPDO
positivity used there is the one contained in `IsSAL K`.

**Scope restriction (active Hayashi/Case I):** this is the normal Case-I
active-sector conclusion of CPSV16 Appendix C.2. It does not assert the
coefficient-rescaled Case-II result. See
`docs/paper-gaps/cpgsv17_pf_rank_one.tex`.

Source: arXiv:1606.00608, Appendix C.2, Case I, Lemmas C.4--C.5 and the
corollary, lines 1374--1505. -/
theorem exists_activeSectorTraceMatrix_rank_one_coefficients_of_isSAL_of_literal_ZCL
    (K : MPOTensor d D) (hK : K.IsInjective) (hSAL : IsSAL K)
    (hZCL_sq : physTraceTransfer K * physTraceTransfer K = physTraceTransfer K)
    (hK_normal : MPSTensor.IsNormalTensor K.toMPSTensor) :
    ∃ (F : PhysicalSectorFactorization K) (p : Fin F.sectorCount → ℝ)
      (a b : F.ActiveSector p → ℝ),
      (∀ k, 0 ≤ p k) ∧ (∑ k, p k) = 1 ∧
        (∀ k h, (F.neighboringOperator k h).PosSemidef) ∧
          (∀ k h, F.activeSectorTraceMatrix p k h = a k * b h) ∧
            (∑ k, a k * b k) = 1 := by
  letI : NeZero D := ⟨hK_normal.bondDim_ne_zero⟩
  obtain ⟨hη⟩ := exists_etaStructure_reducedBlockState_of_isSAL K hSAL
  obtain ⟨beta, alpha, hm⟩ :=
    exists_normalizedFourSiteTail_entry_ne_zero
      K ((Classical.choose_spec hSAL).1 4 (by omega))
  let F := zeroWeightReparameterizedInverseMapPhysicalSectorFactorization
    K hK (normalizedFourSiteTail K)
      (isThreeSiteClosure_reducedBlockState K) hη alpha beta hm
  obtain ⟨z, hpos, hspan, hnonzero, htriangle, hinactive, hne⟩ :=
    exists_rephased_inverseMap_activeSectorTraceMatrix_primitivity_witnesses
      K hK (normalizedFourSiteTail K)
        (isThreeSiteClosure_reducedBlockState K) hη alpha beta hm
          (Classical.choose hSAL)
  letI : Nonempty ((F.rephase z).ActiveSector hη.p) := hne
  obtain ⟨a, b, hab, hsum⟩ :=
    activeSectorTraceMatrix_rank_one_coefficients_of_literal_ZCL
      K (F.rephase z) hη.p hpos hspan hnonzero htriangle hZCL_sq hinactive hK_normal
  exact ⟨F.rephase z, hη.p, a, b, hη.hp_nonneg, hη.hp_sum, hpos, hab, hsum⟩

end MPOTensor
