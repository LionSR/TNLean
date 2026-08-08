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
witnesses. Literal zero correlation length and normality then give normalized
rank-one coefficients. Extending these coefficients by zero gives the same
factorization on every ambient Hayashi sector.

**Scope restriction (normal Case I):** this module proves only the normal
Case-I conclusion. It does not replace literal zero correlation length by a
scale-invariant condition and does not pass to Case II. See
`docs/paper-gaps/cpgsv17_pf_rank_one.tex`.

Source: arXiv:1606.00608, Appendix C.2, Case I, Lemmas C.4--C.5 and the
corollary, lines 1374--1505.
-/

open scoped Matrix ComplexOrder BigOperators

namespace MPOTensor

variable {d D : ℕ}

private theorem exists_activeSectorTraceMatrix_rank_one_coefficients_witnesses
    (K : MPOTensor d D) (hK : K.IsInjective) (hSAL : IsSAL K)
    (hZCL_sq : physTraceTransfer K * physTraceTransfer K = physTraceTransfer K)
    (hK_normal : MPSTensor.IsNormalTensor K.toMPSTensor) :
    ∃ (F : PhysicalSectorFactorization K) (p : Fin F.sectorCount → ℝ)
      (a b : F.ActiveSector p → ℝ),
      (∀ k, 0 ≤ p k) ∧ (∑ k, p k) = 1 ∧
        (∀ k h, (F.neighboringOperator k h).PosSemidef) ∧
          (∀ k h, F.activeSectorTraceMatrix p k h = a k * b h) ∧
            (∑ k, a k * b k) = 1 ∧
              (∀ k h, p k = 0 ∨ p h = 0 → F.neighboringOperator k h = 0) := by
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
  refine ⟨F.rephase z, hη.p, a, b, hη.hp_nonneg, hη.hp_sum, hpos, hab, hsum, ?_⟩
  intro k h hzero
  exact rephase_zeroWeightReparameterized_neighboringOperator_eq_zero_of_incident
    K hK (normalizedFourSiteTail K) (isThreeSiteClosure_reducedBlockState K)
      hη alpha beta hm z k h hzero

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
  obtain ⟨F, p, a, b, hp, hpsum, hpos, hab, hsum, _⟩ :=
    exists_activeSectorTraceMatrix_rank_one_coefficients_witnesses
      K hK hSAL hZCL_sq hK_normal
  exact ⟨F, p, a, b, hp, hpsum, hpos, hab, hsum⟩

/-- In normal Case I, the neighboring-operator trace coefficients factor on
all ambient Hayashi sectors. The active coefficients are retained unchanged,
and both ambient coefficient functions vanish on zero-weight sectors.

The same witness supplies normalized nonnegative Hayashi weights and positive
semidefinite neighboring operators. Consequently
$\operatorname{Re}\operatorname{tr}(\eta_{k,h})=a_kb_h$ for every pair of
ambient sectors and $\sum_k a_kb_k=1$.

**Scope restriction (normal Case I):** this theorem assumes literal zero
correlation length and normality. It makes no Case-II or scale-invariant ZCL
claim. See `docs/paper-gaps/cpgsv17_pf_rank_one.tex`.

Source: arXiv:1606.00608, Appendix C.2, Case I, Lemmas C.4--C.5 and the
corollary, lines 1374--1505. -/
theorem exists_neighboringOperator_trace_rank_one_coefficients_of_isSAL_of_literal_ZCL
    (K : MPOTensor d D) (hK : K.IsInjective) (hSAL : IsSAL K)
    (hZCL_sq : physTraceTransfer K * physTraceTransfer K = physTraceTransfer K)
    (hK_normal : MPSTensor.IsNormalTensor K.toMPSTensor) :
    ∃ (F : PhysicalSectorFactorization K) (p : Fin F.sectorCount → ℝ)
      (aActive bActive : F.ActiveSector p → ℝ)
      (a b : Fin F.sectorCount → ℝ),
      (∀ k, 0 ≤ p k) ∧ (∑ k, p k) = 1 ∧
        (∀ k h, (F.neighboringOperator k h).PosSemidef) ∧
          (∀ k h, F.activeSectorTraceMatrix p k h = aActive k * bActive h) ∧
            (∑ k, aActive k * bActive k) = 1 ∧
              (∀ k : F.ActiveSector p, a k = aActive k ∧ b k = bActive k) ∧
                (∀ k, p k = 0 → a k = 0 ∧ b k = 0) ∧
                  (∀ k h, (F.neighboringOperator k h).trace.re = a k * b h) ∧
                    (∑ k, a k * b k) = 1 := by
  classical
  obtain ⟨F, p, aActive, bActive, hp, hpsum, hpos, habActive, hsumActive,
      hincident⟩ := exists_activeSectorTraceMatrix_rank_one_coefficients_witnesses
        K hK hSAL hZCL_sq hK_normal
  let a : Fin F.sectorCount → ℝ := fun k ↦
    if hk : p k ≠ 0 then aActive ⟨k, hk⟩ else 0
  let b : Fin F.sectorCount → ℝ := fun k ↦
    if hk : p k ≠ 0 then bActive ⟨k, hk⟩ else 0
  have hagree : ∀ k : F.ActiveSector p,
      a k = aActive k ∧ b k = bActive k := by
    intro k
    simp [a, b, k.property]
  have hzero : ∀ k, p k = 0 → a k = 0 ∧ b k = 0 := by
    intro k hk
    simp [a, b, hk]
  have hab : ∀ k h, (F.neighboringOperator k h).trace.re = a k * b h := by
    intro k h
    by_cases hk : p k ≠ 0
    · by_cases hh : p h ≠ 0
      · simpa [PhysicalSectorFactorization.activeSectorTraceMatrix, a, b, hk, hh]
          using habActive ⟨k, hk⟩ ⟨h, hh⟩
      · rw [hincident k h (Or.inr (not_ne_iff.mp hh)), Matrix.trace_zero]
        simp [b, hh]
    · rw [hincident k h (Or.inl (not_ne_iff.mp hk)), Matrix.trace_zero]
      simp [a, hk]
  have hsum : (∑ k, a k * b k) = 1 := by
    calc
      ∑ k, a k * b k = ∑ k : F.ActiveSector p, a k * b k := by
        symm
        apply Finset.sum_subtype (Finset.univ.filter (fun k ↦ p k ≠ 0))
          (by simp)
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        simp [a, b, hk]
      _ = ∑ k : F.ActiveSector p, aActive k * bActive k := by
        apply Finset.sum_congr rfl
        intro k _
        rw [(hagree k).1, (hagree k).2]
      _ = 1 := hsumActive
  exact ⟨F, p, aActive, bActive, a, b, hp, hpsum, hpos, habActive,
    hsumActive, hagree, hzero, hab, hsum⟩

end MPOTensor
