/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorFactorization
import TNLean.MPS.MPDO.SectorFactorization

/-!
# Physical-sector factorization from the inverse-map tensors

This file combines the sector tensors obtained from the Hayashi decomposition
of a three-site closure as a `PhysicalSectorFactorization`.  The construction
records only the direct-sum factorization and its neighboring contractions;
it does not assert positivity of those contractions.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, equation `AppUkU=rl`, lines 1383--1387; Lemma C.4 (`propSN`),
  lines 1406--1411; equation `formK`, lines 1434--1439; and equation `etarl`,
  lines 1441--1445
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d D : ℕ}

/-- The physical-sector factorization determined by a Hayashi decomposition
and a nonzero entry of the virtual tail.

The nonzero dimensions of the left and right factors follow from the
trace-one left and right sector density matrices; they are not additional
hypotheses.  No positivity of the neighboring contractions is asserted.

**Local fix (tail index):** the selected tail entry is
$R_{\beta_3,\alpha_1}$, as dictated by the inverse-map contraction.  The
correction is recorded in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

Source: arXiv:1606.00608, Appendix C.2, equation `AppUkU=rl`, lines
1383--1387; Lemma C.4 (`propSN`), lines 1406--1411; and equation `formK`,
lines 1434--1439. -/
noncomputable def inverseMapPhysicalSectorFactorization
    {rho : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    (K : MPOTensor d D) (hK : K.IsInjective)
    (R : Matrix (Fin D) (Fin D) ℂ) (hρ : IsThreeSiteClosure K R rho)
    (hη : EtaStructure rho) (α₁ β₃ : Fin D) (hm : R β₃ α₁ ≠ 0) :
    PhysicalSectorFactorization K where
  sectorCount := hη.m
  leftDim := hη.dL
  rightDim := hη.dR
  leftDim_pos := fun k ↦ Fin.pos_iff_nonempty.mpr <| by
    have hp : Nonempty (Fin d × Fin (hη.dL k)) :=
      Matrix.nonempty_of_trace_eq_one (hη.ρ_left k) (hη.hρ_left_dm k).2
    exact hp.map Prod.snd
  rightDim_pos := fun k ↦ Fin.pos_iff_nonempty.mpr <| by
    have hp : Nonempty (Fin (hη.dR k) × Fin d) :=
      Matrix.nonempty_of_trace_eq_one (hη.ρ_right k) (hη.hρ_right_dm k).2
    exact hp.map Prod.fst
  sectorEquiv := hη.decompB
  physicalIsometry := hη.U_B
  physicalIsometry_isometry := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff').mp hη.U_B.2
  leftTensor := fun k beta ↦ sectorTensorL K hK hη R α₁ β₃ k beta
  rightTensor := fun k alpha ↦ sectorTensorR K hK hη β₃ k alpha
  factorization := physicalSlice_sector_factorization K hK R rho hρ hη hm

/-- The neighboring contraction of the resulting physical-sector
factorization is the inverse-map operator `sectorEta`.

No positivity or normalization is part of this identification.

Source: arXiv:1606.00608, Appendix C.2, equation `etarl`, lines 1441--1445. -/
theorem inverseMapPhysicalSectorFactorization_neighboringOperator_eq_sectorEta
    {rho : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    (K : MPOTensor d D) (hK : K.IsInjective)
    (R : Matrix (Fin D) (Fin D) ℂ) (hρ : IsThreeSiteClosure K R rho)
    (hη : EtaStructure rho) (α₁ β₃ : Fin D) (hm : R β₃ α₁ ≠ 0)
    (k h : Fin hη.m) :
    (inverseMapPhysicalSectorFactorization K hK R hρ hη α₁ β₃ hm).neighboringOperator k h =
      sectorEta K hK hη R α₁ β₃ k h := by
  ext ⟨xR, xL⟩ ⟨yR, yL⟩
  change (∑ gamma : Fin D,
      sectorTensorR K hK hη β₃ k gamma xR yR *
        sectorTensorL K hK hη R α₁ β₃ h gamma xL yL) = _
  rw [sectorEta, Matrix.sum_apply]
  simp only [Matrix.kroneckerMap_apply]

/-- An injective MPO tensor satisfying SAL admits the raw physical-sector
factorization obtained from the four-site Hayashi decomposition.

This conclusion contains no positivity, recurrence, ZCL, primitivity, or
normality assertion.  Those are subsequent steps in the proof of the positive
factorization used in Proposition C.8.

**Scope restriction (raw sector factorization):** this is the algebraic
factorization step of Lemma C.4, not the coherent positivity conclusion used
later in Proposition C.8.  The remaining steps are recorded in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

Source: arXiv:1606.00608, Appendix C.2, Lemma C.4 (`propSN`), lines
1406--1411, and equations `formK` and `etarl`, lines 1434--1445. -/
theorem nonempty_physicalSectorFactorization_of_isSAL
    (K : MPOTensor d D) (hK : K.IsInjective) (hSAL : IsSAL K) :
    Nonempty (PhysicalSectorFactorization K) := by
  obtain ⟨hη⟩ := exists_etaStructure_reducedBlockState_of_isSAL K hSAL
  obtain ⟨β₃, α₁, hm⟩ :=
    exists_normalizedFourSiteTail_entry_ne_zero K
      ((Classical.choose_spec hSAL).1 4 (by omega))
  exact ⟨inverseMapPhysicalSectorFactorization K hK (normalizedFourSiteTail K)
    (isThreeSiteClosure_reducedBlockState K) hη α₁ β₃ hm⟩

end MPOTensor
