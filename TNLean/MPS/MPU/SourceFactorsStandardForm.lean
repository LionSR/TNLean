/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SourceFactorsPhysicalAdjoint
import TNLean.MPS.MPU.ConjugationSourceFactors

/-!
# Standard forms from arbitrary normalized supplied source factors

The gate comparison with the selected factors, for the same tensor, provides
actual standard-form data with the supplied gates. No new decomposition,
transform or standard-form existence witness is assumed. The existing
normalized factor comparison supplies the two unitary rank changes.

Source: arXiv:1703.09188, `StandardForm` and Definition `SF`, lines 603–622,
and `FundamentalMPU`, lines 624–648. **Scope restriction (reduced canonical
presentation):** The tensor has a supplied reduced canonical presentation,
and the factors use its recorded weight; see
`docs/paper-gaps/mpu_canonical_form_full_support.tex`.
-/

open scoped Matrix Kronecker

namespace MPOTensor

/-- Any normalized factors at the canonical recorded weight provide actual
standard-form data for their own gates, not merely the SVD-selected gates.
Source: CPSV17, `StandardForm` and `SF`, lines 603–622. -/
theorem IsMPUCanonicalFormII.exists_twoSiteStandardFormData_sourceFactors
    {d D : ℕ} {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U) (S : SourceFactors U hU.ρ) :
    Nonempty (TwoSiteStandardFormData (blockTwo U)
      (SourceFactors.sourceU U S) (SourceFactors.sourceV U S)) := by
  let S₀ := sourceFactors U hU.ρ hU.ρ_posDef
  have hu₀ := hU.sourceFactors_sourceU_isUnitaryBetween hsimple S₀
  have huS := hU.sourceFactors_sourceU_isUnitaryBetween hsimple S
  obtain ⟨hr, hl, x, y, hu, hv⟩ :=
    hU.exists_supplied_source_gate_unitary_gauges_of_mpo_eq hU S₀ S hu₀ huS
      (fun _ _ ↦ rfl)
  have huId : Matrix.reindex
      (Equiv.prodCongr (finCongr hl.symm) (finCongr hr.symm)) (Equiv.refl _)
      (SourceFactors.sourceU U S₀) = SourceFactors.sourceU U S₀ := by
    ext ⟨l, r⟩ ij
    rfl
  have hvId : Matrix.reindex (Equiv.refl _)
      (Equiv.prodCongr (finCongr hr.symm) (finCongr hl.symm))
      (SourceFactors.sourceV U S₀) = SourceFactors.sourceV U S₀ := by
    ext ij ⟨r, l⟩
    rfl
  rw [huId] at hu
  rw [hvId] at hv
  have data := (hU.twoSiteStandardFormData hsimple).ofGateGauges x y
  change TwoSiteStandardFormData (blockTwo U)
    (((x : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ) ⊗ₖ
      (y : Matrix (Fin r[U]) (Fin r[U]) ℂ)) * SourceFactors.sourceU U S₀)
    (SourceFactors.sourceV U S₀ *
      (star (y : Matrix (Fin r[U]) (Fin r[U]) ℂ) ⊗ₖ
        star (x : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ))) at data
  rw [← hu, ← hv] at data
  exact ⟨data⟩

end MPOTensor
