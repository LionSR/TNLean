/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CPSVBlockingChannelCounterexample
import TNLean.MPS.MPDO.NeighboringTraceObstructionAmbientBlocks
import TNLean.MPS.MPDO.SitewisePhysicalRecovery

/-!
# The CPSV16 blocking-channel obstruction after physical embedding

The four-letter counterexample embeds isometrically into the five-letter
physical space used by the ambient simple-biCF construction.  A hypothetical
channel between the embedded closure families could be composed with the
sitewise embedding and its trace-preserving recovery, producing a channel
between the original closure families.  The trace-norm obstruction therefore
survives the physical embedding.
-/

open scoped Matrix

noncomputable section

namespace MPOTensor.CPSVBlockingChannelCounterexample

open NeighboringTraceObstructionAmbientBlocks

/-- A channel between embedded closure families descends through the
sitewise physical isometry to a channel between the original families. -/
private theorem exists_sourceMap_of_exists_embeddedMap (N : ℕ)
    (h : ∃ T : Matrix (Fin 2 → Fin 5) (Fin 2 → Fin 5) ℂ →ₗ[ℂ]
        Matrix (Fin N → Fin 5) (Fin N → Fin 5) ℂ,
      IsKrausCPTP T ∧
      ∀ X : Matrix (Fin 2) (Fin 2) ℂ,
        T (physCloseN embeddedObstruction 2 X) =
          physCloseN embeddedObstruction N X) :
    ∃ T : Matrix (Fin 2 → Fin 4) (Fin 2 → Fin 4) ℂ →ₗ[ℂ]
        Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ,
      IsKrausCPTP T ∧
      ∀ X : Matrix (Fin 2) (Fin 2) ℂ,
        T (physCloseN NonCartesianActiveSectorCandidate.tensor 2 X) =
          physCloseN NonCartesianActiveSectorCandidate.tensor N X := by
  obtain ⟨T, hT, hclose⟩ := h
  let Tsource : Matrix (Fin 2 → Fin 4) (Fin 2 → Fin 4) ℂ →ₗ[ℂ]
      Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ :=
    sitewisePhysicalRecovery physicalInclusion N ∘ₗ T ∘ₗ
      singleKrausMap (sitewisePhysicalMatrix physicalInclusion 2)
  have hForward : IsKrausCPTP
      (singleKrausMap (sitewisePhysicalMatrix physicalInclusion 2)) :=
    singleKrausMap_isKrausCPTP (sitewisePhysicalMatrix physicalInclusion 2)
      (sitewisePhysicalMatrix_isometry physicalInclusion
        physicalInclusion_isometry 2)
  have hRecover : IsKrausCPTP
      (sitewisePhysicalRecovery physicalInclusion N) :=
    sitewisePhysicalRecovery_isKrausCPTP physicalInclusion
      physicalInclusion_isometry N
  have hTsource : IsKrausCPTP Tsource :=
    isKrausCPTP_comp (isKrausCPTP_comp hForward hT) hRecover
  refine ⟨Tsource, hTsource, fun X ↦ ?_⟩
  simp only [Tsource, LinearMap.comp_apply]
  rw [singleKrausMap_sitewisePhysicalMatrix_physCloseN]
  change sitewisePhysicalRecovery physicalInclusion N
      (T (physCloseN embeddedObstruction 2 X)) = _
  rw [hclose X]
  simpa [embeddedObstruction] using
    sitewisePhysicalRecovery_physCloseN physicalInclusion
      physicalInclusion_isometry
      NonCartesianActiveSectorCandidate.tensor N X

/-- No trace-preserving completely positive map sends all two-site closures
of the embedded obstruction to the corresponding three-site closures. -/
theorem not_exists_embedded_two_to_three_site_map :
    ¬ ∃ T : Matrix (Fin 2 → Fin 5) (Fin 2 → Fin 5) ℂ →ₗ[ℂ]
        Matrix (Fin 3 → Fin 5) (Fin 3 → Fin 5) ℂ,
      IsKrausCPTP T ∧
      ∀ X : Matrix (Fin 2) (Fin 2) ℂ,
        T (physCloseN embeddedObstruction 2 X) =
          physCloseN embeddedObstruction 3 X := by
  intro h
  exact not_exists_two_to_three_site_map
    (exists_sourceMap_of_exists_embeddedMap 3 h)

/-- No trace-preserving completely positive map sends all two-site closures
of the embedded obstruction to the corresponding four-site closures. -/
theorem not_exists_embedded_two_to_four_site_map :
    ¬ ∃ T : Matrix (Fin 2 → Fin 5) (Fin 2 → Fin 5) ℂ →ₗ[ℂ]
        Matrix (Fin 4 → Fin 5) (Fin 4 → Fin 5) ℂ,
      IsKrausCPTP T ∧
      ∀ X : Matrix (Fin 2) (Fin 2) ℂ,
        T (physCloseN embeddedObstruction 2 X) =
          physCloseN embeddedObstruction 4 X := by
  intro h
  exact not_exists_two_to_four_site_map
    (exists_sourceMap_of_exists_embeddedMap 4 h)

end MPOTensor.CPSVBlockingChannelCounterexample
