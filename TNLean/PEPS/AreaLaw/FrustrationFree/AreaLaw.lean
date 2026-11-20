/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.FrustrationFree.Amplification
import TNLean.PEPS.AreaLaw.PhysicalCollarInformation
import TNLean.PEPS.AreaLaw.Geometry.TwoFamilyAssembly
import TNLean.PEPS.AreaLaw.BoundaryTheorem

/-!
# The frustration-free area law by the sweep

The goal `eq:goal` of the frustration-free area-law note, proved along the note's route: the
sublinear collar bound (Proposition 9.6, `sublinearCollarBound_real`, valid for every gapped
instance and hence for the frustration-free model), the amplification by the exact sweep of the
range projections of the terms (`frustrationFreeAmplificationBound`), and the two-family
cancellation of tile entropies (Proposition 11.2, `twoFamilyDecomposition`, and Lemma 11.1 in
`regionalEntropy_le_of_collar_amplification_twoFamilies_at`). The proof does not use the
time-filtered amplification `amplificationBound` of the general theorem.

The collar bound is still the general one: the note's further replacement of the scanner input
by the raw terms (`eq:identity`) is not formalized here, and is not needed for `eq:goal`. See
`docs/formalization/frustration-free-area-law-plan.md`.

## Main statements

* `TNLean.PEPS.AreaLaw.FrustrationFree.frustrationFreeAreaLaw`.

## References

* Reading note *Entanglement across a cut in two-dimensional frustration-free ground states*,
  November 18, 2026, `docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`,
  `eq:goal`, Sections "Amplification with the original frustration-free terms" and "Two families
  and cancellation of tile entropies".
* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Propositions 9.6 and 11.2 and Lemma 11.1.
-/

namespace TNLean.PEPS.AreaLaw.FrustrationFree

/-- **The frustration-free area law** (`eq:goal` of the frustration-free area-law note), by the
note's route: the collar bound, the amplification by the exact sweep, and the two-family
cancellation. For `q ≥ 1`, `R`, and `J, Δ > 0` there is a constant `C`, chosen before the domain,
the Hamiltonian and the cut, with `S_Ω(A) ≤ C |∂_Λ A|` for every instance of `eq:model`. Source:
`docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`, `eq:goal` and Section
"Two families and cancellation of tile entropies". -/
theorem frustrationFreeAreaLaw : FrustrationFreeAreaLaw := by
  intro q hq R J Δ hJ hΔ
  obtain ⟨C₁, N₁, hcol⟩ := sublinearCollarBound_real q R hq (J := J) (D₀ := 2 * R + 11)
    (Ctpl := 24) hJ.le hΔ (by linarith) le_rfl
  set C₂ := frustrationFreeAmplificationConstant q R J Δ (max C₁ 1) 100
  set N₂ := frustrationFreeAmplificationThreshold q R J Δ (max C₁ 1) 100
  obtain ⟨C₃, hdec⟩ := twoFamilyDecomposition (2 * R + 11) 24 (uniformAreaLawScale N₁ N₂ C₂)
    (one_le_two.trans (two_le_uniformAreaLawScale N₁ N₂ C₂))
  refine ⟨uniformAreaLawConstantOf q C₂ C₃, uniformAreaLawConstantOf_nonneg hq C₂ C₃,
    fun Λ h Ω hff A ↦ ?_⟩
  exact regionalEntropy_le_of_collar_amplification_twoFamilies_at hq hΔ h hff.isHermitian
    hff.norm_eq_one (hff.isGapped hΔ) (hff.groundSpace_eq hΔ) A
    (fun n s₀ hn ↦ hcol n s₀ hn Λ h hff.isHermitian (hff.norm_term_le hJ.le) 0 Ω
      hff.norm_eq_one (hff.isGapped hΔ) (hff.groundSpace_eq hΔ) A)
    (fun n hn2 hn ↦ frustrationFreeAmplificationBound hq hJ hΔ (lt_max_of_lt_right one_pos) 100
      n hn2 hn Λ h Ω hff A)
    (hdec Λ A)

end TNLean.PEPS.AreaLaw.FrustrationFree
