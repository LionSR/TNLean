/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.SpectatorSiteExpectation
import TNLean.Circuit.SiteOscillation
import TNLean.PEPS.AreaLaw.Amplification.LocalRootChannels

/-!
# Actual channel shells controlled by physical site oscillations

Average an arbitrary operator over the physical sites of a shell region, leaving
its finite spectator untouched. The resulting operator lies in the regional
commutant, where the actual difference of localized square-root channels
vanishes. Its norm therefore depends only on the physical on-site oscillations.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`09-amplification.tex`, lines 101–121, especially
`eq:amplification-shell-oscillation`, at revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean text is reused.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open QuantumCircuit Matrix
open scoped BigOperators Kronecker Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.PEPS.AreaLaw

variable {q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [NeZero q]
variable {Aux : Type*} [Fintype Aux] [DecidableEq Aux]

/-- A channel localized away from a physical site cannot increase its
oscillation, even for an operator acting on a spectator. Source: area law,
`09-amplification.tex`, lines 124–127. -/
theorem siteOscillation_localRootChannel_le_of_notMem (K : Finset ι)
    {k : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (y : ι) (hy : y ∉ K)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    siteOscillation q y (localRootChannel K k B) ≤ siteOscillation q y B := by
  apply siteOscillation_le
  intro U hU hunitary
  have hUK : U ∈ supportedOperators q ((K : Set ι)ᶜ) := by
    apply supportedOperators_mono _ hU
    intro z hz
    have hzy : z = y := Set.mem_singleton_iff.mp hz
    simpa only [Set.mem_compl_iff, Finset.mem_coe, hzy] using hy
  rw [localRootChannel_commutator K hk₀ hk₁ hUK B]
  exact (norm_localRootChannel_le K hk₀ hk₁ _).trans
    (norm_commutator_le_siteOscillation y B hU hunitary)

private theorem norm_shell_le_sum_oscillation
    (regions : ℕ → Finset ι) (hregions : Monotone regions)
    {k : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (l : ℕ) {η : ℝ} (hη : 0 ≤ η)
    (hbound : ∀ C : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ,
      ‖localRootChannelShell regions k l C‖ ≤ η * ‖C‖)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    ‖localRootChannelShell regions k l B‖ ≤
      η * ∑ y ∈ regions l, siteOscillation q y B := by
  let E := spectatorSiteExpectation q (regions l)ᶜ B
  have hzero : localRootChannelShell regions k l E = 0 := by
    apply localRootChannelShell_eq_zero_of_forall_commute regions hregions hk₀ hk₁ l
    intro A hA
    exact (spectatorSiteExpectation_commute (regions l)ᶜ B (by simpa using hA)).symm
  have havg : ‖B - E‖ ≤ ∑ y ∈ regions l, siteOscillation q y B := by
    have h := norm_sub_spectatorSiteExpectation_le (regions l)ᶜ B
      (fun y => siteOscillation q y B) (fun y _ U hU hunitary =>
        norm_commutator_le_siteOscillation_right y B hU hunitary)
    simpa only [compl_compl] using h
  have heq : localRootChannelShell regions k l (B - E) =
      localRootChannelShell regions k l B := by
    rw [localRootChannelShell_sub, hzero, sub_zero]
  rw [← heq]
  exact (hbound (B - E)).trans (mul_le_mul_of_nonneg_left havg hη)

/-- The zeroth localized root-channel shell is bounded by twice the sum of
the physical oscillations in its region, uniformly in the finite spectator.
Source: area law, `09-amplification.tex`, lines 101–121. -/
theorem norm_localRootChannelShell_zero_le_sum_siteOscillation
    (regions : ℕ → Finset ι) (hregions : Monotone regions)
    {k : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    ‖localRootChannelShell regions k 0 B‖ ≤
      2 * ∑ y ∈ regions 0, siteOscillation q y B :=
  norm_shell_le_sum_oscillation regions hregions hk₀ hk₁ 0 (by norm_num)
    (norm_localRootChannelShell_zero_le regions hk₀ hk₁) B

/-- A successor shell is controlled by the two actual conditional-expectation
errors and the sum of physical oscillations in the larger region. Source:
area law, `09-amplification.tex`, `eq:amplification-shell-oscillation`.
There is no spectator-dimension factor. -/
theorem norm_localRootChannelShell_succ_le_sum_siteOscillation
    (regions : ℕ → Finset ι) (hregions : Monotone regions)
    {k : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (l : ℕ) {εNext εPrev : ℝ}
    (hNext : ‖k - siteExpectation q (regions (l + 1)) k‖ ≤ εNext)
    (hPrev : ‖k - siteExpectation q (regions l) k‖ ≤ εPrev)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    ‖localRootChannelShell regions k (l + 1) B‖ ≤
      4 * (Real.sqrt εNext + Real.sqrt εPrev) *
        ∑ y ∈ regions (l + 1), siteOscillation q y B :=
  norm_shell_le_sum_oscillation regions hregions hk₀ hk₁ (l + 1)
    (mul_nonneg (by norm_num) (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
    (norm_localRootChannelShell_succ_le regions hk₀ hk₁ l hNext hPrev) B

end TNLean.PEPS.AreaLaw
