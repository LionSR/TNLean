/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.SiteOscillation
import TNLean.Circuit.SpectatorSiteExpectation

/-!
# Initial site oscillation of supported operators with spectators

The native spectator expectation fixes an operator exactly when each physical
matrix block belongs to the existing space `supportedOperators q K`. Such an
operator commutes with the physical algebra outside `K`, so its site
oscillation vanishes there. Together with `d_y(B) ≤ 2 * ‖B‖`, this gives the
initial bound `d_y(B) ≤ 2 * ‖B‖ * 1_K(y)` without a spectator dimension factor
or a Hermiticity assumption.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`09-amplification.tex`, lines 109–127 and 173, at revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. This is the initial
support estimate used before the Poisson evolution argument, not a growth
estimate for that evolution.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open Matrix
open scoped Kronecker Matrix.Norms.L2Operator

namespace QuantumCircuit

variable {q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Aux : Type*} [Fintype Aux] [DecidableEq Aux]

omit [Fintype Aux] [DecidableEq Aux] in
/-- A spectator operator is fixed by the native site expectation precisely
when each physical matrix block is supported on the retained sites.
Source: area law, `09-amplification.tex`, lines 114–121 and 173. -/
theorem spectatorSiteExpectation_eq_self_iff [NeZero q] (K : Finset ι)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    spectatorSiteExpectation q K B = B ↔
      ∀ a b : Aux, (Matrix.of fun σ τ => B (σ, a) (τ, b)) ∈
        supportedOperators q (K : Set ι) := by
  constructor
  · intro h a b
    have hblock : siteExpectation q K (Matrix.of fun σ τ => B (σ, a) (τ, b)) =
        Matrix.of fun σ τ => B (σ, a) (τ, b) := by
      ext σ τ
      exact congrArg (fun M => M (σ, a) (τ, b)) h
    rw [← hblock]
    exact siteExpectation_mem_supportedOperators K _
  · intro h
    ext ⟨σ, a⟩ ⟨τ, b⟩
    change siteExpectation q K (Matrix.of fun σ' τ' => B (σ', a) (τ', b)) σ τ = _
    rw [siteExpectation_of_mem_supportedOperators K (h a b)]
    rfl

/-- A supported operator, with an arbitrary finite spectator, has zero
oscillation at any physical site outside its support. Source: area law,
`09-amplification.tex`, lines 109–121 and the initial estimate at line 173. -/
theorem siteOscillation_eq_zero_of_not_mem_support [NeZero q] (K : Finset ι)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ)
    (hB : ∀ a b : Aux, (Matrix.of fun σ τ => B (σ, a) (τ, b)) ∈
      supportedOperators q (K : Set ι)) {y : ι} (hy : y ∉ K) :
    siteOscillation q y B = 0 := by
  apply siteOscillation_eq_zero_of_commute
  intro U hU
  have hUK : U ∈ supportedOperators q ((K : Set ι)ᶜ) :=
    supportedOperators_mono (Set.singleton_subset_iff.mpr hy) hU
  have hfix := (spectatorSiteExpectation_eq_self_iff K B).mpr hB
  simpa only [hfix] using (spectatorSiteExpectation_commute K B hUK).symm

/-- The literal initial oscillation bound, with the indicator of the physical
support and no spectator dimension factor. Source: area law,
`09-amplification.tex`, line 173, using the elementary bound at line 127. -/
theorem siteOscillation_le_support_indicator [NeZero q] (K : Finset ι)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ)
    (hB : ∀ a b : Aux, (Matrix.of fun σ τ => B (σ, a) (τ, b)) ∈
      supportedOperators q (K : Set ι)) (y : ι) :
    siteOscillation q y B ≤ 2 * ‖B‖ * (K : Set ι).indicator (fun _ => (1 : ℝ)) y := by
  by_cases hy : y ∈ K
  · simpa only [Set.indicator_of_mem hy, mul_one] using
      siteOscillation_le_two_mul_norm y B
  · simp only [Set.indicator_of_notMem hy, mul_zero,
      siteOscillation_eq_zero_of_not_mem_support K B hB hy, le_refl]

end QuantumCircuit
