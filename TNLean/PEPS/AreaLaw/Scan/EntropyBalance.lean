/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.Defs

/-!
# Integrated entropy balance of the scan

At a charge round every split term of a good old history is sampled with probability at least
`c/(nD)`, so the entropy gain of Proposition 7.4 dominates `(cka/(nD)) 𝒬(p)`
(`scanner:charge-gain`). Integrating over every full round, telescoping the endpoint values of
`log N²`, and bounding the two ends by the initial floor and the terminal rough upper
comparison gives `ScanData.IntegratedChargeBound`.

## Main results

* `TNLean.PEPS.AreaLaw.Scan.sum_integral_le_of_deriv`: telescoped integration of derivative
  lower bounds over a finite chain of intervals.
* `TNLean.PEPS.AreaLaw.Scan.ScanData.chargeDefect_le_choiceGainSum`: `scanner:charge-gain`.
* `TNLean.PEPS.AreaLaw.Scan.ScanData.integratedChargeBound`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  section file `08-scanner.tex`, lines 416–479.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Independently
  formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Scan

open MeasureTheory Set

/-- Telescoped integration of derivative lower bounds over a chain of `R` unit intervals whose
adjacent endpoint values agree. Rounds in `T` carry a nonnegative gain `coef · Q r` that is
retained only on `[α, β] ⊆ [0, 1]`; every round pays the error `err`
(`08-scanner.tex`, lines 457–475). -/
theorem sum_integral_le_of_deriv {R : ℕ} (f Q : Fin R → ℝ → ℝ) (T : Finset (Fin R))
    {coef err α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ 1) (hcoef : 0 ≤ coef)
    (hR : 0 < R)
    (hcont : ∀ r, ContinuousOn (f r) (Icc 0 1))
    (hdiff : ∀ r, DifferentiableOn ℝ (f r) (Ioo 0 1))
    (hQ_nonneg : ∀ r, ∀ p ∈ Ioo (0 : ℝ) 1, 0 ≤ Q r p)
    (hQ_cont : ∀ r, ContinuousOn (Q r) (Ioo 0 1))
    (hQ_bdd : ∃ B, ∀ r, ∀ p ∈ Ioo (0 : ℝ) 1, Q r p ≤ B)
    (hgainT : ∀ r ∈ T, ∀ p ∈ Ioo (0 : ℝ) 1, coef * Q r p - err ≤ -deriv (f r) p)
    (hgain : ∀ r, ∀ p ∈ Ioo (0 : ℝ) 1, -err ≤ -deriv (f r) p)
    (htele : ∀ (r : Fin R) (hr : r.val + 1 < R), f ⟨r.val + 1, hr⟩ 0 = f r 1) :
    coef * ∑ r ∈ T, ∫ p in α..β, Q r p ≤
      f ⟨0, hR⟩ 0 - f ⟨R - 1, Nat.sub_lt hR one_pos⟩ 1 + R * err := by
  sorry

namespace ScanData

variable {X : ScannerExponents} {κ : ScanConstants} {n : ℕ} (S : ScanData X κ n)

/-- On a charge round the choice-averaged entropy gain dominates `c/(nD)` times the charge
defect `𝒬(p)`: good old histories sample each split term with probability at least `c/(nD)`
and bad ones contribute nonnegatively (`scanner:charge-gain`, lines 442–451). -/
theorem chargeDefect_le_choiceGainSum (r : Fin (X.rounds n)) (hr : IsChargeRound r)
    (k : ℕ) (p : ℝ) :
    κ.c / (n * X.D n) * (S.round r).chargeDefect k p ≤ (S.round r).choiceGainSum k p := by
  sorry

/-- The charge defect is nonnegative (lines 437–438). -/
theorem chargeDefect_nonneg (r : Fin (X.rounds n)) (k : ℕ) (p : ℝ) :
    0 ≤ (S.round r).chargeDefect k p := by
  sorry

/-- The charge defect is bounded at fixed `k` (lines 438–440, 488). -/
theorem chargeDefect_le (r : Fin (X.rounds n)) (k : ℕ) (p : ℝ) :
    (S.round r).chargeDefect k p ≤ κ.C * X.K n * n * X.D n * (κ.C * Real.log n ^ κ.Cl) := by
  sorry

/-- The integrated entropy inequality (lines 457–475), for every replica count `k ≥ 1`. -/
theorem integratedChargeBound {C₁ : ℝ} (hn : ScaleFacts X n C₁) (k : ℕ) (hk : 1 ≤ k) :
    S.IntegratedChargeBound k := by
  sorry

end ScanData

end TNLean.PEPS.AreaLaw.Scan
