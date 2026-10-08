/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.Defs

/-!
# Selection of a low-defect charge point

Normalizing the integrated entropy inequality by the `nm` charge rounds and the interval length
`ε/2`, and averaging, selects a charge round and a parameter `p_k ∈ [ε/2, ε]` with
`𝒬(p_k)/(KnD) ≤ δ_n + o_k(1)` (`scanner:selected-density`).

## Main results

* `TNLean.PEPS.AreaLaw.Scan.exists_mem_Icc_le_of_sum_integral_le`: averaging over finitely many
  continuous functions on an interval.
* `TNLean.PEPS.AreaLaw.Scan.tendsto_log_div_nat`: `log (k + 2) / k → 0`.
* `TNLean.PEPS.AreaLaw.Scan.exists_selected_density`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  section file `08-scanner.tex`, lines 471–490 and 529–532.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Independently
  formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Scan

open Filter Topology Set

/-- Averaging: if the integrals of finitely many continuous functions over `[α, β]` sum to at
most `|T| (β - α) c`, one of them takes a value at most `c` somewhere on `[α, β]`
(lines 480–490). -/
theorem exists_mem_Icc_le_of_sum_integral_le {R : ℕ} (Q : Fin R → ℝ → ℝ) (T : Finset (Fin R))
    (hT : T.Nonempty) {α β c : ℝ} (hαβ : α < β)
    (hcont : ∀ r ∈ T, ContinuousOn (Q r) (Icc α β))
    (h : ∑ r ∈ T, ∫ p in α..β, Q r p ≤ T.card * ((β - α) * c)) :
    ∃ r ∈ T, ∃ p ∈ Icc α β, Q r p ≤ c := by
  sorry

/-- `log (k + 2) / k → 0`: the replica floor `β_k = O(log(k+2))` does not survive the
normalization by `k` (lines 452–455). -/
theorem tendsto_log_div_nat :
    Tendsto (fun k : ℕ ↦ Real.log (k + 2) / k) atTop (𝓝 0) := by
  sorry

/-- The selected density bound `scanner:selected-density` (lines 471–490). For fixed scale
constants, uniformly in the scan data at every sufficiently large `n`, the integrated entropy
inequality at `k` yields a charge round and a common `p_k ∈ [ε/2, ε]` with
`𝒬(p_k)/(KnD) ≤ δ_n + ρ_k`, where `ρ_k → 0` depends on the fixed data but not on the selected
round or parameter (lines 393–395, 529–532). -/
theorem exists_selected_density (X : ScannerExponents) (κ : ScanConstants) (C₁ C_T : ℝ) :
    ∃ Cδ : ℝ, 0 ≤ Cδ ∧ ∀ᶠ n in atTop, ScaleFacts X n C₁ → ∀ S : ScanData X κ n,
      S.terminalBound ≤ C_T * X.W * (n : ℝ) ^ (1 + X.e) →
      ∃ ρ : ℕ → ℝ, (∀ k, 0 ≤ ρ k) ∧ Tendsto ρ atTop (𝓝 0) ∧
        ∀ k, 1 ≤ k → S.IntegratedChargeBound k →
          ∃ r ∈ X.chargeRounds n, ∃ p ∈ Icc (X.eps n / 2) (X.eps n),
            (S.round r).chargeDefect k p / (X.K n * n * X.D n) ≤ X.delta Cδ κ.Cl n + ρ k := by
  sorry

end TNLean.PEPS.AreaLaw.Scan
