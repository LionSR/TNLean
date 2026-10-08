/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.Defs

/-!
# Energy at the selected charge point

At the selected point the energy estimate of Proposition 7.4 is bounded leaf by leaf: old good
leaves by Hölder's inequality against the charge defect, old bad leaves by the tail of
Lemma 9.1(4), and new leaves by their total weight `p ≤ ε`. The coefficient
`a² (D/m) KnD = W² n D²/(mK) ≤ C W² n^ℓ D²` contains no total-volume factor.

## Main results

* `TNLean.PEPS.AreaLaw.Scan.integral_rpow_le_of_holder`: Hölder for `η^{1/8}` against a finite
  measure.
* `TNLean.PEPS.AreaLaw.Scan.ScanData.energySum_le`: the leaf accounting.
* `TNLean.PEPS.AreaLaw.Scan.exists_defectEnergy_le`: `scanner:energy-output` from the selected
  density.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  section file `08-scanner.tex`, lines 492–528.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Independently
  formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Scan

open MeasureTheory Set

/-- Hölder's inequality for the eighth root against a finite measure:
`∫ η^{1/8} dν ≤ ν(univ)^{7/8} (∫ η dν)^{1/8}` for bounded measurable `η ≥ 0`
(lines 497–501). -/
theorem integral_rpow_le_of_holder {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    [IsFiniteMeasure ν] {η : Ω → ℝ} (hη : Measurable η) (hη0 : ∀ x, 0 ≤ η x) {B : ℝ}
    (hηB : ∀ x, η x ≤ B) :
    ∫ x, η x ^ (1 / 8 : ℝ) ∂ν ≤ ν.real univ ^ (7 / 8 : ℝ) * (∫ x, η x ∂ν) ^ (1 / 8 : ℝ) := by
  sorry

namespace ScanData

variable {X : ScannerExponents} {κ : ScanConstants} {n : ℕ} (S : ScanData X κ n)

/-- Leaf accounting for the energy sum of Proposition 7.4 (lines 492–507): with `N = CKnD`
split occurrences per leaf, split weights `≤ CD/m`, move entropies `≤ η_max = C (log n)^{C_l}`,
bad weight `≤ n^{-200}` and new-leaf weight `p`,
`energySum ≤ (CD/m) N ((𝒬/N)^{1/8} + η_max^{1/8} (n^{-200} + p))`. -/
theorem energySum_le {C₁ : ℝ} (hn : ScaleFacts X n C₁) (r : Fin (X.rounds n)) (k : ℕ)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    (S.round r).energySum k p ≤
      κ.C * X.D n / X.m n * (κ.C * X.K n * n * X.D n) *
        (((S.round r).chargeDefect k p / (κ.C * X.K n * n * X.D n)) ^ (1 / 8 : ℝ) +
          (κ.C * Real.log n ^ κ.Cl) ^ (1 / 8 : ℝ) * ((n : ℝ) ^ (-200 : ℝ) + p)) := by
  sorry

end ScanData

/-- The defect-energy bound `scanner:energy-output` at a point satisfying the selected density
bound (lines 492–533). For fixed constants, uniformly in the scan data at every sufficiently
large `n`, a point `p ∈ [ε/2, ε]` with `𝒬(p)/(KnD) ≤ δ_n + ρ` has
`E_def ≤ C n^ℓ D² W² (log n)^{C_l} (δ_n^{1/8} + ε + n^{-100}) + C n^{-1000} + Λ (rem_k + ρ^{1/8})`
with `Λ` depending on the fixed data only. -/
theorem exists_defectEnergy_le (X : ScannerExponents) (κ : ScanConstants) (C₁ Cδ : ℝ)
    (hCδ : 0 ≤ Cδ) :
    ∃ C Cl : ℝ, ∀ᶠ n in Filter.atTop, ScaleFacts X n C₁ → ∀ S : ScanData X κ n,
      ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ (r : Fin (X.rounds n)) (k : ℕ) (p ρ : ℝ),
        p ∈ Icc (X.eps n / 2) (X.eps n) → 0 ≤ ρ →
        (S.round r).chargeDefect k p / (X.K n * n * X.D n) ≤ X.delta Cδ κ.Cl n + ρ →
        S.defectEnergy r k p ≤
          C * (n : ℝ) ^ X.ell * (X.D n : ℝ) ^ 2 * X.W ^ 2 * Real.log n ^ Cl *
              (X.delta Cδ κ.Cl n ^ (1 / 8 : ℝ) + X.eps n + (n : ℝ) ^ (-100 : ℝ)) +
            C * (n : ℝ) ^ (-1000 : ℝ) + Λ * (S.rem k + ρ ^ (1 / 8 : ℝ)) := by
  sorry

end TNLean.PEPS.AreaLaw.Scan
