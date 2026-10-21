/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.BootstrapRoundBound
import TNLean.PEPS.AreaLaw.Scan.PhysicalBoxBootstrap

/-!
# A bounded round count in the physical safe-box estimate

The physical entropy estimate uses a single round count bounded by
`initialBoxBootstrapRoundBound`, uniformly in the safety parameter and scale.
Its coefficient remains the bootstrap recurrence evaluated at that count.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*,
proof of Proposition 9.5, `08-scanner.tex`, lines 788–805, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
This is an auxiliary quantitative deduction using the cyclic-color initial
constants. Independently proved; no upstream Lean proof text reused.
-/

namespace TNLean.PEPS.AreaLaw.Scan

/-- The physical safe-box estimate has a uniform round count `m` within the explicit budget,
with the actual coefficient `C_m` of the bootstrap recurrence. This auxiliary deduction from
Proposition 9.5 (`08-scanner.tex`, lines 788–805) leaves the physical and transport parameters
visible and does not require monotonicity of the coefficient sequence. -/
theorem exists_boxEntropy_le_boxError_bounded_rounds
    (q R : ℕ) (hq : 1 ≤ q) {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    {ct Cent eent Cen een : ℝ} (hct : 0 < ct)
    (htransport : CollarScan.FiniteFamilyTransportBound ct Cent eent Cen een) :
    ∃ m : ℕ, m ≤ initialBoxBootstrapRoundBound q R J Δ ∧
      ∀ D₀ : ℕ, 2 * R + 10 < D₀ → ∀ r : ℕ, 1 ≤ r → boxEntropy q R J Δ D₀ r ≤
        boxBootstrapConstant (Real.log q)
          (boxImprovementConstant q R (initialBoxExponent_pos_and_lt_one q R J Δ).1
            (initialBoxExponent_pos_and_lt_one q R J Δ).2 J Δ
            (latticeTruncationRadiusConstant R J Δ 2) ct Cent eent Cen een)
          (fun _ ↦ 1) (initialBoxConstantExplicit q R J Δ) m *
          (r : ℝ) ^ (1 + (Exponents.boxError : ℝ)) := by
  refine ⟨_, boxBootstrapRounds_initial_le q R J Δ, ?_⟩
  exact boxEntropy_le_boxError_explicit q R hq hJ hΔ hct htransport

end TNLean.PEPS.AreaLaw.Scan
