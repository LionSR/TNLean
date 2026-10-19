/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.AngularInformationFromCollar
import TNLean.PEPS.Approximation.CellConditionalInformationFromGap

/-!
# Angular information from the original spectral gap

The original full-system gap gives angular information decay uniformly in the Hamiltonian,
ground vector, marked points and physical regions. The physical sublinear collar theorem
at range one, clearance 13 and template constant 24 supplies the premise of the conditional
angular information theorem. No area-law or collar estimate is assumed. At the transport
constants of the companion library, the slope `angularScale J Δ a p` and the size threshold
`angularThresholdClosed q J Δ a A₀ m₀ p` are closed-form functions of the parameters.

Source: polynomial-PEPS manuscript, Proposition 3.4, `02-information.tex`, lines 635–785,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.Approximation

/-- Angular information decay in an original gapped square-grid ground state,
with all scale constants chosen before the physical system and regions.
Source: polynomial-PEPS manuscript, Proposition 3.4, `02-information.tex`,
lines 635–785, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The statement includes local dimension one and interaction bound zero, and
assumes no collar, area-law or two-family decomposition estimate. -/
theorem angularInformationBound {q : ℕ} (hq : 1 ≤ q)
    {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    AngularInformationBound q J Δ := by
  have hcol : AreaLaw.SublinearCollarBound q 1 J Δ 13 24 :=
    AreaLaw.sublinearCollarBound_real q 1 hq hJ hΔ (by norm_num) (by norm_num)
  exact angularInformationBound_of_sublinearCollarBound hq hJ hΔ hcol

/-- The size threshold of Proposition 3.4 at closed-form constants: `angularThreshold` at the
template constant `24`, the collar threshold `collarThresholdClosed q J Δ`, and the
amplification constant and threshold at the collar constant `collarConstantClosed q J Δ`.
Source: polynomial-PEPS manuscript, Proposition 3.4 (`prop:angular`), `02-information.tex`,
lines 635–785. -/
noncomputable def angularThresholdClosed (q : ℕ) (J Δ a A₀ : ℝ) (m₀ : ℕ) (p : ℝ) : ℝ :=
  angularThreshold q J Δ a A₀ m₀ p 24 (collarThresholdClosed q J Δ)
    (collarAmplificationConstant q 1 J Δ (collarConstantClosed q J Δ))
    (collarAmplificationThreshold q 1 J Δ (collarConstantClosed q J Δ))

/-- **Proposition 3.4 at an integer accuracy, at closed-form constants.** For `q ≥ 1`,
`J ≥ 0`, `Δ > 0`, `a > 0`, `m₀ ∈ ℕ` and an integer `p > 0`, every slope
`D ≥ angularScale J Δ a p` and every threshold `L₀ ≥ angularThresholdClosed q J Δ a A₀ m₀ p`
form an angular scale. There is no collar or amplification premise.
Source: polynomial-PEPS manuscript, Proposition 3.4 (`prop:angular`), `02-information.tex`,
lines 635–785; `06-geometry.tex`, lines 62–63 and 440–445. -/
theorem isAngularScale_closed_le {q : ℕ} (hq : 1 ≤ q) {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    {a A₀ : ℝ} (ha : 0 < a) (m₀ : ℕ) {p : ℕ} (hp : 0 < p) {D L₀ : ℝ}
    (hD : angularScale J Δ a p ≤ D) (hL₀ : angularThresholdClosed q J Δ a A₀ m₀ p ≤ L₀) :
    IsAngularScale q J Δ a A₀ m₀ p D L₀ :=
  isAngularScale_of_sublinearCollarBoundAt_le_explicit hq hJ hΔ
    (sublinearCollarBoundAt_closed hq hJ hΔ) ha m₀ hp hD hL₀

/-- Uniform angular slopes and thresholds can exceed any prescribed lower bounds.
The positive slope and threshold are chosen before every finite physical instance,
translated site placement, marked set and pair of regions.
Source: polynomial-PEPS manuscript, Proposition 3.4 (`prop:angular`),
`02-information.tex`, lines 635–658, and the choice of a sufficiently large
fixed slope in `06-geometry.tex`, lines 440–445, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem exists_isAngularScale_ge
    {q : ℕ} (hq : 1 ≤ q) {J Δ a A₀ : ℝ}
    (hJ : 0 ≤ J) (hΔ : 0 < Δ) (ha : 0 < a)
    (hA₀ : 1 ≤ A₀) (m₀ : ℕ) {p : ℕ} (hp : 0 < p)
    (Dmin Lmin : ℝ) :
    ∃ D L₀ : ℝ, max Dmin 1 ≤ D ∧ max Lmin 2 ≤ L₀ ∧
      IsAngularScale q J Δ a A₀ m₀ p D L₀ := by
  obtain ⟨D₁, L₁, hscale⟩ :=
    (angularInformationBound hq hJ hΔ).exists_isAngularScale ha hA₀ m₀ hp
  refine ⟨max D₁ (max Dmin 1), max L₁ (max Lmin 2),
    le_max_right _ _, le_max_right _ _, ?_⟩
  intro L hL h E₀ Ω hΩ pos c hpos V hV X E hXE n hn hnL hdiam hsep
  have hlog : 0 ≤ Real.log (L : ℝ) := Real.log_nonneg (by
    have h2 := (le_max_right Lmin 2).trans
      ((le_max_right L₁ (max Lmin 2)).trans hL)
    linarith only [h2])
  have hfloor : D₁ * Real.log (L : ℝ) ≤
      max D₁ (max Dmin 1) * Real.log (L : ℝ) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hlog
  exact hscale L ((le_max_left _ _).trans hL) h E₀ Ω hΩ
    pos c hpos V hV X E hXE n (hfloor.trans hn) hnL hdiam
    (fun x hx y hy ↦
      (mul_le_mul_of_nonneg_left
        (max_le_max_right _ hfloor) ha.le).trans (hsep x hx y hy))

end TNLean.PEPS.Approximation
