/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.AngularInformationFromCollar
import TNLean.PEPS.AreaLaw.PhysicalCollarInformation

/-!
# Angular information from the original spectral gap

The original full-system gap gives angular information decay uniformly in the Hamiltonian,
ground vector, marked points and physical regions. The physical sublinear collar theorem
at range one, clearance 13 and template constant 24 supplies the premise of the conditional
angular information theorem. No area-law or collar estimate is assumed.

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
