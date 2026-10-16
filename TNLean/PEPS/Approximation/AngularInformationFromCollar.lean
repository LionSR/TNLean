/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/

import TNLean.PEPS.Approximation.AngularAnnularInformationInduction
import TNLean.PEPS.Approximation.AngularSingleScaleReset

/-!
# Angular information from the sublinear collar estimate

For each prescribed accuracy, the cell estimate and information reset give
one logarithmic lower scale that works at every annulus. The finite annular
induction then bounds the mutual information of the original physical
regions in the original ground state. All constants are chosen before the
system size, Hamiltonian, marked points, regions, and scale.

**Scope restriction (sublinear collar bound):** The sublinear collar
estimate remains an explicit premise. This is the corresponding implication
in Proposition 3.4, not a derivation of the collar estimate. See
`docs/paper-gaps/polypeps_angular_annular_geometry_scope.tex`.

Source: polynomial-PEPS manuscript, Proposition 3.4 (`prop:angular`),
`02-information.tex`, lines 635–785, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.Approximation

/-- The sublinear collar estimate at interaction range one implies angular
information decay with all constants uniform over the subsequent physical
systems, marked points, regions, and annular scales.

Source: polynomial-PEPS manuscript, `02-information.tex`, lines 635–785. -/
theorem angularInformationBound_of_sublinearCollarBound {q : ℕ} (hq : 1 ≤ q)
    {J Δ D₀ Ctpl : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hcol : AreaLaw.SublinearCollarBound q 1 J Δ D₀ Ctpl) :
    AngularInformationBound q J Δ := by
  classical
  intro a A₀ ha _hA₀ m₀ p hp
  let a' : ℝ := min a 1 / 200
  have ha' : 0 < a' := div_pos (lt_min ha zero_lt_one) (by norm_num)
  have ha'a : a' < a / 100 :=
    show min a 1 / 200 < a / 100 by linarith [min_le_left a 1]
  have ha'1 : a' ≤ 1 / 200 :=
    div_le_div_of_nonneg_right (min_le_right a 1) (by norm_num)
  let d : ℝ := a' / 8
  have hd : 0 < d := div_pos ha' (by norm_num)
  have hda' : d < a' / 4 :=
    div_lt_div_of_pos_left ha' (by norm_num) (by norm_num)
  have hd1 : d ≤ 1 := show a' / 8 ≤ 1 by linarith
  let N : ℕ := (m₀ + 1) * (2 * ⌈(max A₀ 2 + (3 / 2) * a') / d⌉₊ + 3) ^ 2
  obtain ⟨D, L₀, hD, hL₀, hreset⟩ :=
    exists_angular_single_scale_reset_of_sublinearCollarBound q hq J hJ hΔ hcol
      ha' ha'a hd hda' hd1 hp N
  refine ⟨D, L₀, fun L hL h E₀ Ω hΩ V hV X E _hXE n hn _hnL hdiam hsep ↦ ?_⟩
  have hlog : 1 ≤ Real.log (L : ℝ) :=
    (Real.le_log_iff_exp_le ((Real.exp_pos 1).trans_le (hL₀.trans hL))).2 (hL₀.trans hL)
  have ht : 0 < D * Real.log (L : ℝ) :=
    mul_pos (zero_lt_one.trans_le hD) (zero_lt_one.trans_le hlog)
  let c := chooseDyadicCutoff ht hn
  apply mutualInformation_le_of_annular_reset Ω hΩ.1 (ht.trans_le hn) ha.le ha' ha'a hd hda'
    (Real.rpow_nonneg (Nat.cast_nonneg L) (-p)) hdiam hV hsep c
  intro j hj Aold hAold S hS hcard hold
  refine hreset L hL h E₀ Ω hΩ (dyadicScale n j)
    (c.lower_at (ht.trans_le hn).le hj) (0, 0) Aold
    (cumulativeLayer (sitePosition L '' X) n V c.last j) (sitePosition L '' E)
    hAold ?_ S hS hcard hold
  intro x hx y hy
  simpa only [div_mul_eq_mul_div] using
    cumulativeLayer_separation c (ht.trans_le hn).le ha.le hsep hj hx hy

end TNLean.PEPS.Approximation
