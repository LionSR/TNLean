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

end TNLean.PEPS.Approximation
