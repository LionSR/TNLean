/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RegularizedPatchRadiusDerivative
import TNLean.PEPS.AreaLaw.RegularizedPatchMinimizerStationarity

/-!
# The logarithmic radius derivative at an original patch minimum

For a fixed minimizing density tuple, the original logarithmic objective has
the canonical marginal derivative at the radius where the tuple minimizes.
The commutations used in the ordered trace calculation follow from that minimum.
No choice of a family of minimizers is differentiated.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states*, September 24, 2026, `03-patches.tex`, lines 453–466; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {n : V → ℕ} {m : ℕ}

/-- The fixed minimizing tuple has the stated full radius derivative.
All filter commutations are derived from the same actual norm minimum.
Source: polynomial-PEPS manuscript, `03-patches.tex`, lines 453–466. -/
theorem hasDerivAt_log_regularizedPatchObjective_exp_neg_of_isMinOn
    (regions : Fin m → Finset V) (hnested : Monotone regions)
    (a : Fin m → ℝ) (ha : ∀ j, 0 < a j)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Fin (n v.1)))
    (hΩ : ‖Ω‖ = 1)
    (x : ∀ j, Matrix (Entropy.RegionConfig n (regions j))
      (Entropy.RegionConfig n (regions j)) ℂ)
    (hx : x ∈ regularizedPatchDomain (Out := fun v ↦ Fin (n v)) regions) (R : ℝ)
    (hmin : IsMinOn
      (regularizedPatchObjective (Out := fun v ↦ Fin (n v))
        regions a (Real.exp (-R)) Ω)
      (regularizedPatchDomain (Out := fun v ↦ Fin (n v)) regions) x) :
    HasDerivAt
      (fun r : ℝ ↦ Real.log
        (regularizedPatchObjective (Out := fun v ↦ Fin (n v))
          regions a (Real.exp (-r)) Ω x))
      (∑ j, (a j / 2) *
        (Matrix.trace
          (normalizedRegularizedPatchMarginal (Out := fun v ↦ Fin (n v))
            regions a (Real.exp (-R)) Ω x (regions j) *
            (Real.exp (-R) • (x j + Real.exp (-R) • 1) ^ (-1 : ℝ)))).re) R := by
  apply hasDerivAt_log_regularizedPatchObjective_exp_neg_of_outer_commute
    regions hnested a (fun j ↦ (ha j).le) Ω hΩ x hx R
  intro _j k _hjk
  exact commute_filter_normalizedRegularizedPatchMarginal_of_isMinOn
    regions hnested a ha (Real.exp_pos (-R)) Ω x hx hmin k

end TNLean.PEPS
