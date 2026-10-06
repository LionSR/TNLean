/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.PeriodicFullRingString
import TNLean.MPS.Examples.StringOrderScalarPhase

/-!
# Existing canonical phase example on the actual periodic ring

This reuses the existing four independent physical letters and canonical
purity proof. No new tensor or new source-error classification is introduced.
The finite physical expectation, rather than a stationary boundary proxy,
oscillates under the source-allowed nonidentity scalar twist.

**Local fix (full-ring phase):** The complex limit printed in the source's
`RL` passage is phase-sensitive. This example uses actual periodic
expectations and retains that phase, as recorded in
`docs/paper-gaps/pgwsvc08_string_order_virtual_boundary.tex`.

## References

* Pérez-García, Wolf, Sanz, Verstraete, Cirac, arXiv:0802.0447,
  the periodic overlap in display `RL`, lines 381–388.
-/

open scoped Matrix BigOperators InnerProductSpace
open Filter

namespace MPSTensor

/-- A nonreal scalar twist has the same, unconjugated length phase in the
actual normalized expectation. This distinguishes the ket-action orientation
from its complex conjugate at odd lengths. -/
theorem stringPhaseTensor_fullRing_I_eq_pow (L : ℕ)
    (hL : mpvState stringPhaseTensor L ≠ 0) :
    mpvExpectation stringPhaseTensor L
      (Matrix.finKronecker fun _ : Fin L =>
        Complex.I • (1 : Matrix (Fin 4) (Fin 4) ℂ)) = Complex.I ^ L := by
  apply mpvExpectation_finKronecker_const_eq_phase_pow stringPhaseTensor
    (Complex.I • 1) 1 Complex.I (by simp) ?_ L hL
  intro i
  simp [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, ite_smul]

/-- The already formalized faithful pure tensor has no complex full-ring
limit for the scalar twist `-1`. This only checks phase-sensitive convergence. -/
theorem stringPhaseTensor_fullRing_neg_one_not_tendsto :
    ¬ ∃ z : ℂ, Tendsto (fun L : ℕ => mpvExpectation stringPhaseTensor L
      (Matrix.finKronecker fun _ : Fin L => (-1 : Matrix (Fin 4) (Fin 4) ℂ)))
      atTop (nhds z) := by
  apply pureCanonical_mpvExpectation_fullRing_not_tendsto stringPhaseTensor
    ((1 / 2 : ℂ) • 1) stringPhaseTensor_canonical.1
    stringPhaseTensor_canonical.2.1 stringPhaseTensor_canonical.2.2
    stringPhaseTensor_unital stringPhaseTensor_pure
    (-1) 1 (-1) (by simp) (by simp) (by norm_num)
  intro i
  simp [Matrix.one_apply, neg_smul]

end MPSTensor
