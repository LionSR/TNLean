/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.GaussianFilteredTerm
import QICLean.Analysis.GaussianFilter.CommutatorSeries

/-!
# The corrected commutator series of the actual Gaussian-filtered term

The existing filtered term has variance q/ΔE². Specializing the QICLean
Gaussian identity identifies that actual operator with the exponential
of the squared commutator and with its norm-convergent even series.
No spectral gap, polynomial approximation or new filter is assumed.

**Local fix (Gaussian moments):** the variance occurs to power r at
commutator order 2r, rather than to the printed power 2r. The correction
is owned by QICLean and documented at
https://sirui-lu.com/QICLean/paper-gaps/hastings05_gaussian_series_coefficients.pdf.

Source: Hastings, arXiv:cond-mat/0508554v3, eqs. tnd/thd, lines 194--207,
and the Gaussian variational choice, lines 1005--1009 of proj3new.tex.
-/

open scoped Matrix.Norms.L2Operator NNReal

namespace TNLean.Lattice

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The actual source Gaussian filter is the exponential of
\(-q\operatorname{ad}_H^2/(2\Delta E^2)\). The same existing filter and
commutator operator are retained. Source: Hastings, lines 1005--1009. -/
theorem gaussianFilteredTerm_eq_exp_commutator {q : ℝ} (hq : 0 ≤ q)
    (ΔE : ℝ) {H : Matrix n n ℂ} (hH : H.IsHermitian) (W : Matrix n n ℂ) :
    gaussianFilteredTerm q ΔE H W =
      NormedSpace.exp ((-((q / ΔE ^ 2 : ℝ) : ℂ) / 2) •
        GaussianFilter.commutatorCLM H ^ 2) W := by
  rw [gaussianFilteredTerm,
    GaussianFilter.gaussianIntertwiner_eq_exp_commutator (q / ΔE ^ 2).toNNReal hH W,
    Real.coe_toNNReal _ (div_nonneg hq (sq_nonneg ΔE))]

/-- The actual source Gaussian-filtered term is the operator-norm sum
of the even commutators, with coefficient
\((-q/(2\Delta E^2))^r/r!\) at order \(2r\).
Source: Hastings, lines 1005--1009, with the module's moment correction. -/
theorem hasSum_gaussianFilteredTerm_commutator {q : ℝ} (hq : 0 ≤ q)
    (ΔE : ℝ) {H : Matrix n n ℂ} (hH : H.IsHermitian) (W : Matrix n n ℂ) :
    HasSum (fun r : ℕ ↦
      ((-((q / ΔE ^ 2 : ℝ) : ℂ) / 2) ^ r / (r.factorial : ℂ)) •
        ((GaussianFilter.commutatorCLM H) ^ (2 * r)) W)
      (gaussianFilteredTerm q ΔE H W) := by
  have hs := GaussianFilter.hasSum_gaussianIntertwiner_commutator (q / ΔE ^ 2).toNNReal hH W
  rw [Real.coe_toNNReal _ (div_nonneg hq (sq_nonneg ΔE))] at hs
  exact hs

end TNLean.Lattice
