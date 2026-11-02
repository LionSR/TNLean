/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.GaussianFilter.Kernel

/-!
# The actual Gaussian approximation to a negative-frequency selector

The multiplier is the right tail of a centered Gaussian with variance
\(\Delta^2/q\). It lies between zero and one. At frequencies at least
\(\Delta\) it is at most \(e^{-q/2}\); at frequencies at most
\(-\Delta\) it differs from one by at most the same amount.

The bounds are derived from the actual Gaussian moment-generating function
and Mathlib's Chernoff bound, with no tail or approximation hypothesis.
Source: Hastings–Koma, arXiv:math-ph/0507008, Lemma 3.1, equation (3.7),
with \(\alpha=\Delta^2/(2q)\). Identifying this multiplier with the
regularized Cauchy time integral is a separate step.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace TNLean.Lattice

/-- The Gaussian approximation to the negative-frequency step. Its
variance is \(\Delta^2/q\), so the gap tails have the source rate
\(e^{-q/2}\). Source: Hastings–Koma, arXiv:math-ph/0507008,
Lemma 3.1, equation (3.7). -/
def gaussianNegativeFrequencyCutoff (q Δ ω : ℝ) : ℝ :=
  (gaussianReal 0 (Δ ^ 2 / q).toNNReal).real (Set.Ici ω)

private theorem gaussian_gap_rate {q Δ : ℝ} (hq : 0 < q) (hΔ : 0 < Δ) :
    Real.exp (-(Δ ^ 2) / (2 * ((Δ ^ 2 / q).toNNReal : ℝ))) =
      Real.exp (-q / 2) := by
  congr 1
  rw [Real.coe_toNNReal _ (div_nonneg (sq_nonneg Δ) hq.le)]
  field_simp [hq.ne', hΔ.ne']

/-- The actual Gaussian frequency multiplier is nonnegative.
Source: Hastings–Koma, arXiv:math-ph/0507008, equation (3.7). -/
theorem gaussianNegativeFrequencyCutoff_nonneg (q Δ ω : ℝ) :
    0 ≤ gaussianNegativeFrequencyCutoff q Δ ω :=
  measureReal_nonneg

/-- The actual Gaussian frequency multiplier is at most one.
Source: Hastings–Koma, arXiv:math-ph/0507008, equation (3.7). -/
theorem gaussianNegativeFrequencyCutoff_le_one (q Δ ω : ℝ) :
    gaussianNegativeFrequencyCutoff q Δ ω ≤ 1 :=
  measureReal_le_one

/-- Above the actual positive gap, the actual Gaussian selector has the
explicit exponential error. The Gaussian tail bound is proved from its
moment-generating function. Source: Hastings–Koma,
arXiv:math-ph/0507008, Lemma 3.1, equation (3.7). -/
theorem gaussianNegativeFrequencyCutoff_le_exp_of_gap
    {q Δ ω : ℝ} (hq : 0 < q) (hΔ : 0 < Δ) (hω : Δ ≤ ω) :
    gaussianNegativeFrequencyCutoff q Δ ω ≤ Real.exp (-q / 2) := by
  let v := (Δ ^ 2 / q).toNNReal
  calc
    (gaussianReal 0 v).real (Set.Ici ω) ≤
        (gaussianReal 0 v).real {x : ℝ | Δ ≤ x} :=
      measureReal_mono fun _ hx ↦ hω.trans hx
    _ ≤ Real.exp (-(Δ ^ 2) / (2 * (v : ℝ))) :=
      (GaussianFilter.hasSubgaussianMGF_gaussianReal v).measure_ge_le hΔ.le
    _ = _ := gaussian_gap_rate hq hΔ

/-- Below the negative gap, the actual Gaussian selector differs from one
by at most the same explicit exponential error. No symmetry or tail
estimate is assumed: apply the Gaussian moment-generating-function bound
to the negated variable. Source: Hastings–Koma,
arXiv:math-ph/0507008, Lemma 3.1, equation (3.7). -/
theorem abs_one_sub_gaussianNegativeFrequencyCutoff_le_exp_of_gap
    {q Δ ω : ℝ} (hq : 0 < q) (hΔ : 0 < Δ) (hω : ω ≤ -Δ) :
    |1 - gaussianNegativeFrequencyCutoff q Δ ω| ≤ Real.exp (-q / 2) := by
  let v := (Δ ^ 2 / q).toNNReal
  rw [abs_of_nonneg (sub_nonneg.mpr (gaussianNegativeFrequencyCutoff_le_one q Δ ω))]
  calc
    1 - (gaussianReal 0 v).real (Set.Ici ω) =
        (gaussianReal 0 v).real ((Set.Ici ω)ᶜ) :=
      (probReal_compl_eq_one_sub measurableSet_Ici).symm
    _ ≤ (gaussianReal 0 v).real {x : ℝ | Δ ≤ -x} := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      intro x hx
      have hx' : x < ω := by simpa only [Set.mem_compl_iff, Set.mem_Ici, not_le] using hx
      change Δ ≤ -x
      linarith
    _ ≤ Real.exp (-(Δ ^ 2) / (2 * (v : ℝ))) := by
      simpa only [Pi.neg_apply, id_eq] using
        (GaussianFilter.hasSubgaussianMGF_gaussianReal v).neg.measure_ge_le hΔ.le
    _ = _ := gaussian_gap_rate hq hΔ

end TNLean.Lattice
