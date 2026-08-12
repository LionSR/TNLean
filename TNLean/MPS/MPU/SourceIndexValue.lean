/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SourceCuts
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Source-index value of a specified MPU tensor

This module defines the numerical source-index expression of a specified tensor
from its right and left source-cut ranks. It does not choose a simple blocking
and therefore does not define the choice-independent index of an MPU.

For a tensor with right rank $r$ and left rank $\ell$, the value is
$$
\frac{1}{2}(\log_2 r-\log_2 \ell).
$$
A common nonzero scaling of both ranks cancels from this expression. If the
supplied ranks satisfy $r\ell=d^2$, the expression also has the two equivalent
forms $\log_2(r/d)$ and $-\log_2(\ell/d)$.

These are the algebraic parts of arXiv:1703.09188, Definition IV.1 and the
following paragraph, lines 681--688. Proposition IV.2, which proves independence
of the chosen simple blocking, is not asserted here.

## Main definitions and results

* `MPOTensor.sourceIndexValue`: the source-index value of a specified tensor.
* `MPOTensor.sourceIndexValue_eq_of_common_rank_scale`: cancellation of a
  supplied common nonzero rank scale.
* `MPOTensor.sourceIndexValue_eq_logb_rightRank_div`: the right-rank formula
  under a supplied rank-product equality.
* `MPOTensor.sourceIndexValue_eq_neg_logb_leftRank_div`: the left-rank formula
  under a supplied rank-product equality.
-/

namespace MPOTensor

variable {d D e E : ℕ}

/-- The source-index value of a specified tensor, computed from its right and
left source-cut ranks:
$$
\frac{1}{2}(\log_2 r-\log_2 \ell).
$$

This is the numerical expression in arXiv:1703.09188, Definition IV.1, lines
681--686. It makes no choice of a simple blocking. -/
noncomputable def sourceIndexValue (U : MPOTensor d D) : ℝ :=
  (1 / 2 : ℝ) * (Real.logb 2 r[U] - Real.logb 2 ℓ[U])

/-- Multiplying both source ranks by the same nonzero natural number does not
change the source-index value.

This is the logarithmic cancellation used in the proof of arXiv:1703.09188,
Proposition IV.2, lines 697--704, stated only for two specified tensors and
supplied rank equalities. -/
theorem sourceIndexValue_eq_of_common_rank_scale
    (U : MPOTensor d D) (V : MPOTensor e E) (c : ℕ) (hc : c ≠ 0)
    (hrU : r[U] ≠ 0) (hℓU : ℓ[U] ≠ 0)
    (hr : r[V] = c * r[U]) (hℓ : ℓ[V] = c * ℓ[U]) :
    sourceIndexValue V = sourceIndexValue U := by
  rw [sourceIndexValue, sourceIndexValue, hr, hℓ]
  norm_cast at hc hrU hℓU
  rw [Real.logb_mul hc hrU, Real.logb_mul hc hℓU]
  ring

/-- If the supplied source ranks satisfy $r\ell=d^2$ and $d$ is nonzero, then
its source-index value is $\log_2(r/d)$.

This is the first equivalent formula following arXiv:1703.09188, Definition
IV.1, lines 686--688. -/
theorem sourceIndexValue_eq_logb_rightRank_div (U : MPOTensor d D)
    (hd : d ≠ 0) (hprod : r[U] * ℓ[U] = d ^ 2) :
    sourceIndexValue U = Real.logb 2 ((r[U] : ℝ) / d) := by
  have hr : r[U] ≠ 0 := by
    intro h
    simp [h, hd] at hprod
  have hℓ : ℓ[U] ≠ 0 := by
    intro h
    simp [h, hd] at hprod
  norm_cast at hd hr hℓ
  have hprodReal : (r[U] : ℝ) * (ℓ[U] : ℝ) = (d : ℝ) * d := by
    exact_mod_cast hprod.trans (pow_two d)
  have hlog := congrArg (Real.logb 2) hprodReal
  rw [Real.logb_mul hr hℓ, Real.logb_mul hd hd] at hlog
  rw [sourceIndexValue, Real.logb_div hr hd]
  linarith

/-- If the supplied source ranks satisfy $r\ell=d^2$ and $d$ is nonzero, then
its source-index value is $-\log_2(\ell/d)$.

This is the second equivalent formula following arXiv:1703.09188, Definition
IV.1, lines 686--688. -/
theorem sourceIndexValue_eq_neg_logb_leftRank_div (U : MPOTensor d D)
    (hd : d ≠ 0) (hprod : r[U] * ℓ[U] = d ^ 2) :
    sourceIndexValue U = -Real.logb 2 ((ℓ[U] : ℝ) / d) := by
  have hr : r[U] ≠ 0 := by
    intro h
    simp [h, hd] at hprod
  have hℓ : ℓ[U] ≠ 0 := by
    intro h
    simp [h, hd] at hprod
  norm_cast at hd hr hℓ
  have hprodReal : (r[U] : ℝ) * (ℓ[U] : ℝ) = (d : ℝ) * d := by
    exact_mod_cast hprod.trans (pow_two d)
  have hlog := congrArg (Real.logb 2) hprodReal
  rw [Real.logb_mul hr hℓ, Real.logb_mul hd hd] at hlog
  rw [sourceIndexValue, Real.logb_div hℓ hd]
  linarith

end MPOTensor
