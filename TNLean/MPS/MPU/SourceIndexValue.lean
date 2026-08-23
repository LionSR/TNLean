/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.BlockingRanks
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Source-index value of a specified MPU tensor

This module defines the numerical source-index expression of a specified tensor
from its positive right and left source-cut ranks. It does not choose a simple
blocking and therefore does not define the choice-independent index of an MPU.

For a tensor with positive right rank $r$ and left rank $\ell$, the value is
$$
\frac{1}{2}(\log_2 r-\log_2 \ell).
$$
A common positive scaling of both ranks cancels from this expression. If the
supplied ranks satisfy $r\ell=d^2$, the expression also has the two equivalent
forms $\log_2(r/d)$ and $-\log_2(\ell/d)$.

These are the algebraic parts of arXiv:1703.09188, Definition IV.1 and the
following paragraph, lines 681--688. Proposition IV.2, which proves independence
of the chosen simple blocking, is not asserted here.

## Main definitions

* `MPOTensor.sourceIndexValue`: the source-index value of a specified tensor
  whose two source ranks are positive.

## Main results

* `MPOTensor.sourceIndexValue_eq_of_common_rank_scale`: cancellation of a
  supplied common positive rank scale.
* `MPOTensor.sourceIndexValue_blockTensor_eq_of_products`: blocking invariance
  under supplied endpoint rank-product identities.
* `MPOTensor.sourceIndexValue_eq_add_of_common_rank_product`: additivity from
  supplied source-rank product identities with a common positive factor.
* `MPOTensor.sourceIndexValue_eq_logb_rightRank_div`: the right-rank formula
  under a supplied rank-product equality.
* `MPOTensor.sourceIndexValue_eq_neg_logb_leftRank_div`: the left-rank formula
  under a supplied rank-product equality.
-/

namespace MPOTensor

variable {d D e E f F : ℕ}

/-- The source-index value of a specified tensor with positive right and left
source-cut ranks:
$$
\frac{1}{2}(\log_2 r-\log_2 \ell).
$$

This is the numerical expression in arXiv:1703.09188, Definition IV.1, lines
681--686. It makes no choice of a simple blocking. -/
noncomputable def sourceIndexValue (U : MPOTensor d D)
    (_hr : 0 < r[U]) (_hℓ : 0 < ℓ[U]) : ℝ :=
  (1 / 2 : ℝ) * (Real.logb 2 r[U] - Real.logb 2 ℓ[U])

/-- Multiplying both positive source ranks by the same positive natural number
does not change the source-index value.

This is the logarithmic cancellation used in the proof of arXiv:1703.09188,
Proposition IV.2, lines 697--704, stated only for two specified tensors and
supplied rank equalities. -/
theorem sourceIndexValue_eq_of_common_rank_scale
    (U : MPOTensor d D) (V : MPOTensor e E) (c : ℕ) (hc : 0 < c)
    (hrU : 0 < r[U]) (hℓU : 0 < ℓ[U])
    (hr : r[V] = c * r[U]) (hℓ : ℓ[V] = c * ℓ[U]) :
    sourceIndexValue V (hr.symm ▸ Nat.mul_pos hc hrU) (hℓ.symm ▸ Nat.mul_pos hc hℓU) =
      sourceIndexValue U hrU hℓU := by
  rw [sourceIndexValue, sourceIndexValue, hr, hℓ, Nat.cast_mul, Nat.cast_mul]
  have hcReal : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  have hrReal : (r[U] : ℝ) ≠ 0 := by exact_mod_cast hrU.ne'
  have hℓReal : (ℓ[U] : ℝ) ≠ 0 := by exact_mod_cast hℓU.ne'
  rw [Real.logb_mul hcReal hrReal, Real.logb_mul hcReal hℓReal]
  ring

/-- Suppose $k₀ \le k$, the physical dimension $d$ is positive, and the
endpoint source ranks satisfy
$$
r_{k₀}\ell_{k₀}=d^{2k₀}, \qquad r_k\ell_k=d^{2k}.
$$
Then the specified source-index values of the two blocked tensors agree.

This composes the rank-growth and logarithmic-cancellation steps in
arXiv:1703.09188, Proposition IV.2, lines 697--704. The endpoint product
identities are explicit hypotheses. Their positivity consequences supply the
rank positivity required by the specified source-index value. This theorem
neither chooses a simple blocking nor asserts the public blocking-independent
index.

**Local fix (rank-product exponent):** Source line 703 prints $d^k$; consistently
with Theorem III.8 and the blocked physical dimension $d^k$, the endpoint
product is $d^{2k}$. See
`docs/paper-gaps/mpu_blocking_rank_product_exponent.tex`. -/
theorem sourceIndexValue_blockTensor_eq_of_products (U : MPOTensor d D) {k₀ k : ℕ}
    (h : k₀ ≤ k) (hd : 0 < d)
    (hprod₀ : r[blockTensor U k₀] * ℓ[blockTensor U k₀] = d ^ (2 * k₀))
    (hprod : r[blockTensor U k] * ℓ[blockTensor U k] = d ^ (2 * k)) :
    sourceIndexValue (blockTensor U k)
        (Nat.pos_of_mul_pos_right (hprod.symm ▸ Nat.pow_pos hd))
        (Nat.pos_of_mul_pos_left (hprod.symm ▸ Nat.pow_pos hd)) =
      sourceIndexValue (blockTensor U k₀)
        (Nat.pos_of_mul_pos_right (hprod₀.symm ▸ Nat.pow_pos hd))
        (Nat.pos_of_mul_pos_left (hprod₀.symm ▸ Nat.pow_pos hd)) := by
  have hr : 0 < r[blockTensor U k] :=
    Nat.pos_of_mul_pos_right (hprod.symm ▸ Nat.pow_pos hd)
  have hℓ : 0 < ℓ[blockTensor U k] :=
    Nat.pos_of_mul_pos_left (hprod.symm ▸ Nat.pow_pos hd)
  have hr₀ : 0 < r[blockTensor U k₀] :=
    Nat.pos_of_mul_pos_right (hprod₀.symm ▸ Nat.pow_pos hd)
  have hℓ₀ : 0 < ℓ[blockTensor U k₀] :=
    Nat.pos_of_mul_pos_left (hprod₀.symm ▸ Nat.pow_pos hd)
  change sourceIndexValue (blockTensor U k) hr hℓ =
    sourceIndexValue (blockTensor U k₀) hr₀ hℓ₀
  obtain ⟨hrScale, hℓScale⟩ :=
    blockingRanks_eq_pow_mul_of_products U h hd hprod₀ hprod
  exact sourceIndexValue_eq_of_common_rank_scale
    (blockTensor U k₀) (blockTensor U k) (d ^ (k - k₀)) (Nat.pow_pos hd)
    hr₀ hℓ₀ hrScale hℓScale

/-- Suppose the right and left source ranks of specified tensors $U$, $V$, and
$W$ satisfy
$$
r[W] = c\,r[U]r[V], \qquad \ell[W] = c\,\ell[U]\ell[V]
$$
for a positive natural number $c$. Then the base-$2$ source-index value of $W$
is the sum of those of $U$ and $V$.

This is the logarithmic cancellation in arXiv:1703.09188, Theorem `IndexTh`
(ii), lines 837--845. It is a specified-tensor logarithmic cancellation lemma,
not the public blocking-independent MPU index. -/
theorem sourceIndexValue_eq_add_of_common_rank_product
    (U : MPOTensor d D) (V : MPOTensor e E) (W : MPOTensor f F)
    (c : ℕ) (hc : 0 < c)
    (hrU : 0 < r[U]) (hℓU : 0 < ℓ[U])
    (hrV : 0 < r[V]) (hℓV : 0 < ℓ[V])
    (hrW : 0 < r[W]) (hℓW : 0 < ℓ[W])
    (hr : r[W] = c * r[U] * r[V]) (hℓ : ℓ[W] = c * ℓ[U] * ℓ[V]) :
    sourceIndexValue W hrW hℓW =
      sourceIndexValue U hrU hℓU + sourceIndexValue V hrV hℓV := by
  rw [sourceIndexValue, sourceIndexValue, sourceIndexValue, hr, hℓ,
    Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]
  have hcReal : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  have hrUReal : (r[U] : ℝ) ≠ 0 := by exact_mod_cast hrU.ne'
  have hℓUReal : (ℓ[U] : ℝ) ≠ 0 := by exact_mod_cast hℓU.ne'
  have hrVReal : (r[V] : ℝ) ≠ 0 := by exact_mod_cast hrV.ne'
  have hℓVReal : (ℓ[V] : ℝ) ≠ 0 := by exact_mod_cast hℓV.ne'
  rw [Real.logb_mul (mul_ne_zero hcReal hrUReal) hrVReal,
    Real.logb_mul hcReal hrUReal,
    Real.logb_mul (mul_ne_zero hcReal hℓUReal) hℓVReal,
    Real.logb_mul hcReal hℓUReal]
  ring

/-- If the supplied source ranks satisfy $r\ell=d^2$ and $d$ is positive, then
its source-index value is $\log_2(r/d)$.

This is the first equivalent formula following arXiv:1703.09188, Definition
IV.1, lines 686--688. -/
theorem sourceIndexValue_eq_logb_rightRank_div (U : MPOTensor d D)
    (hr : 0 < r[U]) (hℓ : 0 < ℓ[U]) (hd : 0 < d)
    (hprod : r[U] * ℓ[U] = d ^ 2) :
    sourceIndexValue U hr hℓ = Real.logb 2 ((r[U] : ℝ) / d) := by
  have hdReal : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hrReal : (r[U] : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hℓReal : (ℓ[U] : ℝ) ≠ 0 := by exact_mod_cast hℓ.ne'
  have hprodReal : (r[U] : ℝ) * (ℓ[U] : ℝ) = (d : ℝ) * d := by
    exact_mod_cast hprod.trans (pow_two d)
  have hlog := congrArg (Real.logb 2) hprodReal
  rw [Real.logb_mul hrReal hℓReal, Real.logb_mul hdReal hdReal] at hlog
  rw [sourceIndexValue, Real.logb_div hrReal hdReal]
  linarith

/-- If the supplied source ranks satisfy $r\ell=d^2$ and $d$ is positive, then
its source-index value is $-\log_2(\ell/d)$.

This is the second equivalent formula following arXiv:1703.09188, Definition
IV.1, lines 686--688. -/
theorem sourceIndexValue_eq_neg_logb_leftRank_div (U : MPOTensor d D)
    (hr : 0 < r[U]) (hℓ : 0 < ℓ[U]) (hd : 0 < d)
    (hprod : r[U] * ℓ[U] = d ^ 2) :
    sourceIndexValue U hr hℓ = -Real.logb 2 ((ℓ[U] : ℝ) / d) := by
  have hdReal : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hrReal : (r[U] : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hℓReal : (ℓ[U] : ℝ) ≠ 0 := by exact_mod_cast hℓ.ne'
  have hprodReal : (r[U] : ℝ) * (ℓ[U] : ℝ) = (d : ℝ) * d := by
    exact_mod_cast hprod.trans (pow_two d)
  have hlog := congrArg (Real.logb 2) hprodReal
  rw [Real.logb_mul hrReal hℓReal, Real.logb_mul hdReal hdReal] at hlog
  rw [sourceIndexValue, Real.logb_div hℓReal hdReal]
  linarith

end MPOTensor
