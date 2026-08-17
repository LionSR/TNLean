/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Positive
import TNLean.Analysis.PositiveGapTransfer

/-!
# Weighted sums of positive operators

Kernel equality and Loewner comparison for strictly positively weighted
finite sums of positive operators, with the resulting gap transfer.  The
statements are the analytic content of the blocked-sum comparison in
Rozmán--Molnár--Schuch, arXiv:2607.19078v1, Lemma `block-obc`
(statement at main.tex lines 607--651, argument at lines 795--811).  That
source expands the blocked parent Hamiltonian as a weighted sum
$\sum_i \gamma_i h_i$ of positive local terms with real coefficients
$0 < \gamma_i \le 1$: strict positivity of the coefficients preserves the
kernel, and the bound $\gamma_i \le 1$ places the weighted sum below the
unweighted sum in Loewner order.  The source tex is not vendored in this
repository, so the citation is by arXiv identifier and lemma label.

## Main results

* `LinearMap.IsPositive.apply_eq_zero_of_re_inner_eq_zero`: a positive
  operator annihilates a vector as soon as its quadratic form vanishes on
  that vector.
* `WeightedPositiveKernel.ker_weighted_sum_eq_sum`: strictly positive real
  weights do not change the kernel of a finite sum of positive operators;
  `WeightedPositiveKernel.ker_weighted_sum_eq_iInf` identifies the common
  kernel with the intersection of the individual kernels.
* `WeightedPositiveKernel.weighted_sum_le_sum`: weights at most one place the
  weighted sum below the unweighted sum in Loewner order.
* `WeightedPositiveKernel.norm_gap_sum_of_weighted_sum`: under both
  conditions on the weights, a norm gap of the weighted sum on the
  orthogonal complement of its kernel is inherited by the unweighted sum.
-/

open scoped InnerProductSpace

namespace LinearMap.IsPositive

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A positive operator annihilates a vector on which its quadratic form
vanishes: `Re ⟪T v, v⟫ = 0` forces `T v = 0`.

The proof uses the positivity of the quadratic form along the real affine
line `t ↦ v + t • (T v)`: it is nonnegative for every real `t`, vanishes at
`t = 0`, and its linear coefficient is `2 * ‖T v‖ ^ 2`, which forces
`‖T v‖ = 0`. -/
theorem apply_eq_zero_of_re_inner_eq_zero {T : E →ₗ[𝕜] E} (hT : T.IsPositive)
    {v : E} (hv : RCLike.re (⟪T v, v⟫_𝕜) = 0) : T v = 0 := by
  by_contra hne
  have hsq : (0 : ℝ) < ‖T v‖ ^ 2 := pow_pos (norm_pos_iff.mpr hne) 2
  have hc : (0 : ℝ) ≤ RCLike.re (⟪T (T v), T v⟫_𝕜) := hT.re_inner_nonneg_left (T v)
  -- The quadratic form is nonnegative along the real affine line, with
  -- constant term `0` and linear coefficient `2 * ‖T v‖ ^ 2`.
  have hline : ∀ t : ℝ,
      0 ≤ 2 * t * (‖T v‖ ^ 2) + t ^ 2 * RCLike.re (⟪T (T v), T v⟫_𝕜) := by
    intro t
    have hpos := hT.re_inner_nonneg_left (v + (t : 𝕜) • T v)
    have hexp : RCLike.re (⟪T (v + (t : 𝕜) • T v), v + (t : 𝕜) • T v⟫_𝕜)
        = 2 * t * (‖T v‖ ^ 2) + t ^ 2 * RCLike.re (⟪T (T v), T v⟫_𝕜) := by
      have hTv : T (v + (t : 𝕜) • T v) = T v + (t : 𝕜) • T (T v) := by
        rw [map_add, map_smul]
      have hsymm : ⟪T (T v), v⟫_𝕜 = ⟪T v, T v⟫_𝕜 := hT.isSymmetric (T v) v
      have hself : RCLike.re (⟪T v, T v⟫_𝕜) = ‖T v‖ ^ 2 := inner_self_eq_norm_sq _
      rw [hTv]
      simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
        RCLike.conj_ofReal, map_add, RCLike.re_ofReal_mul, hsymm, hself, hv]
      ring
    rwa [hexp] at hpos
  -- At negative times, `2 * t * ‖T v‖ ^ 2 ≤ t ^ 2 * re ⟪T (T v), T v⟫`, so
  -- dividing by any positive `t` gives `2 * ‖T v‖ ^ 2 ≤ t * re ⟪T (T v), T v⟫`.
  have hkey : ∀ t : ℝ, 0 < t →
      2 * (‖T v‖ ^ 2) ≤ t * RCLike.re (⟪T (T v), T v⟫_𝕜) := by
    intro t ht
    have h := hline (-t)
    have h2 : (2 * (‖T v‖ ^ 2)) * t
        ≤ (t * RCLike.re (⟪T (T v), T v⟫_𝕜)) * t := by
      nlinarith [mul_nonneg (sq_nonneg t) hc]
    exact le_of_mul_le_mul_right h2 ht
  -- Evaluate at the positive time `‖T v‖ ^ 2 / (re ⟪T (T v), T v⟫ + 1)`.
  have hden : (0 : ℝ) < RCLike.re (⟪T (T v), T v⟫_𝕜) + 1 := by linarith
  have hsmall := hkey ((‖T v‖ ^ 2) / (RCLike.re (⟪T (T v), T v⟫_𝕜) + 1))
    (div_pos hsq hden)
  have hfrac : ((‖T v‖ ^ 2) / (RCLike.re (⟪T (T v), T v⟫_𝕜) + 1))
      * RCLike.re (⟪T (T v), T v⟫_𝕜) ≤ ‖T v‖ ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith [sq_nonneg ‖T v‖]
  linarith

end LinearMap.IsPositive

namespace WeightedPositiveKernel

variable {ι 𝕜 E : Type*} [Fintype ι] [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]

/-- The quadratic form of a weighted sum of operators expands into the
weighted sum of the individual quadratic forms. -/
theorem re_inner_weighted_sum_apply (w : ι → ℝ) (P : ι → E →ₗ[𝕜] E) (v : E) :
    RCLike.re (⟪(∑ i, (w i : 𝕜) • P i) v, v⟫_𝕜) =
      ∑ i, w i * RCLike.re (⟪P i v, v⟫_𝕜) := by
  rw [LinearMap.sum_apply, sum_inner, map_sum (RCLike.re : 𝕜 →+ ℝ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, inner_smul_left, RCLike.conj_ofReal, RCLike.re_ofReal_mul]

/-- A strictly positively weighted sum of positive operators annihilates a
vector exactly when every operator in the sum annihilates it.

With strictly positive weights this is the weighted form of the
blocked-sum kernel comparison in Rozmán--Molnár--Schuch, arXiv:2607.19078v1,
Lemma `block-obc`: expanding the real quadratic form of the weighted sum
gives a sum of nonnegative terms, so its vanishing forces each
`Re ⟪P i v, v⟫` to vanish, and positivity of `P i` then forces `P i v = 0`. -/
theorem apply_weighted_sum_eq_zero_iff {w : ι → ℝ} (hw : ∀ i, 0 < w i)
    {P : ι → E →ₗ[𝕜] E} (hP : ∀ i, (P i).IsPositive) (v : E) :
    (∑ i, (w i : 𝕜) • P i) v = 0 ↔ ∀ i, P i v = 0 := by
  constructor
  · intro hsum
    have hre : (∑ i, w i * RCLike.re (⟪P i v, v⟫_𝕜)) = 0 := by
      rw [← re_inner_weighted_sum_apply w P v, hsum]
      simp
    have hterms : (fun i => w i * RCLike.re (⟪P i v, v⟫_𝕜)) = 0 :=
      (Fintype.sum_eq_zero_iff_of_nonneg
        (fun i => mul_nonneg (le_of_lt (hw i)) ((hP i).re_inner_nonneg_left v))).mp hre
    intro i
    have hterm : w i * RCLike.re (⟪P i v, v⟫_𝕜) = 0 := by
      simpa using congrFun hterms i
    rcases mul_eq_zero.mp hterm with h | h
    · exact absurd h (ne_of_gt (hw i))
    · exact (hP i).apply_eq_zero_of_re_inner_eq_zero h
  · intro h
    rw [LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [LinearMap.smul_apply, h i]
    simp

/-- A finite sum of positive operators annihilates a vector exactly when
every summand annihilates it. -/
theorem apply_sum_eq_zero_iff {P : ι → E →ₗ[𝕜] E} (hP : ∀ i, (P i).IsPositive)
    (v : E) :
    (∑ i, P i) v = 0 ↔ ∀ i, P i v = 0 := by
  have h := apply_weighted_sum_eq_zero_iff (fun _ : ι => one_pos) hP v
  simpa using h

/-- The kernel of a strictly positively weighted sum of positive operators is
the intersection of the individual kernels. -/
theorem ker_weighted_sum_eq_iInf {w : ι → ℝ} (hw : ∀ i, 0 < w i)
    {P : ι → E →ₗ[𝕜] E} (hP : ∀ i, (P i).IsPositive) :
    LinearMap.ker (∑ i, (w i : 𝕜) • P i) = ⨅ i, LinearMap.ker (P i) := by
  ext v
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  exact apply_weighted_sum_eq_zero_iff hw hP v

/-- The kernel of a finite sum of positive operators is the intersection of
the individual kernels. -/
theorem ker_sum_eq_iInf {P : ι → E →ₗ[𝕜] E} (hP : ∀ i, (P i).IsPositive) :
    LinearMap.ker (∑ i, P i) = ⨅ i, LinearMap.ker (P i) := by
  ext v
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  exact apply_sum_eq_zero_iff hP v

/-- Strictly positive real weights do not change the kernel of a finite sum
of positive operators. -/
theorem ker_weighted_sum_eq_sum {w : ι → ℝ} (hw : ∀ i, 0 < w i)
    {P : ι → E →ₗ[𝕜] E} (hP : ∀ i, (P i).IsPositive) :
    LinearMap.ker (∑ i, (w i : 𝕜) • P i) = LinearMap.ker (∑ i, P i) :=
  (ker_weighted_sum_eq_iInf hw hP).trans (ker_sum_eq_iInf hP).symm

/-- A weighted sum of positive operators with nonnegative real weights is
positive. -/
theorem isPositive_weighted_sum {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    {P : ι → E →ₗ[𝕜] E} (hP : ∀ i, (P i).IsPositive) :
    (∑ i, (w i : 𝕜) • P i).IsPositive :=
  LinearMap.isPositive_sum Finset.univ fun i _ =>
    (hP i).smul_of_nonneg (RCLike.ofReal_nonneg.mpr (hw i))

/-- Real weights at most one place the weighted sum below the unweighted sum
in Loewner order.

This is the Loewner comparison of the blocked-sum argument in
Rozmán--Molnár--Schuch, arXiv:2607.19078v1, Lemma `block-obc`: the
difference is the weighted sum with weights `1 - w i`, each nonnegative. -/
theorem weighted_sum_le_sum {w : ι → ℝ} (hw : ∀ i, w i ≤ 1)
    {P : ι → E →ₗ[𝕜] E} (hP : ∀ i, (P i).IsPositive) :
    (∑ i, (w i : 𝕜) • P i) ≤ ∑ i, P i := by
  rw [LinearMap.le_def]
  have hsub : (∑ i, P i) - ∑ i, (w i : 𝕜) • P i
      = ∑ i, ((1 - w i : ℝ) : 𝕜) • P i := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RCLike.ofReal_sub, RCLike.ofReal_one, sub_smul, one_smul]
  rw [hsub]
  exact isPositive_weighted_sum (fun i => sub_nonneg.mpr (hw i)) hP

section GapTransfer

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

/-- A norm gap of a strictly positively weighted sum of positive operators,
with weights at most one, is inherited by the unweighted sum.

This is the gap step of the blocked-sum comparison in
Rozmán--Molnár--Schuch, arXiv:2607.19078v1, Lemma `block-obc`, obtained
from `LinearMap.IsPositive.norm_gap_of_le_of_ker_eq`: the weighted sum is
positive, dominated by the unweighted sum, and has the same kernel, so a
lower bound `γ * ‖v‖ ≤ ‖(∑ i, (w i : ℂ) • P i) v‖` on the orthogonal
complement of that common kernel holds equally for `∑ i, P i`. -/
theorem norm_gap_sum_of_weighted_sum {w : ι → ℝ} (hw : ∀ i, 0 < w i)
    (hwle : ∀ i, w i ≤ 1) {P : ι → F →ₗ[ℂ] F} (hP : ∀ i, (P i).IsPositive)
    {γ : ℝ} (hγ : 0 ≤ γ)
    (hGap : ∀ v ∈ (LinearMap.ker (∑ i, (w i : ℂ) • P i))ᗮ,
      γ * ‖v‖ ≤ ‖(∑ i, (w i : ℂ) • P i) v‖) :
    ∀ v ∈ (LinearMap.ker (∑ i, P i))ᗮ, γ * ‖v‖ ≤ ‖(∑ i, P i) v‖ :=
  (isPositive_weighted_sum (fun i => le_of_lt (hw i)) hP).norm_gap_of_le_of_ker_eq hγ
    (weighted_sum_le_sum hwle hP) (ker_weighted_sum_eq_sum hw hP) hGap

end GapTransfer

end WeightedPositiveKernel
