/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum

/-!
# Exact arithmetic for CPSV16 Examples 4.10 and 4.11

The printed four-site calculation in CPSV16 Example 4.10 and the independently
derived four-site specialization of the family in Example 4.11 lead to the
strict integer comparisons
\[
  2^{32}7^7>3^3 5^{20}
\]
and
\[
  41^{82}5^{50}>2^{48}13^{52}7^{112}.
\]
This module certifies these comparisons and the positivity of the logarithms of
their ratios.

Normalization directly certifies all four closed arithmetic goals. For each
logarithmic statement, `Real.log_pos` first reduces positivity of the logarithm
to the assertion that its ratio is greater than one; normalization then closes
that rational inequality.

These scalar results do not identify reduced-state spectra and do not assert
saturation or failure of an area law. Such conclusions require separate formal
links from the printed tensors to the corresponding entropy expressions.

**Scope restriction (scalar arithmetic only):**
`docs/paper-gaps/cpsv16_exact_arithmetic_scope.tex` records this boundary and
distinguishes the printed Example 4.10 calculation from the independently
derived four-site specialization of Example 4.11.

## Main results

* `example410_integer_inequality`: the exact integer comparison associated with
  the four-site calculation for Example 4.10.
* `example411_integer_inequality`: the exact integer comparison associated with
  the derived four-site specialization of Example 4.11.
* `example410_log_ratio_pos`: positivity of the first logarithmic ratio.
* `example411_log_ratio_pos`: positivity of the second logarithmic ratio.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, Example 4.10,
  lines 897--905, and the arbitrary-length family of Example 4.11, lines 907--924.
* `docs/paper-gaps/cpsv16_examples_4_10_4_11_entropy.tex`, for the independent
  four-site specialization and entropy calculation for Example 4.11.
-/

namespace CPSVExamples410411Arithmetic

/-- The strict integer comparison arising in the exact four-site calculation
for CPSV16 Example 4.10.

Source: CPSV16, arXiv:1606.00608, Example 4.10, lines 897--905. -/
theorem example410_integer_inequality :
    (2 : ℕ) ^ 32 * 7 ^ 7 > 3 ^ 3 * 5 ^ 20 := by
  norm_num

/-- The strict integer comparison arising from the four-site specialization of
the arbitrary-length family and literal weights printed in CPSV16 Example 4.11.

Source: the independent derivation recorded in
`docs/paper-gaps/cpsv16_examples_4_10_4_11_entropy.tex`. The source paper,
arXiv:1606.00608, Example 4.11, lines 907--924, prints only the arbitrary-length
family, its weights, and its SAL claim. -/
theorem example411_integer_inequality :
    (41 : ℕ) ^ 82 * 5 ^ 50 > 2 ^ 48 * 13 ^ 52 * 7 ^ 112 := by
  norm_num

/-- The logarithm of the exact ratio associated with CPSV16 Example 4.10 is
strictly positive.

This is only a scalar arithmetic statement; it does not identify the ratio with
an entropy difference.

Source: CPSV16, arXiv:1606.00608, Example 4.10, lines 897--905. -/
theorem example410_log_ratio_pos :
    0 < Real.log (((2 : ℝ) ^ 32 * 7 ^ 7) / (3 ^ 3 * 5 ^ 20)) := by
  apply Real.log_pos
  norm_num

/-- The logarithm of the exact ratio associated with the four-site specialization
of the literal weights in CPSV16 Example 4.11 is strictly positive.

This is only a scalar arithmetic statement; it does not identify the ratio with
an entropy difference.

Source: the independent derivation recorded in
`docs/paper-gaps/cpsv16_examples_4_10_4_11_entropy.tex`. The source paper,
arXiv:1606.00608, Example 4.11, lines 907--924, prints only the arbitrary-length
family, its weights, and its SAL claim. -/
theorem example411_log_ratio_pos :
    0 < Real.log
      (((41 : ℝ) ^ 82 * 5 ^ 50) / (2 ^ 48 * 13 ^ 52 * 7 ^ 112)) := by
  apply Real.log_pos
  norm_num

end CPSVExamples410411Arithmetic
