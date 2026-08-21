/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Fintype.BigOperators
import TNLean.MPS.MPDO.CPSVExamples410411Arithmetic

/-!
# Correlated-flip weight layer for CPSV16 Example 4.10

CPSV16 Example 4.10 places one maximally entangled qubit pair on each bond of a
four-spin ring and applies, independently at every spin, the corrected
correlated flip channel with flip probability one quarter.  A flip at spin $n$
acts by one flip on each of the two bonds adjacent to $n$, and a joint flip
configuration $s$ turns the pair on bond $n$ into the flipped Bell state
exactly when the flips at spins $n$ and $n+1$ disagree.  The four-site state is
therefore the mixture, over independent flip configurations, of orthonormal
products of Bell states labelled by the cyclic difference pattern of $s$.

This module records that derivation at the level of the label distributions.
It defines the flip configuration distribution, its pushforward to bond
difference patterns, the weight families attached to windows of one, two,
three, and four consecutive spins, and their natural-logarithm entropies.  The
mutual-information defect of these weight families equals one sixteenth of the
exact logarithm certified in the arithmetic module, hence is strictly positive.

The weight families list precisely the reduced-state spectra computed in the
paper-gap note at flip probability one quarter; the source prints only the
channel and the four entropy decimals.  Identifying
them with the spectra of the reductions of a corrected tensor, and proving the
zero-correlation-length and area-law clauses of the example, are the remaining
operator-level obligations.

**Scope restriction (classical weight layer):** the uniform boundary factors
record maximally mixed halves of the boundary bonds, and the identification of
these weight families with reduced-state spectra is not made in this module.
See `docs/paper-gaps/cpsv16_examples_4_10_4_11_entropy.tex`.

## Main results

* `bondWeight_eq_bondWeightValue`: closed form of the bond pattern distribution.
* `entropyOne_eq`, `entropyTwo_eq`, `entropyThree_eq`, `entropyFour_eq`: the
  exact natural-logarithm window entropies.
* `mutualInfoTwo_sub_mutualInfoOne_eq`: the exact mutual-information defect.
* `mutualInfoTwo_sub_mutualInfoOne_pos`: strict positivity of the defect.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, Example 4.10,
  lines 897--905.
* `docs/paper-gaps/cpsv16_examples_4_10_4_11_entropy.tex`, for the corrected
  channel and the exact four-spin calculation.
-/

namespace CPSVExample410CorrelatedFlip

open Real

/-- The probability of one on-site flip outcome of the corrected channel at
flip probability one quarter; `true` marks a flip.

Source channel: CPSV16, arXiv:1606.00608, Example 4.10, lines 897--905, with
the left-right correction recorded in
`docs/paper-gaps/cpsv16_examples_4_10_4_11_entropy.tex`. -/
noncomputable def flipWeight (b : Bool) : ℝ := if b then 1 / 4 else 3 / 4

/-- The probability of a joint flip configuration on the four spins; the four
channels act independently.

Source channel: CPSV16, arXiv:1606.00608, Example 4.10, lines 897--905. -/
noncomputable def flipProb (s : Bool × Bool × Bool × Bool) : ℝ :=
  flipWeight s.1 * flipWeight s.2.1 * flipWeight s.2.2.1 * flipWeight s.2.2.2

/-- The bond difference pattern of a flip configuration: bond $n$ carries the
flipped Bell state exactly when the flips at spins $n$ and $n+1$ disagree,
with spin five identified with spin one.

Derived from the Bell-pair ring of CPSV16, arXiv:1606.00608, Example 4.10,
line 900. -/
def bondPattern (s : Bool × Bool × Bool × Bool) : Bool × Bool × Bool × Bool :=
  (xor s.1 s.2.1, xor s.2.1 s.2.2.1, xor s.2.2.1 s.2.2.2, xor s.2.2.2 s.1)

/-- The pushforward of the flip configuration distribution to bond difference
patterns.

Derived from CPSV16, arXiv:1606.00608, Example 4.10, lines 897--905. -/
noncomputable def bondWeight (t : Bool × Bool × Bool × Bool) : ℝ :=
  ∑ s : Bool × Bool × Bool × Bool, if bondPattern s = t then flipProb s else 0

/-- The closed form of the bond pattern distribution: weight $41/128$ on the
unflipped pattern, $15/128$ on each of the four adjacent flipped pairs,
$9/128$ on the two opposite flipped pairs and on the fully flipped pattern,
and zero on the eight odd patterns.

Derived from CPSV16, arXiv:1606.00608, Example 4.10, lines 897--905. -/
noncomputable def bondWeightValue : Bool × Bool × Bool × Bool → ℝ
  | (false, false, false, false) => 41 / 128
  | (true, true, false, false) => 15 / 128
  | (false, true, true, false) => 15 / 128
  | (false, false, true, true) => 15 / 128
  | (true, false, false, true) => 15 / 128
  | (true, false, true, false) => 9 / 128
  | (false, true, false, true) => 9 / 128
  | (true, true, true, true) => 9 / 128
  | (true, false, false, false) => 0
  | (false, true, false, false) => 0
  | (false, false, true, false) => 0
  | (false, false, false, true) => 0
  | (true, true, true, false) => 0
  | (true, true, false, true) => 0
  | (true, false, true, true) => 0
  | (false, true, true, true) => 0

/-- The flip configuration distribution is normalized.

Derived from CPSV16, arXiv:1606.00608, Example 4.10, lines 897--905. -/
theorem sum_flipProb : ∑ s : Bool × Bool × Bool × Bool, flipProb s = 1 := by
  norm_num [flipProb, flipWeight, Fintype.sum_prod_type, Fintype.sum_bool]

/-- The bond pattern distribution takes exactly the closed-form values.

Derived from CPSV16, arXiv:1606.00608, Example 4.10, lines 897--905. -/
theorem bondWeight_eq_bondWeightValue : bondWeight = bondWeightValue := by
  funext t
  rcases t with ⟨_ | _, _ | _, _ | _, _ | _⟩ <;>
    norm_num [bondWeight, bondWeightValue, bondPattern, flipProb, flipWeight,
      Fintype.sum_prod_type, Fintype.sum_bool]

/-- The bond pattern distribution is normalized.

Derived from CPSV16, arXiv:1606.00608, Example 4.10, lines 897--905. -/
theorem sum_bondWeight : ∑ t : Bool × Bool × Bool × Bool, bondWeight t = 1 := by
  rw [bondWeight_eq_bondWeightValue]
  norm_num [bondWeightValue, Fintype.sum_prod_type, Fintype.sum_bool]

/-- The distribution of a single bond label under the flip configuration
distribution.

Derived from CPSV16, arXiv:1606.00608, Example 4.10, lines 897--905. -/
noncomputable def oneBondWeight (u : Bool) : ℝ :=
  ∑ s : Bool × Bool × Bool × Bool, if xor s.1 s.2.1 = u then flipProb s else 0

/-- The joint distribution of two consecutive bond labels under the flip
configuration distribution.

Derived from CPSV16, arXiv:1606.00608, Example 4.10, lines 897--905. -/
noncomputable def twoBondWeight (u v : Bool) : ℝ :=
  ∑ s : Bool × Bool × Bool × Bool,
    if xor s.1 s.2.1 = u ∧ xor s.2.1 s.2.2.1 = v then flipProb s else 0

/-- A single bond keeps its Bell state with probability $5/8$.

Derived from CPSV16, arXiv:1606.00608, Example 4.10, lines 897--905. -/
theorem oneBondWeight_false : oneBondWeight false = 5 / 8 := by
  norm_num [oneBondWeight, flipProb, flipWeight, Fintype.sum_prod_type, Fintype.sum_bool]

/-- A single bond is flipped with probability $3/8$.

Derived from CPSV16, arXiv:1606.00608, Example 4.10, lines 897--905. -/
theorem oneBondWeight_true : oneBondWeight true = 3 / 8 := by
  norm_num [oneBondWeight, flipProb, flipWeight, Fintype.sum_prod_type, Fintype.sum_bool]

/-- Two consecutive bonds both keep their Bell states with probability
$7/16$.

Derived from CPSV16, arXiv:1606.00608, Example 4.10, lines 897--905. -/
theorem twoBondWeight_false_false : twoBondWeight false false = 7 / 16 := by
  norm_num [twoBondWeight, flipProb, flipWeight, Fintype.sum_prod_type, Fintype.sum_bool]

/-- Each of the three remaining label pairs of two consecutive bonds has
probability $3/16$.

Derived from CPSV16, arXiv:1606.00608, Example 4.10, lines 897--905. -/
theorem twoBondWeight_of_pair_ne_false_false (u v : Bool) (h : (u, v) ≠ (false, false)) :
    twoBondWeight u v = 3 / 16 := by
  rcases u <;> rcases v <;>
    first
      | exact absurd rfl h
      | norm_num [twoBondWeight, flipProb, flipWeight, Fintype.sum_prod_type, Fintype.sum_bool]

/-- The one-bond distribution is the marginal of the bond pattern
distribution.

Derived from CPSV16, arXiv:1606.00608, Example 4.10, lines 897--905. -/
theorem oneBondWeight_eq_marginal (u : Bool) :
    oneBondWeight u = ∑ v : Bool, ∑ w : Bool, ∑ x : Bool, bondWeight (u, v, w, x) := by
  rw [bondWeight_eq_bondWeightValue]
  rcases u <;>
    norm_num [oneBondWeight_false, oneBondWeight_true, bondWeightValue, Fintype.sum_bool]

/-- The two-bond distribution is the marginal of the bond pattern
distribution.

Derived from CPSV16, arXiv:1606.00608, Example 4.10, lines 897--905. -/
theorem twoBondWeight_eq_marginal (u v : Bool) :
    twoBondWeight u v = ∑ w : Bool, ∑ x : Bool, bondWeight (u, v, w, x) := by
  rw [bondWeight_eq_bondWeightValue]
  rcases u <;> rcases v <;>
    norm_num [twoBondWeight_false_false, twoBondWeight_of_pair_ne_false_false, bondWeightValue,
      Fintype.sum_bool]

/-- The weight family of a one-spin window: the two boundary bond halves are
maximally mixed, giving the uniform distribution on four labels.

Spectrum of the one-spin reduction computed in
`docs/paper-gaps/cpsv16_examples_4_10_4_11_entropy.tex`; the source states only
the channel and the entropy values (CPSV16, arXiv:1606.00608, Example 4.10,
lines 900--904). -/
noncomputable def windowWeightOne : Bool × Bool → ℝ := fun _ ↦ 1 / 4

/-- The weight family of a two-spin window: one interior bond label together
with two maximally mixed boundary bond halves.

Spectrum of the two-spin reduction computed in
`docs/paper-gaps/cpsv16_examples_4_10_4_11_entropy.tex`; the source states only
the channel and the entropy values (CPSV16, arXiv:1606.00608, Example 4.10,
lines 900--904). -/
noncomputable def windowWeightTwo (x : Bool × Bool × Bool) : ℝ :=
  oneBondWeight x.2.1 / 4

/-- The weight family of a three-spin window: two consecutive interior bond
labels together with two maximally mixed boundary bond halves.

Spectrum of the three-spin reduction computed in
`docs/paper-gaps/cpsv16_examples_4_10_4_11_entropy.tex`; the source states only
the channel and the entropy values (CPSV16, arXiv:1606.00608, Example 4.10,
lines 900--904). -/
noncomputable def windowWeightThree (x : Bool × Bool × Bool × Bool) : ℝ :=
  twoBondWeight x.2.1 x.2.2.1 / 4

/-- The one-spin window weights are normalized.

Derived from CPSV16, arXiv:1606.00608, Example 4.10, lines 897--905. -/
theorem sum_windowWeightOne : ∑ x : Bool × Bool, windowWeightOne x = 1 := by
  norm_num [windowWeightOne, Fintype.sum_prod_type, Fintype.sum_bool]

/-- The two-spin window weights are normalized.

Derived from CPSV16, arXiv:1606.00608, Example 4.10, lines 897--905. -/
theorem sum_windowWeightTwo : ∑ x : Bool × Bool × Bool, windowWeightTwo x = 1 := by
  norm_num [windowWeightTwo, oneBondWeight_false, oneBondWeight_true,
    Fintype.sum_prod_type, Fintype.sum_bool]

/-- The three-spin window weights are normalized.

Derived from CPSV16, arXiv:1606.00608, Example 4.10, lines 897--905. -/
theorem sum_windowWeightThree :
    ∑ x : Bool × Bool × Bool × Bool, windowWeightThree x = 1 := by
  norm_num [windowWeightThree, twoBondWeight_false_false, twoBondWeight_of_pair_ne_false_false,
    Fintype.sum_prod_type, Fintype.sum_bool]

/-- The natural-logarithm entropy of the one-spin window weights.

Displayed value: CPSV16, arXiv:1606.00608, Example 4.10, line 904. -/
noncomputable def entropyOne : ℝ := ∑ x : Bool × Bool, negMulLog (windowWeightOne x)

/-- The natural-logarithm entropy of the two-spin window weights.

Displayed value: CPSV16, arXiv:1606.00608, Example 4.10, line 904. -/
noncomputable def entropyTwo : ℝ :=
  ∑ x : Bool × Bool × Bool, negMulLog (windowWeightTwo x)

/-- The natural-logarithm entropy of the three-spin window weights.

Displayed value: CPSV16, arXiv:1606.00608, Example 4.10, line 904. -/
noncomputable def entropyThree : ℝ :=
  ∑ x : Bool × Bool × Bool × Bool, negMulLog (windowWeightThree x)

/-- The natural-logarithm entropy of the bond pattern distribution, the
four-spin window weights.

Displayed value: CPSV16, arXiv:1606.00608, Example 4.10, line 904. -/
noncomputable def entropyFour : ℝ :=
  ∑ t : Bool × Bool × Bool × Bool, negMulLog (bondWeight t)

private lemma negMulLog_quarter : negMulLog (1 / 4 : ℝ) = 1 / 4 * (2 * log 2) := by
  rw [negMulLog, show (1 / 4 : ℝ) = 4⁻¹ by norm_num, log_inv,
    show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
  push_cast
  ring

private lemma negMulLog_five_thirtytwoths :
    negMulLog (5 / 32 : ℝ) = 5 / 32 * (5 * log 2 - log 5) := by
  rw [negMulLog, log_div (by norm_num) (by norm_num),
    show (32 : ℝ) = 2 ^ 5 by norm_num, log_pow]
  push_cast
  ring

private lemma negMulLog_three_thirtytwoths :
    negMulLog (3 / 32 : ℝ) = 3 / 32 * (5 * log 2 - log 3) := by
  rw [negMulLog, log_div (by norm_num) (by norm_num),
    show (32 : ℝ) = 2 ^ 5 by norm_num, log_pow]
  push_cast
  ring

private lemma negMulLog_seven_sixtyfourths :
    negMulLog (7 / 64 : ℝ) = 7 / 64 * (6 * log 2 - log 7) := by
  rw [negMulLog, log_div (by norm_num) (by norm_num),
    show (64 : ℝ) = 2 ^ 6 by norm_num, log_pow]
  push_cast
  ring

private lemma negMulLog_three_sixtyfourths :
    negMulLog (3 / 64 : ℝ) = 3 / 64 * (6 * log 2 - log 3) := by
  rw [negMulLog, log_div (by norm_num) (by norm_num),
    show (64 : ℝ) = 2 ^ 6 by norm_num, log_pow]
  push_cast
  ring

private lemma negMulLog_fortyone_128ths :
    negMulLog (41 / 128 : ℝ) = 41 / 128 * (7 * log 2 - log 41) := by
  rw [negMulLog, log_div (by norm_num) (by norm_num),
    show (128 : ℝ) = 2 ^ 7 by norm_num, log_pow]
  push_cast
  ring

private lemma negMulLog_fifteen_128ths :
    negMulLog (15 / 128 : ℝ) = 15 / 128 * (7 * log 2 - log 3 - log 5) := by
  rw [negMulLog, log_div (by norm_num) (by norm_num),
    show (128 : ℝ) = 2 ^ 7 by norm_num, log_pow,
    show (15 : ℝ) = 3 * 5 by norm_num, log_mul (by norm_num) (by norm_num)]
  push_cast
  ring

private lemma negMulLog_nine_128ths :
    negMulLog (9 / 128 : ℝ) = 9 / 128 * (7 * log 2 - 2 * log 3) := by
  rw [negMulLog, log_div (by norm_num) (by norm_num),
    show (128 : ℝ) = 2 ^ 7 by norm_num, log_pow,
    show (9 : ℝ) = 3 ^ 2 by norm_num, log_pow]
  push_cast
  ring

/-- The one-spin entropy is $2\ln 2$, that is, two bits.

Displayed value: CPSV16, arXiv:1606.00608, Example 4.10, line 904. -/
theorem entropyOne_eq : entropyOne = 2 * log 2 := by
  rw [entropyOne]
  norm_num [windowWeightOne, Fintype.sum_prod_type, Fintype.sum_bool, negMulLog_quarter]
  ring

/-- The exact two-spin entropy in natural logarithms; divided by $\ln 2$ it is
the displayed decimal $2.9544$.

Displayed value: CPSV16, arXiv:1606.00608, Example 4.10, line 904. -/
theorem entropyTwo_eq :
    entropyTwo = 5 * log 2 - 5 / 8 * log 5 - 3 / 8 * log 3 := by
  rw [entropyTwo]
  norm_num [windowWeightTwo, oneBondWeight_false, oneBondWeight_true,
    Fintype.sum_prod_type, Fintype.sum_bool, negMulLog_five_thirtytwoths,
    negMulLog_three_thirtytwoths]
  ring

/-- The exact three-spin entropy in natural logarithms; divided by $\ln 2$ it
is the displayed decimal $3.8802$.

Displayed value: CPSV16, arXiv:1606.00608, Example 4.10, line 904. -/
theorem entropyThree_eq :
    entropyThree = 6 * log 2 - 7 / 16 * log 7 - 9 / 16 * log 3 := by
  rw [entropyThree]
  norm_num [windowWeightThree, twoBondWeight_false_false, twoBondWeight_of_pair_ne_false_false,
    Fintype.sum_prod_type, Fintype.sum_bool, negMulLog_seven_sixtyfourths,
    negMulLog_three_sixtyfourths]
  ring

/-- The exact four-spin entropy in natural logarithms; divided by $\ln 2$ it is
the displayed decimal $2.7839$.

Displayed value: CPSV16, arXiv:1606.00608, Example 4.10, line 904. -/
theorem entropyFour_eq :
    entropyFour =
      7 * log 2 - 41 / 128 * log 41 - 57 / 64 * log 3 - 15 / 32 * log 5 := by
  rw [entropyFour, bondWeight_eq_bondWeightValue]
  norm_num [bondWeightValue, Fintype.sum_prod_type, Fintype.sum_bool,
    negMulLog_fortyone_128ths, negMulLog_fifteen_128ths, negMulLog_nine_128ths]
  ring

/-- The mutual information of one spin against its complement in the four-spin
window weights.

Displayed value: CPSV16, arXiv:1606.00608, Example 4.10, lines 900--905. -/
noncomputable def mutualInfoOne : ℝ := entropyOne + entropyThree - entropyFour

/-- The mutual information of two consecutive spins against their complement
in the four-spin window weights.

Displayed value: CPSV16, arXiv:1606.00608, Example 4.10, lines 900--905. -/
noncomputable def mutualInfoTwo : ℝ := 2 * entropyTwo - entropyFour

/-- The exact mutual-information defect of the window weight families: one
sixteenth of the logarithm of the certified integer ratio.

Derived from CPSV16, arXiv:1606.00608, Example 4.10, lines 897--905; the exact
form is recorded in `docs/paper-gaps/cpsv16_examples_4_10_4_11_entropy.tex`. -/
theorem mutualInfoTwo_sub_mutualInfoOne_eq :
    mutualInfoTwo - mutualInfoOne =
      1 / 16 * Real.log (((2 : ℝ) ^ 32 * 7 ^ 7) / (3 ^ 3 * 5 ^ 20)) := by
  rw [mutualInfoTwo, mutualInfoOne, entropyOne_eq, entropyTwo_eq, entropyThree_eq,
    log_div (by norm_num) (by norm_num), log_mul (by norm_num) (by norm_num),
    log_mul (by norm_num) (by norm_num), log_pow, log_pow, log_pow, log_pow]
  push_cast
  ring

/-- The window weight families strictly violate saturation: the two-spin
mutual information exceeds the one-spin mutual information.

Derived from CPSV16, arXiv:1606.00608, Example 4.10, lines 897--905, through
the certified integer comparison. -/
theorem mutualInfoTwo_sub_mutualInfoOne_pos : 0 < mutualInfoTwo - mutualInfoOne := by
  rw [mutualInfoTwo_sub_mutualInfoOne_eq]
  exact mul_pos (by norm_num) CPSVExamples410411Arithmetic.example410_log_ratio_pos

end CPSVExample410CorrelatedFlip
