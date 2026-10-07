/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DistributedLifetime
import Mathlib.Basic.NNReal.Basic

/-!
# Weighted choice cost at corrected source positions

Only gates meeting the endpoints of corrected source positions are expanded.
Their ket/bra coefficient sums contribute at most `B ^ (4 * b * S.card)`;
physical ket/bra entries at those parties contribute at most `d ^ (4 * S.card)`.
The combined bound is `(B ^ (4 * b) * d ^ 4) ^ S.card`.

The products contain no exterior gate coefficient sums. The argument uses whole-
lifetime participation and bounds on intended physical dimensions, without
bounding private memories or source Schmidt ranks. It is the choice-counting
step of the density-compression proof; no random-source estimate is asserted.

## Main definitions and statements

- `ketBraCoefficientCost`: the squared sum of absolute monomial coefficients.
- `correctedPositionChoiceCost`: weighted cost of labels and physical entries
  only at affected gates and parties.
- `correctedPositionChoiceCost_le`: the exact `Q ^ S.card` bound, where
  `Q = B ^ (4 * b) * d ^ 4`.

## References

- OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*
  (September 24, 2026), Theorem 5.2 (`thm:compression`),
  `eq:compression-choice-cost`, `04-compression.tex:356–381`.
  [Pinned source](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L356).

These proofs are newly written from the paper's mathematical argument. No OpenAI
Lean code is copied or adapted.
-/

/-!
Original proof provenance.
Source: September 24, 2026.
Paper file: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex
Labels: thm:compression, eq:compression-polynomial-bounds, eq:compression-choice-cost;
independently formalized; no upstream Lean proof text reused.
Mathematical source commit: adc7f1241b42e322a6451854ab7e4b4c146bf78a.

Provenance-ID: 8769-lifetime-ket-bra-coefficient-cost
Downstream declaration: TNLean.PEPS.Approximation.ketBraCoefficientCost
Provenance-ID: 8769-lifetime-ket-bra-coefficient-cost-eq-sum
Downstream declaration: TNLean.PEPS.Approximation.ketBraCoefficientCost_eq_sum
Provenance-ID: 8769-lifetime-corrected-position-choice-cost
Downstream declaration: TNLean.PEPS.Approximation.correctedPositionChoiceCost
Provenance-ID: 8769-lifetime-corrected-position-choice-cost-le
Downstream declaration: TNLean.PEPS.Approximation.correctedPositionChoiceCost_le
Provenance-ID: 8769-lifetime-compression-choice-base-le-of-monomial-bounds
Downstream declaration: TNLean.PEPS.Approximation.compressionChoiceBase_le_of_monomial_bounds
-/

namespace TNLean.PEPS.Approximation

open scoped BigOperators NNReal

variable {Party Gate Position Label : Type*} [DecidableEq Party] [DecidableEq Gate]

/-- The total absolute weight of ket and bra monomial label choices at one gate.
The arguments `coeff` are absolute coefficients, hence nonnegative.
Theorem 5.2, `eq:compression-choice-cost`, `04-compression.tex:365–373`. -/
def ketBraCoefficientCost (labels : Finset Label) (coeff : Label → ℝ≥0) : ℝ≥0 :=
  (∑ ξ ∈ labels, coeff ξ) ^ 2

/-- The squared coefficient sum is exactly the sum of products over independently
chosen ket and bra labels. Theorem 5.2, `04-compression.tex:365–373`. -/
theorem ketBraCoefficientCost_eq_sum (labels : Finset Label) (coeff : Label → ℝ≥0) :
    ketBraCoefficientCost labels coeff = ∑ ξ ∈ labels, ∑ ζ ∈ labels, coeff ξ * coeff ζ := by
  rw [ketBraCoefficientCost, pow_two, Finset.sum_mul_sum]

/-- The weighted number of coefficient and physical-entry choices at corrected
endpoints. Only gates touching corrected parties enter the gate product; each
physical party contributes its ket and bra dimensions. Theorem 5.2,
`eq:compression-choice-cost`, `04-compression.tex:356–381`. -/
def correctedPositionChoiceCost (gates : Finset Gate) (participants : Gate → Finset Party)
    (endpoints : Position → Party × Party) (S : Finset Position)
    {Labels : Gate → Type*} (labels : ∀ g, Finset (Labels g))
    (coeff : ∀ g, Labels g → ℝ≥0) (physicalDim : Party → ℕ) : ℝ≥0 :=
  (∏ g ∈ gatesTouching gates participants (correctedParties endpoints S),
    ketBraCoefficientCost (labels g) (coeff g)) *
    ∏ p ∈ correctedParties endpoints S, (physicalDim p : ℝ≥0) ^ 2

/-- At most `2 * b * S.card` expanded gates and `2 * S.card` affected parties
give the paper's exact weighted choice bound. Exterior aggregate gates are
absent from both the cost and its hypotheses. Theorem 5.2,
`eq:compression-choice-cost`, `04-compression.tex:356–381`. -/
theorem correctedPositionChoiceCost_le (gates : Finset Gate)
    (participants : Gate → Finset Party) (endpoints : Position → Party × Party)
    (S : Finset Position) {Labels : Gate → Type*} (labels : ∀ g, Finset (Labels g))
    (coeff : ∀ g, Labels g → ℝ≥0) (physicalDim : Party → ℕ) (b : ℕ) (B d : ℝ≥0)
    (hB : 1 ≤ B) (hd : 1 ≤ d)
    (hlifetime : ∀ p ∈ correctedParties endpoints S,
      (incidentGates gates participants p).card ≤ b)
    (hcoeff : ∀ g ∈ gatesTouching gates participants (correctedParties endpoints S),
      ∑ ξ ∈ labels g, coeff g ξ ≤ B)
    (hphysical : ∀ p ∈ correctedParties endpoints S, (physicalDim p : ℝ≥0) ≤ d) :
    correctedPositionChoiceCost gates participants endpoints S labels coeff physicalDim ≤
      (B ^ (4 * b) * d ^ 4) ^ S.card := by
  let A := correctedParties endpoints S
  let G := gatesTouching gates participants A
  have hgateExponent : 2 * G.card ≤ 4 * b * S.card := by
    simpa only [← Nat.mul_assoc] using Nat.mul_le_mul_left 2
      (card_gatesTouching_correctedParties_le gates participants endpoints S b hlifetime)
  have hpartyExponent : 2 * A.card ≤ 4 * S.card := by
    simpa only [← Nat.mul_assoc] using Nat.mul_le_mul_left 2
      (card_correctedParties_le endpoints S)
  have hgateCost : (∏ g ∈ G, ketBraCoefficientCost (labels g) (coeff g)) ≤
      B ^ (4 * b * S.card) := by
    calc
      _ ≤ (B ^ 2) ^ G.card := Finset.prod_le_pow_card G _ _
        (fun g hg ↦ pow_le_pow_left' (hcoeff g hg) 2)
      _ = B ^ (2 * G.card) := (pow_mul B 2 G.card).symm
      _ ≤ B ^ (4 * b * S.card) := pow_le_pow_right' hB hgateExponent
  have hpartyCost : (∏ p ∈ A, (physicalDim p : ℝ≥0) ^ 2) ≤ d ^ (4 * S.card) := by
    calc
      _ ≤ (d ^ 2) ^ A.card := Finset.prod_le_pow_card A _ _
        (fun p hp ↦ pow_le_pow_left' (hphysical p hp) 2)
      _ = d ^ (2 * A.card) := (pow_mul d 2 A.card).symm
      _ ≤ d ^ (4 * S.card) := pow_le_pow_right' hd hpartyExponent
  calc
    correctedPositionChoiceCost gates participants endpoints S labels coeff physicalDim ≤
        B ^ (4 * b * S.card) * d ^ (4 * S.card) := mul_le_mul' hgateCost hpartyCost
    _ = (B ^ (4 * b) * d ^ 4) ^ S.card := by
      rw [pow_mul B (4 * b) S.card, pow_mul d 4 S.card, mul_pow]

/-- Uniform monomial bounds on coefficient sums and intended physical dimensions
give an explicit monomial bound for `Q = B ^ (4 * b) * d ^ 4`. The lifetime
constant `b` is independent of the size parameter `L`. Theorem 5.2,
`eq:compression-choice-cost`, `04-compression.tex:365–381`. -/
theorem compressionChoiceBase_le_of_monomial_bounds (L B d C D : ℝ≥0) (a c b : ℕ)
    (hB : B ≤ C * L ^ a) (hd : d ≤ D * L ^ c) :
    B ^ (4 * b) * d ^ 4 ≤ (C ^ (4 * b) * D ^ 4) * L ^ (4 * b * a + 4 * c) := by
  calc
    _ ≤ (C * L ^ a) ^ (4 * b) * (D * L ^ c) ^ 4 :=
      mul_le_mul' (pow_le_pow_left' hB _) (pow_le_pow_left' hd _)
    _ = (C ^ (4 * b) * D ^ 4) * L ^ (4 * b * a + 4 * c) := by
      rw [mul_pow C (L ^ a) (4 * b), mul_pow D (L ^ c) 4,
        ← pow_mul L a (4 * b), ← pow_mul L c 4, pow_add,
        Nat.mul_comm a (4 * b), Nat.mul_comm c 4]
      exact mul_mul_mul_comm _ _ _ _

end TNLean.PEPS.Approximation
