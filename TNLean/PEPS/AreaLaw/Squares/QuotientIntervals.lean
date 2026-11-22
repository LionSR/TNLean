/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith

/-!
# Cardinality of integer quotient intervals

For integers a ≤ b and a positive integer u, the number of integers from
⌊a/u⌋ through ⌊b/u⌋, multiplied by u, is at most b - a + 2u. The estimate
holds for negative endpoints as well as positive ones. It bounds the number
of rows and columns met by dyadic cells in the geometric covering argument.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*, September 24,
2026, Lemma 9.4, the boundary-line count in `08-scanner.tex`, lines 622–649,
and its rectangle application in the proof of Proposition 9.5, lines 717–729,
at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Original formalization from the manuscript; no upstream Lean proof text reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- For a positive divisor, the inclusive quotient interval has total length
at most the endpoint displacement plus two divisor lengths.
Auxiliary arithmetic estimate for the proofs of Lemma 9.4 and Proposition 9.5,
the boundary-line count in
`08-scanner.tex`, lines 622–649 and 717–729. -/
theorem quotient_interval_card (a b u : ℤ) (hu : 0 < u) (hab : a ≤ b) :
    u * ((Finset.Icc (a / u) (b / u)).card : ℤ) ≤ b - a + 2 * u := by
  have hdiv := Int.ediv_le_ediv hu hab
  rw [Int.card_Icc, Int.toNat_of_nonneg (by omega)]
  have ha := Int.lt_ediv_add_one_mul_self a hu
  have hb := Int.ediv_mul_le b (ne_of_gt hu)
  nlinarith

end TNLean.PEPS.AreaLaw.Geometry
