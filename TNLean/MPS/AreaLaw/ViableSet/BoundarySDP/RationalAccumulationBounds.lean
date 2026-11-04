/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.CommonDenominator
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalCodeHeights
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalGramContractionCost

/-!
# Common-denominator bounds for rational accumulation

Every prefix of the counted finite-sum evaluator preserves a common denominator
of its summands. Its norm grows at most linearly with the number of accumulated
terms. These estimates bound the reduced rational coordinates actually returned
at every prefix, independently of the arithmetic counts of the individual terms.

## References

- LVV, arXiv:1307.5143, Claim 2.7: matrix elements for boundary minimization.
-/

namespace TNLean.MPS.AreaLaw.RationalGramContractionCost

open RationalContractionCost

/-- The value returned by the actual finite-sum evaluator is the sum of the
values returned by its terms, without requiring equal arithmetic counts. -/
theorem run_sumFin_value {n : ℕ} (f : Fin n → Arithmetic (ℚ × ℚ)) :
    (sumFin n f).run.1 = ∑ i, (f i).run.1 := by
  induction n with
  | zero => simp [sumFin]; rfl
  | succ n ih =>
    simp only [sumFin, run_bind, run_complexAdd, ih, Fin.sum_univ_castSucc]
    rfl

/-- A common positive denominator is preserved by the actual finite-sum
evaluator. A uniform norm bound `B` on the returned summands gives norm bound
`n B` on their accumulated value. -/
theorem sumFin_bounds {n L B : ℕ} (f : Fin n → Arithmetic (ℚ × ℚ)) (hL : 0 < L)
    (hden : ∀ i, HasGaussianIntegerDenominator L (decodeRationalComplex (f i).run.1))
    (hnorm : ∀ i, ‖decodeRationalComplex (f i).run.1‖ ≤ (B : ℝ)) :
    HasGaussianIntegerDenominator L (decodeRationalComplex (sumFin n f).run.1) ∧
      ‖decodeRationalComplex (sumFin n f).run.1‖ ≤ (n * B : ℕ) := by
  rw [run_sumFin_value, decodeRationalComplex_fintype_sum]
  refine ⟨HasGaussianIntegerDenominator.finset_sum hL (fun i _hi ↦ hden i), ?_⟩
  calc
    _ ≤ ∑ i, ‖decodeRationalComplex (f i).run.1‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, (B : ℝ) := Finset.sum_le_sum fun i _hi ↦ hnorm i
    _ = (n * B : ℕ) := by simp [Nat.cast_mul]

/-- Every actual prefix accumulator preserves the summands' common denominator
`L`, has norm at most `a B` after `a` terms, and stores rational coordinates of
height at most `L max(1,a B)`. The zero-length prefix is included. -/
theorem sumFin_prefix_bounds {n a L B : ℕ} (f : Fin n → Arithmetic (ℚ × ℚ))
    (ha : a ≤ n) (hL : 0 < L)
    (hden : ∀ i, HasGaussianIntegerDenominator L (decodeRationalComplex (f i).run.1))
    (hnorm : ∀ i, ‖decodeRationalComplex (f i).run.1‖ ≤ (B : ℝ)) :
    let out := (sumFin a (fun i ↦ f (Fin.castLE ha i))).run.1
    HasGaussianIntegerDenominator L (decodeRationalComplex out) ∧
      ‖decodeRationalComplex out‖ ≤ (a * B : ℕ) ∧
      rationalHeight out.1 ≤ L * max 1 (a * B) ∧
      rationalHeight out.2 ≤ L * max 1 (a * B) := by
  have h := sumFin_bounds (fun i : Fin a ↦ f (Fin.castLE ha i)) hL
    (fun i ↦ hden _) (fun i ↦ hnorm _)
  exact ⟨h.1, h.2, (RationalComplexCode.decode_height_iff _).mp (h.1.height_of_norm_le h.2)⟩

end TNLean.MPS.AreaLaw.RationalGramContractionCost
