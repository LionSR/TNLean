/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Wielandt.Primitivity.Definitions
import QICLean.Kraus.Wielandt.Stochastic

/-!
# Classical stochastic matrices have equal quantum Wielandt indices

For the actual matrix-unit Kraus embedding of a nonnegative real matrix,
the admissible positive lengths for full word span, full vector spreading,
and entrywise positive classical powers coincide. Taking their infima gives
`qIndex = positivePowerIndex = iIndex`.

For a primitive column-stochastic matrix this is Proposition 2 of Sanz,
Pérez-García, Wolf and Cirac, arXiv:0909.5347, source `main.tex`, lines 478–494.
The generic channel formulas and fixed-length criteria are in QICLean;
this file only relates them to the tensor indices.

## Main results

* `MPSTensor.stochasticFamily_iIndex`: the full-word index is the classical index.
* `MPSTensor.stochasticFamily_qIndex`: the vector-spreading index is the classical index.
* `MPSTensor.stochasticFamily_primitive_and_indices`: the primitive stochastic case.
-/

noncomputable section

namespace MPSTensor

variable {D : ℕ} [NeZero D]

/-- The full-Kraus-rank index of the actual stochastic embedding is the
classical positive-power index. Source: arXiv:0909.5347, Proposition 2,
lines 478–494. The equality also covers nonprimitive nonnegative matrices. -/
theorem stochasticFamily_iIndex (a : Matrix (Fin D) (Fin D) ℝ)
    (ha : ∀ i j, 0 ≤ a i j) :
    iIndex (Kraus.stochasticFamily a) = Matrix.positivePowerIndex a := by
  unfold iIndex Matrix.positivePowerIndex
  apply congrArg (sInf : Set ℕ → ℕ)
  ext n
  cases n with
  | zero => simp
  | succ n =>
      exact and_congr_right fun _ ↦ Kraus.stochasticFamily_wordSpan_succ_eq_top_iff a ha n

/-- The primitivity index of the actual stochastic embedding is the
classical positive-power index. Source: arXiv:0909.5347, Proposition 2,
lines 478–494. The equality also covers nonprimitive nonnegative matrices. -/
theorem stochasticFamily_qIndex (a : Matrix (Fin D) (Fin D) ℝ)
    (ha : ∀ i j, 0 ≤ a i j) :
    qIndex (Kraus.stochasticFamily a) = Matrix.positivePowerIndex a := by
  unfold qIndex Matrix.positivePowerIndex
  apply congrArg (sInf : Set ℕ → ℕ)
  ext n
  cases n with
  | zero => simp
  | succ n =>
      exact and_congr_right fun _ ↦ Kraus.stochasticFamily_vectorSpreadSpan_succ_iff a ha n

/-- Classical primitivity gives the paper's vector-spreading primitivity of
the actual stochastic Kraus family. Source: arXiv:0909.5347, Proposition 2,
lines 478–494. Classical primitivity is expressed by a strictly positive
positive-length matrix power. -/
theorem stochasticFamily_isPrimitivePaper (a : Matrix (Fin D) (Fin D) ℝ)
    (ha : ∀ i j, 0 ≤ a i j)
    (hp : ∃ n : ℕ, 0 < n ∧ ∀ i j : Fin D, 0 < (a ^ n) i j) :
    IsPrimitivePaper (Kraus.stochasticFamily a) := by
  obtain ⟨n, hn, hp⟩ := hp
  refine ⟨n, hn, ?_⟩
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ n => exact (Kraus.stochasticFamily_vectorSpreadSpan_succ_iff a ha n).mpr hp

/-- A primitive column-stochastic matrix has a primitive quantum embedding
and `q(E) = p(a) = i(K)`, as stated in arXiv:0909.5347, Proposition 2,
source lines 478–494. No word-span or vector-spreading condition is supplied. -/
theorem stochasticFamily_primitive_and_indices (a : Matrix (Fin D) (Fin D) ℝ)
    (ha : a ∈ Matrix.colStochastic ℝ (Fin D))
    (hp : ∃ n : ℕ, 0 < n ∧ ∀ i j : Fin D, 0 < (a ^ n) i j) :
    IsPrimitivePaper (Kraus.stochasticFamily a) ∧
      qIndex (Kraus.stochasticFamily a) = Matrix.positivePowerIndex a ∧
      Matrix.positivePowerIndex a = iIndex (Kraus.stochasticFamily a) := by
  have hnonneg : ∀ i j, 0 ≤ a i j := fun _ _ ↦ Matrix.nonneg_of_mem_colStochastic ha
  exact ⟨stochasticFamily_isPrimitivePaper a hnonneg hp,
    stochasticFamily_qIndex a hnonneg, (stochasticFamily_iIndex a hnonneg).symm⟩

end MPSTensor
