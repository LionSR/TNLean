/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Nat.Log
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Dyadic anchors and the reflection fold

Let `N` be the least power of two with `N ≥ L`, so `N < 2L`. A dyadic block of side `2 ^ j`
of the padded square `{0, …, N - 1} ^ 2` with block indices `(r, s)` has anchor
`(2 ^ j r + 2 ^ (j - 1), 2 ^ j s + 2 ^ (j - 1))` for `j ≥ 1` and `(r, s)` for `j = 0`.
Every anchor coordinate lies in its block, so it determines the block index by division by
`2 ^ j`, and a nonunit anchor coordinate `2 ^ (j - 1) (2 s + 1)` has exact two-adic
valuation `j - 1`, so it determines the scale.

The reflection `f x = x` for `x ≤ L - 1` and `f x = 2 (L - 1) - x` otherwise folds the
padded coordinates onto `{0, …, L - 1}`. It fixes the genuine coordinates, maps adjacent
coordinates to adjacent coordinates, and every coordinate and every unit interval has at
most two preimages.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), §8.3, equation `eq:anchors` and the proof of
  Lemma 8.2 `lem:routing`, `07-assembly.tex:102–161`.
-/

namespace TNLean.PEPS.Approximation

/-! ### The padded side -/

/-- The least power of two which is at least `L`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), §8.3, `07-assembly.tex:104–105`. -/
def paddedSide (L : ℕ) : ℕ := 2 ^ Nat.clog 2 L

/-- The padded side is at least the genuine side. -/
theorem le_paddedSide (L : ℕ) : L ≤ paddedSide L :=
  Nat.le_pow_clog one_lt_two L

/-- The padded side is the least power of two which is at least `L`. -/
theorem paddedSide_le_of_le_pow {L k : ℕ} (h : L ≤ 2 ^ k) : paddedSide L ≤ 2 ^ k :=
  Nat.pow_le_pow_right two_pos (Nat.clog_le_of_le_pow h)

/-- The padded side is less than twice the genuine side.

Source: Polynomial-PEPS manuscript (Sept 24 2026), §8.3, `07-assembly.tex:104`:
“Let `N` be the least power of two with `N ≥ L`, so `N < 2L`.” -/
theorem paddedSide_lt_two_mul {L : ℕ} (hL : 0 < L) : paddedSide L < 2 * L := by
  rcases Nat.lt_or_ge 1 L with h | h
  · have hpred := Nat.pow_pred_clog_lt_self one_lt_two h
    have hpos : 0 < Nat.clog 2 L := Nat.clog_pos one_lt_two h
    unfold paddedSide
    calc 2 ^ Nat.clog 2 L = 2 * 2 ^ (Nat.clog 2 L).pred := by
          rw [← pow_succ']; exact congrArg _ (Nat.succ_pred_eq_of_pos hpos).symm
      _ < 2 * L := by omega
  · have : L = 1 := by omega
    subst this
    simp [paddedSide]

/-! ### Dyadic anchors -/

/-- One coordinate of the anchor of a dyadic block of side `2 ^ j` with block index `r`. It is
also one coordinate of the integer address of that square in the distribution protocol.

Source: Polynomial-PEPS manuscript (Sept 24 2026), equation `eq:anchors`,
`07-assembly.tex:108–112`, and equation `eq:geometry-addresses`, `06-geometry.tex:633–642`. -/
def dyadicAnchor (j r : ℕ) : ℕ := if j = 0 then r else 2 ^ j * r + 2 ^ (j - 1)

/-- A nonunit anchor coordinate is the odd multiple `2 ^ (j - 1) (2 r + 1)`. -/
theorem dyadicAnchor_of_ne_zero {j : ℕ} (hj : j ≠ 0) (r : ℕ) :
    dyadicAnchor j r = 2 ^ (j - 1) * (2 * r + 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
  simp [dyadicAnchor, pow_succ]
  ring

/-- The anchor coordinate lies in its block: `2 ^ j r ≤ a < 2 ^ j (r + 1)`. -/
theorem dyadicAnchor_mem_block (j r : ℕ) :
    2 ^ j * r ≤ dyadicAnchor j r ∧ dyadicAnchor j r < 2 ^ j * (r + 1) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [dyadicAnchor]
  · have hlt : 2 ^ (j - 1) < 2 ^ j := Nat.pow_lt_pow_right one_lt_two (by omega)
    simp only [dyadicAnchor, hj.ne', ite_false]
    exact ⟨Nat.le_add_right _ _, by rw [mul_add, mul_one]; exact Nat.add_lt_add_left hlt _⟩

/-- The anchor coordinate determines its block index by division by the block side. -/
theorem dyadicAnchor_div (j r : ℕ) : dyadicAnchor j r / 2 ^ j = r := by
  obtain ⟨h1, h2⟩ := dyadicAnchor_mem_block j r
  exact Nat.div_eq_of_lt_le (by rw [mul_comm]; exact h1) (by rw [mul_comm]; exact h2)

/-- An anchor of a block inside the padded square lies in the padded square.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `07-assembly.tex:113–114`: “All anchors
lie on the padded grid.” -/
theorem dyadicAnchor_lt {j r M : ℕ} (h : 2 ^ j * (r + 1) ≤ M) : dyadicAnchor j r < M :=
  (dyadicAnchor_mem_block j r).2.trans_le h

/-- **Row valuation.** A nonunit anchor coordinate has exact two-adic valuation `j - 1`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), proof of Lemma 8.2 `lem:routing`,
`07-assembly.tex:134–137`. -/
theorem padicValNat_two_dyadicAnchor {j : ℕ} (hj : j ≠ 0) (r : ℕ) :
    padicValNat 2 (dyadicAnchor j r) = j - 1 := by
  rw [dyadicAnchor_of_ne_zero hj, padicValNat.mul (by positivity) (by omega),
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by omega), add_zero]

/-- A nonunit anchor coordinate is nonzero. -/
theorem dyadicAnchor_ne_zero {j : ℕ} (hj : j ≠ 0) (r : ℕ) : dyadicAnchor j r ≠ 0 := by
  rw [dyadicAnchor_of_ne_zero hj]; positivity

/-- A nonunit anchor coordinate determines its scale and block index: such a row or column
belongs to a unique nonunit scale.

Source: Polynomial-PEPS manuscript (Sept 24 2026), proof of Lemma 8.2 `lem:routing`,
`07-assembly.tex:134–137`. -/
theorem dyadicAnchor_inj {j j' r r' : ℕ} (hj : j ≠ 0) (hj' : j' ≠ 0)
    (h : dyadicAnchor j r = dyadicAnchor j' r') : j = j' ∧ r = r' := by
  have hjj : j = j' := by
    have := congrArg (padicValNat 2) h
    rw [padicValNat_two_dyadicAnchor hj, padicValNat_two_dyadicAnchor hj'] at this
    omega
  subst hjj
  exact ⟨rfl, by rw [← dyadicAnchor_div j r, h, dyadicAnchor_div]⟩

/-! ### The reflection fold -/

/-- The reflection of padded coordinates onto `{0, …, L - 1}`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), proof of Lemma 8.2 `lem:routing`,
`07-assembly.tex:148–153`. -/
def foldCoord (L x : ℕ) : ℕ := if x < L then x else 2 * (L - 1) - x

/-- The fold fixes the genuine coordinates.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `07-assembly.tex:158–159`: “The map
fixes genuine output coordinates.” -/
theorem foldCoord_of_lt {L x : ℕ} (hx : x < L) : foldCoord L x = x := by
  simp [foldCoord, hx]

/-- The fold takes values in `{0, …, L - 1}`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `07-assembly.tex:154`. -/
theorem foldCoord_lt {L : ℕ} (hL : 0 < L) (x : ℕ) : foldCoord L x < L := by
  unfold foldCoord; split_ifs <;> omega

/-- The fold maps adjacent padded coordinates to adjacent coordinates.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `07-assembly.tex:155`. -/
theorem foldCoord_succ {L x : ℕ} (hx : x + 2 < 2 * L) :
    foldCoord L (x + 1) = foldCoord L x + 1 ∨ foldCoord L x = foldCoord L (x + 1) + 1 := by
  unfold foldCoord; split_ifs <;> omega

/-- Every coordinate has at most two padded preimages: `x` and `2 (L - 1) - x`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `07-assembly.tex:155–156`. -/
theorem eq_or_eq_of_foldCoord_eq {L x u : ℕ} (hx : x + 1 < 2 * L) (h : foldCoord L x = u) :
    x = u ∨ x = 2 * (L - 1) - u := by
  unfold foldCoord at h; split_ifs at h <;> omega

/-- Every unit interval `{u, u + 1}` has at most two padded unit-interval preimages, with
left endpoints `u` and `2 L - 3 - u`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `07-assembly.tex:155–156`. -/
theorem eq_or_eq_of_foldCoord_interval {L x u : ℕ} (hx : x + 2 < 2 * L)
    (h : (foldCoord L x = u ∧ foldCoord L (x + 1) = u + 1) ∨
      (foldCoord L x = u + 1 ∧ foldCoord L (x + 1) = u)) :
    x = u ∨ x = 2 * L - 3 - u := by
  unfold foldCoord at h; split_ifs at h <;> omega

end TNLean.PEPS.Approximation
