/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.SizeBondTrimming
import TNLean.MPS.AreaLaw.ViableSet.BondTrimmingBound
import TNLean.MPS.AreaLaw.Huang.FilterPolynomial

/-!
# Uniform budgets for successive viable sets

Size trimming resets the family size at each cut, and independent bond trimming resets
the individual bond bound. The finite Gaussian filter then multiplies these budgets by
its actual energy count and simultaneous operator-Schmidt rank bound. The resulting
budgets are polynomial uniformly before the chain length is chosen.

**Local fix (trimming radius):** The construction uses the corrected quadratic radius
recorded at <https://sirui-lu.com/QICLean/paper-gaps/lvv13_trimming_radius.pdf>.
The size coefficient uses the library constant-cut bond and corrected net exponent,
as documented in `docs/paper-gaps/lvv13_constant_bond.tex`; the Gaussian parameters have
the conservative quantitative scope of Huang, arXiv:1406.6355v6, Section 5.4.

Source: LVV13, arXiv:1307.5143v1, `algo53.tex`, Claims `c:2`, `c:trim`,
`c:errorreduction`, lines 520--592, and the final induction, lines 652--678.
-/

namespace TNLean.MPS.AreaLaw

/-- The viability precision constant used in size trimming and the successive induction.
LVV13, `algo53.tex`, Claims `c:2` and `c:errorreduction`, lines 520--592. -/
noncomputable def lvvSuccessiveError (Delta : ℝ) : ℝ := (Delta / 169) ^ 2

/-- Natural degree of the library-bond size-trimming cardinality estimate.
LVV13, `algo53.tex`, Claim `c:2`, lines 520--527, with the documented net exponent. -/
noncomputable def lvvSizeTrimmingDegree (q : ℕ) (Delta : ℝ) : ℕ :=
  2 * (q * constantCutBond q 1 1 Delta (lvvSuccessiveError Delta)) ^ 2

/-- Coefficient of the actual polynomial size-trimming family, before length is chosen.
LVV13, `algo53.tex`, Claim `c:2`, lines 520--527, using the library constant-cut bound. -/
noncomputable def lvvSizeTrimmingCoefficient (q : ℕ) (Delta : ℝ) : ℕ :=
  let c := lvvSuccessiveError Delta
  let D := constantCutBond q 1 1 Delta c
  let A := ⌈2 * ((q * D : ℕ) : ℝ) ^ 2 / c⌉₊
  (D + 1) * D * (2 * A + 1) ^ lvvSizeTrimmingDegree q Delta

/-- Cardinality budget at every positive cut, after actual trimming and filtering.
LVV13, `algo53.tex`, final induction, lines 652--678, with Huang's finite Gaussian filter. -/
noncomputable def lvvSuccessiveCardBound (q : ℕ) (Delta : ℝ) (L : ℕ) : ℕ :=
  lvvSizeTrimmingCoefficient q Delta * L ^ lvvSizeTrimmingDegree q Delta *
    huangEnergyCount (lvvSuccessiveError Delta) Delta L *
    huangFilterRankBound q (lvvSuccessiveError Delta) Delta L

/-- Individual MPS bond budget at every positive cut, after actual trimming and filtering.
LVV13, `algo53.tex`, Claims `c:trim`, `c:errorreduction`, lines 549--592. -/
noncomputable def lvvSuccessiveBondBound (q : ℕ) (Delta : ℝ) (L : ℕ) : ℕ :=
  huangFilterRankBound q (lvvSuccessiveError Delta) Delta L *
    max 1 (bondTrimmingRadius L (lvvReferenceBond q Delta L))

/-- The chosen viability precision constant is positive for a positive gap.
LVV13, `algo53.tex`, Claim `c:2`, lines 520--527. -/
theorem lvvSuccessiveError_pos {Delta : ℝ} (hDelta : 0 < Delta) :
    0 < lvvSuccessiveError Delta := sq_pos_of_pos (div_pos hDelta (by norm_num))

/-- One natural-coefficient polynomial bounds the successive family size, individual
bond budget and final-span bond budget, with constants chosen before length.
LVV13, `algo53.tex`, final induction, lines 652--678, in the stated quantitative scope. -/
theorem exists_lvvSuccessive_uniform_polynomial {q : ℕ} (hq : 1 ≤ q) {Delta : ℝ}
    (hDelta : 0 < Delta) :
    ∃ P d : ℕ, 1 ≤ P ∧ ∀ L : ℕ, 1 ≤ L →
      max 1 (lvvSuccessiveCardBound q Delta L) ≤ P * (L + 1) ^ d ∧
      max 1 (lvvSuccessiveBondBound q Delta L) ≤ P * (L + 1) ^ d ∧
      lvvSuccessiveCardBound q Delta L * max 1 (lvvSuccessiveBondBound q Delta L) ≤
        P * (L + 1) ^ d := by
  obtain ⟨C, d, hC, hfilter⟩ :=
    exists_huangFilter_uniform_nat_polynomial hq (lvvSuccessiveError_pos hDelta) hDelta
  obtain ⟨M, p, hM, hradius⟩ := exists_bondTrimmingRadius_lvvReferenceBond_polynomial q Delta
  let A := max 1 (lvvSizeTrimmingCoefficient q Delta * C)
  let B := C * max 1 ⌈M⌉₊
  have hA : 1 ≤ A := le_max_left _ _
  have hB : 1 ≤ B := by
    dsimp only [B]
    simpa only [one_mul] using Nat.mul_le_mul hC (le_max_left 1 ⌈M⌉₊)
  refine ⟨A * B, (lvvSizeTrimmingDegree q Delta + d) + (d + p), ?_, ?_⟩
  · simpa only [one_mul] using Nat.mul_le_mul hA hB
  · intro L hL
    have hL1 : 1 ≤ L + 1 := by omega
    have hradiusNat : bondTrimmingRadius L (lvvReferenceBond q Delta L) ≤ ⌈M⌉₊ * L ^ p := by
      have hreal := (hradius L hL).trans
        (mul_le_mul_of_nonneg_right (Nat.le_ceil M) (pow_nonneg (Nat.cast_nonneg L) p))
      exact_mod_cast hreal
    have hradiusMax : max 1 (bondTrimmingRadius L (lvvReferenceBond q Delta L)) ≤
        max 1 ⌈M⌉₊ * (L + 1) ^ p := by
      apply max_le
      · simpa only [one_mul] using Nat.mul_le_mul (le_max_left 1 ⌈M⌉₊) (one_le_pow₀ hL1)
      · exact hradiusNat.trans (Nat.mul_le_mul (le_max_right 1 ⌈M⌉₊)
          (Nat.pow_le_pow_left (Nat.le_succ L) p))
    have hcard : max 1 (lvvSuccessiveCardBound q Delta L) ≤
        A * (L + 1) ^ (lvvSizeTrimmingDegree q Delta + d) := by
      apply max_le
      · simpa only [one_mul] using Nat.mul_le_mul hA (one_le_pow₀ hL1)
      · calc
          _ = (lvvSizeTrimmingCoefficient q Delta * L ^ lvvSizeTrimmingDegree q Delta) *
              (huangEnergyCount (lvvSuccessiveError Delta) Delta L *
                huangFilterRankBound q (lvvSuccessiveError Delta) Delta L) := by
              dsimp only [lvvSuccessiveCardBound]
              ring
          _ ≤ (lvvSizeTrimmingCoefficient q Delta * (L + 1) ^ lvvSizeTrimmingDegree q Delta) *
              (C * (L + 1) ^ d) := Nat.mul_le_mul
                (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ L) _))
                (hfilter L).2.2.2
          _ = (lvvSizeTrimmingCoefficient q Delta * C) *
              (L + 1) ^ (lvvSizeTrimmingDegree q Delta + d) := by rw [pow_add]; ring
          _ ≤ _ := Nat.mul_le_mul_right _ (le_max_right _ _)
    have hbond : max 1 (lvvSuccessiveBondBound q Delta L) ≤ B * (L + 1) ^ (d + p) := by
      apply max_le
      · simpa only [one_mul] using Nat.mul_le_mul hB (one_le_pow₀ hL1)
      · calc
          _ ≤ (C * (L + 1) ^ d) * (max 1 ⌈M⌉₊ * (L + 1) ^ p) :=
            Nat.mul_le_mul (hfilter L).2.2.1 hradiusMax
          _ = B * (L + 1) ^ (d + p) := by dsimp only [B]; rw [pow_add]; ring
    have hproduct := Nat.mul_le_mul hcard hbond
    rw [mul_mul_mul_comm, ← pow_add] at hproduct
    have hleft : max 1 (lvvSuccessiveCardBound q Delta L) ≤
        max 1 (lvvSuccessiveCardBound q Delta L) * max 1 (lvvSuccessiveBondBound q Delta L) := by
      simpa only [mul_one] using Nat.mul_le_mul_left
        (max 1 (lvvSuccessiveCardBound q Delta L)) (le_max_left 1 _)
    have hright : max 1 (lvvSuccessiveBondBound q Delta L) ≤
        max 1 (lvvSuccessiveCardBound q Delta L) * max 1 (lvvSuccessiveBondBound q Delta L) := by
      simpa only [one_mul] using Nat.mul_le_mul_right
        (max 1 (lvvSuccessiveBondBound q Delta L)) (le_max_left 1 _)
    exact ⟨hleft.trans hproduct, hright.trans hproduct,
      (Nat.mul_le_mul_right _ (le_max_right 1 _)).trans hproduct⟩

end TNLean.MPS.AreaLaw
