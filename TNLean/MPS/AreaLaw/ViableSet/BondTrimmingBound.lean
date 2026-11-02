/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BondTrimming
import TNLean.MPS.AreaLaw.ViableSet.BondTrimmingReference

/-!
# Polynomial growth of the bond-trimming radius

The reference bond is the chain approximation bound at length `48 L`. Multiplication by
`(48 L)²` increases its polynomial exponent by two. The resulting integer exponent and
coefficient depend only on the local dimension and gap parameter, before the chain length
or any ground vector is supplied.

Source: Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, Lemma `l:mpsapprox`,
lines 325–328, and Claim `c:trim`, lines 549–559. The retained radius uses the quadratic
correction recorded at <https://sirui-lu.com/QICLean/paper-gaps/lvv13_trimming_radius.pdf>.
-/

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ} {Δ : ℝ}

/-- The existing polynomial chain bond bound at the rescaled length.
Source: LVV13, `algo53.tex`, Lemma `l:mpsapprox`, lines 325–328. -/
theorem lvvReferenceBond_le_mul_rpow (hL : 1 ≤ L) :
    (lvvReferenceBond q Δ L : ℝ) ≤
      Real.exp (chainIntervalEntropyBound q 1 1 Δ) *
        (2 * tailPrefactorRoot) ^ (64 * Real.sqrt ((1 + 1 / Δ) * chainBudgetConst q 1)) *
        (48 * (L : ℝ)) ^ (128 * Real.sqrt ((1 + 1 / Δ) * chainBudgetConst q 1)) := by
  simpa only [lvvReferenceBond, Nat.cast_mul, Nat.cast_ofNat] using
    (chainBondDimension_le_mul_rpow (q := q) (R := 1) (J := 1) (Δ := Δ)
      (L := 48 * L) (by omega))

/-- The corrected trimming radius has polynomial growth, with its exponent increased by two.
Source: LVV13, `algo53.tex`, Claim `c:trim`, lines 549–559, with the documented radius. -/
theorem bondTrimmingRadius_lvvReferenceBond_le_mul_rpow (hL : 1 ≤ L) :
    (bondTrimmingRadius L (lvvReferenceBond q Δ L) : ℝ) ≤
      Real.exp (chainIntervalEntropyBound q 1 1 Δ) *
        (2 * tailPrefactorRoot) ^ (64 * Real.sqrt ((1 + 1 / Δ) * chainBudgetConst q 1)) *
        (48 * (L : ℝ)) ^ (128 * Real.sqrt ((1 + 1 / Δ) * chainBudgetConst q 1) + 2) := by
  let s := Real.sqrt ((1 + 1 / Δ) * chainBudgetConst q 1)
  let C := Real.exp (chainIntervalEntropyBound q 1 1 Δ) * (2 * tailPrefactorRoot) ^ (64 * s)
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hL)
  have href : (lvvReferenceBond q Δ L : ℝ) ≤ C * (48 * (L : ℝ)) ^ (128 * s) :=
    lvvReferenceBond_le_mul_rpow hL
  calc
    _ = (48 * (L : ℝ)) ^ 2 * (lvvReferenceBond q Δ L : ℝ) := by
      simp only [bondTrimmingRadius, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ (48 * (L : ℝ)) ^ 2 * (C * (48 * (L : ℝ)) ^ (128 * s)) :=
      mul_le_mul_of_nonneg_left href (sq_nonneg _)
    _ = C * (48 * (L : ℝ)) ^ (128 * s + 2) := by
      rw [Real.rpow_add (by positivity), Real.rpow_two]
      ring

/-- A polynomial with natural degree bounds the corrected radius uniformly in the chain length.
Its coefficient and degree are fixed before the chain length or a ground vector is supplied.
Source: LVV13, `algo53.tex`, Claim `c:trim`, lines 549–559, with the documented radius. -/
theorem exists_bondTrimmingRadius_lvvReferenceBond_polynomial (q : ℕ) (Δ : ℝ) :
    ∃ (C : ℝ) (p : ℕ), 0 ≤ C ∧ ∀ L : ℕ, 1 ≤ L →
      (bondTrimmingRadius L (lvvReferenceBond q Δ L) : ℝ) ≤ C * (L : ℝ) ^ p := by
  let s := Real.sqrt ((1 + 1 / Δ) * chainBudgetConst q 1)
  let K := Real.exp (chainIntervalEntropyBound q 1 1 Δ) *
    (2 * tailPrefactorRoot) ^ (64 * s)
  let p : ℕ := ⌈128 * s + 2⌉₊
  have hK : 0 ≤ K := mul_nonneg (le_of_lt (Real.exp_pos _))
    (Real.rpow_nonneg (mul_nonneg (by norm_num) tailPrefactorRoot_pos.le) _)
  refine ⟨K * 48 ^ p, p, mul_nonneg hK (pow_nonneg (by norm_num) _), ?_⟩
  intro L hL
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  calc
    _ ≤ K * (48 * (L : ℝ)) ^ (128 * s + 2) :=
      bondTrimmingRadius_lvvReferenceBond_le_mul_rpow hL
    _ ≤ K * (48 * (L : ℝ)) ^ (p : ℝ) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by linarith) (Nat.le_ceil _)) hK
    _ = (K * 48 ^ p) * (L : ℝ) ^ p := by
      rw [Real.rpow_natCast, mul_pow]
      ring

end TNLean.MPS.AreaLaw
