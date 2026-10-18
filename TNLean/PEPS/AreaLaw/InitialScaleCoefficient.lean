/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.ScaleRecurrence

/-!
# An explicit coefficient for the initial scale recurrence

The initial safe-box estimate follows by iterating a scale recurrence and comparing
an arbitrary positive scale with the next integral power of the dilation factor.
The coefficient below retains the initial value, the inhomogeneous term, and the
gap between the two recurrence scales as separate parameters.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  proof of Proposition 3.3, `02-initial.tex`, lines 648–669, revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace TNLean.PEPS.AreaLaw

/-- The coefficient obtained by summing the recurrence error and rounding up one scale.
This is an auxiliary explicit version of the coefficient in Proposition 3.3. -/
noncomputable def initialScaleCoefficient (M : ℕ) (lam K initial : ℝ) : ℝ :=
  lam * (max initial 0 + K / (lam - M))

/-- A scale recurrence gives a power bound with the named coefficient.
The hypotheses are those of the scale-recurrence step in Proposition 3.3;
no sign condition on the initial value is needed. -/
theorem le_initialScaleCoefficient_mul_rpow {F : ℕ → ℝ} {M : ℕ} {lam K : ℝ}
    (hF : Monotone F) (hM : 2 ≤ M) (hlam : (M : ℝ) < lam) (hK : 0 ≤ K)
    (hrec : ∀ r, 1 ≤ r → F (M * r) ≤ lam * F r + K * r)
    {r : ℕ} (hr : 1 ≤ r) :
    F r ≤ initialScaleCoefficient M lam K (F 1) *
      (r : ℝ) ^ (Real.log lam / Real.log M) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hMone : (1 : ℝ) < M := by exact_mod_cast hM
  have hlampos : 0 < lam := hMpos.trans hlam
  have hgap : 0 < lam - M := sub_pos.mpr hlam
  have hlog : 0 < Real.log M := Real.log_pos hMone
  let B := max (F 1) 0 + K / (lam - M)
  have hB : 0 ≤ B := add_nonneg (le_max_right _ _) (div_nonneg hK hgap.le)
  have hpowers (j : ℕ) : F (M ^ j) ≤ B * lam ^ j := by
    have hiter := Entropy.le_pow_of_scale_recurrence (by omega) hlam hrec j
    have hinit := mul_le_mul_of_nonneg_left (le_max_left (F 1) 0)
      (pow_nonneg hlampos.le j)
    have herror : 0 ≤ K / (lam - M) * (M : ℝ) ^ j := by positivity
    dsimp [B]
    nlinarith
  let e := Real.log lam / Real.log M
  have he : 0 ≤ e := div_nonneg (Real.log_nonneg (hMone.trans hlam).le) hlog.le
  have hbase : (M : ℝ) ^ e = lam := by
    rw [Real.rpow_def_of_pos hMpos]
    have hcancel : Real.log M * e = Real.log lam := by
      dsimp [e]
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ hlog.ne']
    rw [hcancel, Real.exp_log hlampos]
  let j := Nat.log M r
  have hlower : (M : ℝ) ^ j ≤ (r : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self M (by omega : r ≠ 0)
  have hupper : r ≤ M ^ (j + 1) :=
    (Nat.lt_pow_succ_log_self (by omega : 1 < M) r).le
  have hpower : lam ^ j ≤ (r : ℝ) ^ e := by
    calc
      lam ^ j = ((M : ℝ) ^ e) ^ j := by rw [hbase]
      _ = ((M : ℝ) ^ j) ^ e := Real.rpow_pow_comm hMpos.le e j
      _ ≤ (r : ℝ) ^ e := Real.rpow_le_rpow (by positivity) hlower he
  calc
    F r ≤ F (M ^ (j + 1)) := hF hupper
    _ ≤ B * lam ^ (j + 1) := hpowers (j + 1)
    _ = (lam * B) * lam ^ j := by ring
    _ ≤ (lam * B) * (r : ℝ) ^ e :=
      mul_le_mul_of_nonneg_left hpower (mul_nonneg hlampos.le hB)
    _ = _ := rfl

end TNLean.PEPS.AreaLaw
