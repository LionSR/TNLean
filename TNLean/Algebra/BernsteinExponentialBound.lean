/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.TraceExpLogConcavity
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The variance-sensitive Bernstein exponential bound

For a centered finite uniform Hermitian family of norm at most `R`, its logarithmic
moment generating function is bounded above by the variance norm times
`θ² / (2 (1 - θ R / 3))`. The scalar exponential majorant is proved from the
factorial estimate `2 * 3^k ≤ (k + 2)!`; functional calculus gives the matrix bound.

This is an auxiliary finite uniform estimate for Tropp, *User-friendly tail bounds
for sums of random matrices*, Theorem 6.1(ii) and its proof in Section 6.1:
https://tropp.caltech.edu/papers/Tro11-User-Friendly-preprint.pdf.
It is not a probability tail bound.
-/

open scoped BigOperators

namespace Real

private theorem factorial_bernstein (k : ℕ) :
    (2 : ℝ) * 3 ^ k ≤ (k + 2).factorial := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hf : ((k + 1 + 2).factorial : ℝ) = (k + 3) * (k + 2).factorial := by
      rw [show k + 1 + 2 = k + 2 + 1 by omega, Nat.factorial_succ]
      push_cast
      ring
    rw [hf, pow_succ]
    calc
      (2 : ℝ) * (3 ^ k * 3) = 3 * (2 * 3 ^ k) := by ring
      _ ≤ (3 : ℝ) * (k + 2).factorial := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ ≤ ((k : ℝ) + 3) * (k + 2).factorial :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast (show 3 ≤ k + 3 by omega))
          (Nat.cast_nonneg _)

/-- The scalar exponential remainder bound giving the Bernstein coefficient `1/3`.
Used in the proof of Tropp, Theorem 6.1(ii). -/
theorem exp_le_one_add_add_sq_div {x a : ℝ} (ha : 0 ≤ a) (ha3 : a < 3) (hx : |x| ≤ a) :
    exp x ≤ 1 + x + x ^ 2 / (2 * (1 - a / 3)) := by
  have hs : HasSum (fun k : ℕ ↦ x ^ k / k.factorial) (exp x) := by
    simpa only [← Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp x
  have htail : HasSum (fun k : ℕ ↦ x ^ (k + 2) / (k + 2).factorial)
      (exp x - (1 + x)) := by
    have ht := (hasSum_nat_add_iff' 2).mpr hs
    simpa [Finset.sum_range_succ] using ht
  have hg := (hasSum_geometric_of_lt_one (show 0 ≤ a / 3 by positivity)
    (show a / 3 < 1 by linarith)).mul_left (x ^ 2 / 2)
  have hterm (k : ℕ) : x ^ (k + 2) / (k + 2).factorial ≤
      (x ^ 2 / 2) * (a / 3) ^ k := by
    have hfac := factorial_bernstein k
    have hxp : x ^ k ≤ a ^ k := (le_abs_self _).trans
      (by simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg x) hx k)
    have hden : (0 : ℝ) < (k + 2).factorial := by positivity
    calc
      _ = x ^ 2 * x ^ k / (k + 2).factorial := by rw [pow_add]; ring
      _ ≤ x ^ 2 * a ^ k / (k + 2).factorial := by gcongr
      _ ≤ x ^ 2 * a ^ k / (2 * 3 ^ k) := by gcongr
      _ = _ := by rw [div_pow]; ring
  have hle := hasSum_le hterm htail hg
  calc
    exp x ≤ x ^ 2 / 2 * (1 - a / 3)⁻¹ + (1 + x) := sub_le_iff_le_add.mp hle
    _ = _ := by rw [div_mul_eq_div_mul_one_div]; ring

end Real

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder

namespace Matrix

/-- Functional-calculus form of the scalar Bernstein exponential bound.
An auxiliary estimate for Tropp, Theorem 6.1(ii). -/
theorem exp_smul_le_bernstein {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {Z : Matrix n n ℂ} (hZ : Z.IsHermitian) {R θ : ℝ}
    (hR : 0 ≤ R) (hθ : 0 ≤ θ) (hθR : θ * R < 3) (hnorm : ‖Z‖ ≤ R) :
    NormedSpace.exp (θ • Z) ≤
      1 + θ • Z + (θ ^ 2 / (2 * (1 - θ * R / 3))) • Z ^ 2 := by
  have hspec (x : ℝ) (hx : x ∈ spectrum ℝ Z) : |θ * x| ≤ θ * R := by
    rw [abs_mul, abs_of_nonneg hθ]
    exact mul_le_mul_of_nonneg_left ((spectrum.norm_le_norm_of_mem hx).trans hnorm) hθ
  have hle : cfc (fun x : ℝ ↦ Real.exp (θ * x)) Z ≤
      cfc (fun x : ℝ ↦ 1 + θ * x +
        (θ ^ 2 / (2 * (1 - θ * R / 3))) * x ^ 2) Z := by
    apply cfc_mono (hf := by fun_prop) (hg := by fun_prop)
    intro x hx
    have h := Real.exp_le_one_add_add_sq_div (mul_nonneg hθ hR) hθR (hspec x hx)
    convert h using 1
    ring
  rw [cfc_comp_const_mul θ Real.exp Z (ha := hZ.isSelfAdjoint),
    CFC.real_exp_eq_normedSpace_exp ((hZ.smul (IsSelfAdjoint.all θ)).isSelfAdjoint),
    cfc_add Z _ _ (by fun_prop) (by fun_prop),
    cfc_add Z _ _ (by fun_prop) (by fun_prop), cfc_const_one ℝ Z hZ.isSelfAdjoint,
    cfc_const_mul_id θ Z hZ.isSelfAdjoint, cfc_const_mul _ (fun x : ℝ ↦ x ^ 2) Z (by fun_prop),
    cfc_pow_id Z 2 hZ.isSelfAdjoint] at hle
  exact hle

end Matrix

namespace Matrix

open Classical in
/-- The logarithmic moment generating function of a centered finite uniform Hermitian
family is bounded by its variance norm, with the Bernstein coefficient `1/3`.
An auxiliary finite uniform estimate for Tropp, Theorem 6.1(ii). -/
theorem log_average_exp_le_bernstein
    {α n : Type*} [Fintype α] [Nonempty α] [Fintype n] [DecidableEq n] [Nonempty n]
    (Z : α → Matrix n n ℂ) (hZ : ∀ a, (Z a).IsHermitian)
    (hmean : ∑ a, Z a = 0) {R θ : ℝ}
    (hR : 0 ≤ R) (hθ : 0 ≤ θ) (hθR : θ * R < 3) (hnorm : ∀ a, ‖Z a‖ ≤ R) :
    CFC.log ((Fintype.card α : ℝ)⁻¹ • ∑ a, NormedSpace.exp (θ • Z a)) ≤
      (θ ^ 2 / (2 * (1 - θ * R / 3)) *
        ‖(Fintype.card α : ℝ)⁻¹ • ∑ a, Z a ^ 2‖) • (1 : Matrix n n ℂ) := by
  classical
  let c : ℝ := θ ^ 2 / (2 * (1 - θ * R / 3))
  let M : Matrix n n ℂ := (Fintype.card α : ℝ)⁻¹ •
    ∑ a, NormedSpace.exp (θ • Z a)
  let V : Matrix n n ℂ := (Fintype.card α : ℝ)⁻¹ • ∑ a, Z a ^ 2
  have hα : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hc : 0 ≤ c := by
    dsimp [c]
    apply div_nonneg (sq_nonneg θ)
    linarith
  have hmass : (Fintype.card α : ℝ)⁻¹ * Fintype.card α = 1 := inv_mul_cancel₀ hα.ne'
  have hexp (a : α) : (NormedSpace.exp (θ • Z a)).PosDef := by
    have hθZ := ((hZ a).smul (IsSelfAdjoint.all θ)).isSelfAdjoint
    rw [← Matrix.isStrictlyPositive_iff_posDef, ← CFC.real_exp_eq_normedSpace_exp hθZ]
    exact (cfc_isStrictlyPositive_iff Real.exp _ (by fun_prop) hθZ).mpr
      (fun x _ ↦ Real.exp_pos x)
  have hM : M.PosDef := (Matrix.posDef_sum Finset.univ_nonempty
    (fun a _ ↦ hexp a)).smul (inv_pos.mpr hα)
  have hV : V.IsHermitian := by
    apply IsSelfAdjoint.isHermitian
    apply IsSelfAdjoint.smul (IsSelfAdjoint.all _)
    exact isSelfAdjoint_sum Finset.univ fun a _ ↦ (hZ a).isSelfAdjoint.pow 2
  have hle : M ≤ 1 + c • V := by
    have hs := smul_le_smul_of_nonneg_left
      (Finset.sum_le_sum (fun a (_ha : a ∈ Finset.univ) ↦
        exp_smul_le_bernstein (hZ a) hR hθ hθR (hnorm a))) (inv_nonneg.mpr hα.le)
    change M ≤ (Fintype.card α : ℝ)⁻¹ • ∑ a, (1 + θ • Z a + c • Z a ^ 2) at hs
    simpa only [Finset.sum_add_distrib, ← Finset.smul_sum, hmean, smul_zero, add_zero,
      Finset.sum_const, Finset.card_univ, smul_add, smul_smul, nsmul_eq_mul,
      ← Nat.cast_smul_eq_nsmul ℝ, hmass, one_smul, smul_comm _ c, V, smul_smul] using hs
  have hVle : V ≤ ‖V‖ • (1 : Matrix n n ℂ) := by
    simpa [Algebra.algebraMap_eq_smul_one] using
      hV.isSelfAdjoint.le_algebraMap_norm_self
  have hcap : M ≤ (1 + c * ‖V‖) • (1 : Matrix n n ℂ) := by
    calc
      M ≤ 1 + c • V := hle
      _ ≤ 1 + c • (‖V‖ • (1 : Matrix n n ℂ)) :=
        add_le_add_right (smul_le_smul_of_nonneg_left
          hVle hc) 1
      _ = _ := by module
  have hspectrum : ∀ x ∈ spectrum ℝ M, x ≤ 1 + c * ‖V‖ :=
    (le_algebraMap_iff_spectrum_le hM.isHermitian.isSelfAdjoint).mp
      (by simpa [Algebra.algebraMap_eq_smul_one] using hcap)
  have hpositive : ∀ x ∈ spectrum ℝ M, 0 < x :=
    (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos M hM.isHermitian.isSelfAdjoint).mp
      (Matrix.isStrictlyPositive_iff_posDef.mpr hM)
  change CFC.log M ≤ (c * ‖V‖) • (1 : Matrix n n ℂ)
  rw [CFC.log, ← Algebra.algebraMap_eq_smul_one]
  apply cfc_le_algebraMap Real.log (c * ‖V‖) M
    (hf := Real.continuousOn_log.mono (fun x hx ↦ (hpositive x hx).ne'))
    (ha := hM.isHermitian.isSelfAdjoint)
  intro x hx
  exact (Real.log_le_sub_one_of_pos (hpositive x hx)).trans (by linarith [hspectrum x hx])

end Matrix
