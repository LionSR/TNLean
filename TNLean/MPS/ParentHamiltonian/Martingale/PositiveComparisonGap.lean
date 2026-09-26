/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.WeightedPositiveKernel

/-!
# Gap transfer through two-sided positive comparisons

Two positive operators which bound one another up to strictly positive
constants have the same kernel. Consequently a norm gap transfers through
the lower comparison, on the common kernel complement.
-/

open scoped InnerProductSpace ComplexOrder

namespace LinearMap.IsPositive

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Order between positive operators reverses the inclusion of their kernels. -/
theorem ker_le_of_le {P Q : E →ₗ[ℂ] E} (hP : P.IsPositive) (hPQ : P ≤ Q) :
    LinearMap.ker Q ≤ LinearMap.ker P := by
  intro v hv
  apply LinearMap.mem_ker.mpr
  apply hP.apply_eq_zero_of_re_inner_eq_zero
  have h := hPQ.re_inner_nonneg_left v
  have hv' := LinearMap.mem_ker.mp hv
  have hnonneg := hP.re_inner_nonneg_left v
  have hnonpos : RCLike.re ⟪P v, v⟫_ℂ ≤ 0 := by
    simpa only [LinearMap.sub_apply, hv', zero_sub, inner_neg_left, map_neg,
      neg_nonneg] using h
  exact le_antisymm hnonpos hnonneg

/-- Two-sided bounds by strictly positive multiples give equal kernels. -/
theorem ker_eq_of_smul_le_of_le_smul {P Q : E →ₗ[ℂ] E}
    (hP : P.IsPositive) (hQ : Q.IsPositive) {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hLower : (a : ℂ) • P ≤ (b : ℂ) • Q)
    (hUpper : (b : ℂ) • Q ≤ (c : ℂ) • P) :
    LinearMap.ker P = LinearMap.ker Q := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  apply le_antisymm
  · simpa only [LinearMap.ker_smul _ _ hc', LinearMap.ker_smul _ _ hb'] using
      (hQ.smul_of_nonneg (by exact_mod_cast hb.le)).ker_le_of_le hUpper
  · simpa only [LinearMap.ker_smul _ _ hb', LinearMap.ker_smul _ _ ha'] using
      (hP.smul_of_nonneg (by exact_mod_cast ha.le)).ker_le_of_le hLower

/-- A gap transfers through a two-sided positive comparison, with the ratio
of the lower comparison constants. Equality of the kernels is derived from
the two order bounds. -/
theorem norm_gap_of_smul_le_of_le_smul [FiniteDimensional ℂ E]
    {P Q : E →ₗ[ℂ] E} (hP : P.IsPositive) (hQ : Q.IsPositive)
    {a b c γ : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hγ : 0 < γ)
    (hLower : (a : ℂ) • P ≤ (b : ℂ) • Q)
    (hUpper : (b : ℂ) • Q ≤ (c : ℂ) • P)
    (hGap : ∀ v ∈ (LinearMap.ker P)ᗮ, γ * ‖v‖ ≤ ‖P v‖) :
    ∀ v ∈ (LinearMap.ker Q)ᗮ, (a * γ / b) * ‖v‖ ≤ ‖Q v‖ := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hker := hP.ker_eq_of_smul_le_of_le_smul hQ ha hb hc hLower hUpper
  have hscaledGap : ∀ v ∈ (LinearMap.ker ((a : ℂ) • P))ᗮ,
      (a * γ) * ‖v‖ ≤ ‖((a : ℂ) • P) v‖ := by
    intro v hv
    have hv' : v ∈ (LinearMap.ker P)ᗮ := by
      simpa only [LinearMap.ker_smul _ _ ha'] using hv
    simpa only [LinearMap.smul_apply, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ha, mul_assoc] using
      mul_le_mul_of_nonneg_left (hGap v hv') ha.le
  have hkerScaled : LinearMap.ker ((a : ℂ) • P) =
      LinearMap.ker ((b : ℂ) • Q) := by
    simpa only [LinearMap.ker_smul _ _ ha', LinearMap.ker_smul _ _ hb'] using hker
  have hTransfer := norm_gap_of_le_of_ker_eq
    (hP.smul_of_nonneg (by exact_mod_cast ha.le))
    (mul_nonneg ha.le hγ.le) hLower hkerScaled hscaledGap
  intro v hv
  have hv' : v ∈ (LinearMap.ker ((b : ℂ) • Q))ᗮ := by
    simpa only [LinearMap.ker_smul _ _ hb'] using hv
  have h := hTransfer v hv'
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hb).mpr
  simpa only [LinearMap.smul_apply, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hb, mul_comm b] using h

end LinearMap.IsPositive
