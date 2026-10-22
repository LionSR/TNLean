/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Monotonicity of the binary relative entropy

The binary relative entropy `a log (a / b) + (1 - a) log ((1 - a) / (1 - b))` increases in its
first argument above `b` and decreases in its second argument below `a`. Hastings' proof of the
area law (arXiv:0705.2024v4, lines 463–477) applies it with the ground-state expectation `a` of
the effect lowered to `1 − 2ε'` and the product-state expectation raised to `36 ε'`, the form in
which `le_of_lindbladUhlmann` takes eq. `LU`.

The definition `binaryRelEnt` is QICLean's `binaryRelativeEntropy` (QICLean#882) verbatim; that
declaration is not yet in the pinned QICLean. After the next pin bump the definition and the
first-argument lemma, which QICLean proves as `binaryRelativeEntropy_le_of_le`, can be replaced
by QICLean's.

## Main results

* `binaryRelEnt_le_of_le_left`: increasing in the first argument on `[b, 1]`.
* `binaryRelEnt_le_of_le_right`: decreasing in the second argument on `(0, a]`.
* `binaryRelEnt_le_of_le`: `B(a', b) ≤ B(a, x)` for `0 < x ≤ b < 1` and `b ≤ a' ≤ a ≤ 1`.

## References

* M. B. Hastings, *An area law for one-dimensional quantum systems*, J. Stat. Mech. (2007)
  P08024, arXiv:0705.2024v4, `References/0705.2024/law16.tex`, lines 463–477.
-/

namespace TNLean.MPS.AreaLaw.Hastings

/-- The binary relative entropy `a log (a / b) + (1 - a) log ((1 - a) / (1 - b))` of the
two-outcome distributions `(a, 1 - a)` and `(b, 1 - b)`. -/
noncomputable def binaryRelEnt (a b : ℝ) : ℝ :=
  a * Real.log (a / b) + (1 - a) * Real.log ((1 - a) / (1 - b))

/-- Tangent-line bound for `y ↦ y log (y / c)` at a positive point `x`. -/
private lemma mul_log_div_tangent {x y c : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (hc : 0 < c) :
    y * Real.log (x / c) + y - x ≤ y * Real.log (y / c) := by
  rcases hy.eq_or_lt with rfl | hy
  · simp only [zero_mul, zero_add, zero_sub, zero_div, Real.log_zero, mul_zero]
    linarith
  have h := Real.log_le_sub_one_of_pos (div_pos hx hy)
  rw [Real.log_div hx.ne' hy.ne'] at h
  have h' := mul_le_mul_of_nonneg_left h hy.le
  have hxy : y * (x / y - 1) = x - y := by field_simp
  rw [hxy] at h'
  rw [Real.log_div hx.ne' hc.ne', Real.log_div hy.ne' hc.ne']
  nlinarith

/-- Changing the reference point `c` to `c'` in `y log (y / c)` costs at most `y (c / c' - 1)`. -/
private lemma mul_log_div_le_of_ref {y c c' : ℝ} (hy : 0 ≤ y) (hc : 0 < c) (hc' : 0 < c') :
    y * Real.log (y / c') ≤ y * Real.log (y / c) + y * (c / c' - 1) := by
  rcases hy.eq_or_lt with rfl | hy
  · simp
  have hsplit : y / c' = y / c * (c / c') := by field_simp
  rw [hsplit, Real.log_mul (div_pos hy hc).ne' (div_pos hc hc').ne', mul_add]
  have := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hc hc')) hy.le
  linarith

/-- For `0 < b < 1`, the binary relative entropy `B(a, b)` is increasing in `a` on `[b, 1]`. -/
theorem binaryRelEnt_le_of_le_left {a a' b : ℝ} (hb₀ : 0 < b) (hb₁ : b < 1) (hba : b ≤ a)
    (haa' : a ≤ a') (ha' : a' ≤ 1) : binaryRelEnt a b ≤ binaryRelEnt a' b := by
  unfold binaryRelEnt
  have ha₀ : 0 < a := hb₀.trans_le hba
  have hb₁' : 0 < 1 - b := sub_pos.mpr hb₁
  rcases (sub_nonneg.mpr (haa'.trans ha')).eq_or_lt with h1a | h1a
  · have ha'1 : a' = 1 := le_antisymm ha' (by linarith)
    have ha1 : a = 1 := by linarith
    subst ha1 ha'1
    exact le_rfl
  have hfirst := mul_log_div_tangent ha₀ (ha₀.le.trans haa') hb₀
  have hsecond := mul_log_div_tangent h1a (sub_nonneg.mpr ha') hb₁'
  have hlog₁ : 0 ≤ Real.log (a / b) := Real.log_nonneg ((one_le_div hb₀).mpr hba)
  have hlog₂ : Real.log ((1 - a) / (1 - b)) ≤ 0 :=
    Real.log_nonpos (div_nonneg h1a.le hb₁'.le) ((div_le_one hb₁').mpr (by linarith))
  nlinarith

/-- For `0 < b ≤ b' ≤ a ≤ 1` with `b' < 1`, the binary relative entropy satisfies
`B(a, b') ≤ B(a, b)`: it is decreasing in the second argument below `a`. -/
theorem binaryRelEnt_le_of_le_right {a b b' : ℝ} (hb₀ : 0 < b) (hbb' : b ≤ b')
    (hb'a : b' ≤ a) (ha : a ≤ 1) (hb'₁ : b' < 1) : binaryRelEnt a b' ≤ binaryRelEnt a b := by
  unfold binaryRelEnt
  have hb'₀ : 0 < b' := hb₀.trans_le hbb'
  have h1b : 0 < 1 - b := by linarith
  have h1b' : 0 < 1 - b' := by linarith
  have hfirst := mul_log_div_le_of_ref (hb'₀.le.trans hb'a) hb₀ hb'₀
  have hsecond := mul_log_div_le_of_ref (sub_nonneg.mpr ha) h1b h1b'
  have hq₁ : 1 ≤ a / b' := (one_le_div hb'₀).mpr hb'a
  have hq₂ : (1 - a) / (1 - b') ≤ 1 := (div_le_one h1b').mpr (by linarith)
  have he₁ : a * (b / b' - 1) = a / b' * (b - b') := by field_simp
  have he₂ : (1 - a) * ((1 - b) / (1 - b') - 1) = (1 - a) / (1 - b') * (b' - b) := by
    field_simp
    ring
  have hr₁ : a / b' * (b - b') ≤ b - b' := by nlinarith
  have hr₂ : (1 - a) / (1 - b') * (b' - b) ≤ b' - b := by
    nlinarith [div_nonneg (sub_nonneg.mpr ha) h1b'.le]
  linarith

/-- For `0 < x ≤ b < 1` and `b ≤ a' ≤ a ≤ 1`, lowering the first argument of the binary
relative entropy to `a'` and raising the second from `x` to `b` does not increase it:
`B(a', b) ≤ B(a, x)`. This is the comparison used in Hastings, arXiv:0705.2024v4,
`law16.tex` lines 470–477. -/
theorem binaryRelEnt_le_of_le {a a' b x : ℝ} (hx : 0 < x) (hxb : x ≤ b) (hb : b < 1)
    (hba' : b ≤ a') (ha'a : a' ≤ a) (ha : a ≤ 1) : binaryRelEnt a' b ≤ binaryRelEnt a x :=
  (binaryRelEnt_le_of_le_left (hx.trans_le hxb) hb hba' ha'a ha).trans
    (binaryRelEnt_le_of_le_right hx hxb (hba'.trans ha'a) ha hb)

end TNLean.MPS.AreaLaw.Hastings
