/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CocycleCohomology

/-!
# The commutator phase of a scalar two-cocycle is a bicharacter

For a scalar two-cocycle `ω` and commuting group elements, the commutator phase
`c(g, h) = ω(g, h) ω(h, g)⁻¹` is antisymmetric, trivial when an argument is the identity, and
multiplicative in each argument. On a commutative group it is therefore a bicharacter. This is
the standard invariant used to decide whether a class on a subgroup extends: an ambient cocycle
restricts to a cocycle whose commutator phase is the restriction of a bicharacter of the ambient
group. arXiv:2502.20257 uses this obstruction for `ℤ₂ × ℤ₂ ≤ ℤ₄ × ℤ₂` in `example:z4z2`
(`Papers/2502.20257/main.tex`, lines 4383–4385, citing Blanik, Garre-Rubio and Schuch).

## Main results

* `TNLean.Algebra.ScalarCocycle.commPhase_swap`: `c(h, g) = c(g, h)⁻¹`.
* `TNLean.Algebra.ScalarCocycle.commPhase_one_right`: `c(g, 1) = 1` for a cocycle.
* `TNLean.Algebra.ScalarCocycle.commPhase_mul_right`, `commPhase_mul_left`: multiplicativity in
  each argument, for commuting arguments.
* `TNLean.Algebra.ScalarCocycle.commPhase_pow_left`: `c(gⁿ, h) = c(g, h)ⁿ`.
-/

open scoped TNLean.Algebra.ScalarCohomology

namespace TNLean.Algebra

variable {G : Type} [Group G]

namespace ScalarCocycle

omit [Group G] in
/-- The commutator phase is antisymmetric: `c(h, g) = c(g, h)⁻¹`. -/
theorem commPhase_swap (ω : ScalarCocycle G) (g h : G) :
    commPhase ω h g = (commPhase ω g h)⁻¹ := by
  simp [commPhase, mul_comm]

/-- A two-cocycle takes the value `ω(1, 1)` whenever one argument is the identity. -/
theorem apply_one_right {ω : ScalarCocycle G} (hω : groupCohomology.IsMulCocycle₂ ω) (g : G) :
    ω (g, 1) = ω (1, 1) := by
  have h := (isMulCocycle₂_iff ω).mp hω g 1 1
  simp only [mul_one] at h
  exact mul_left_cancel h

/-- A two-cocycle takes the value `ω(1, 1)` whenever one argument is the identity. -/
theorem apply_one_left {ω : ScalarCocycle G} (hω : groupCohomology.IsMulCocycle₂ ω) (g : G) :
    ω (1, g) = ω (1, 1) := by
  have h := (isMulCocycle₂_iff ω).mp hω 1 1 g
  simp only [one_mul] at h
  exact (mul_right_cancel h).symm

/-- The commutator phase of a two-cocycle is trivial when the second argument is the
identity. -/
theorem commPhase_one_right {ω : ScalarCocycle G} (hω : groupCohomology.IsMulCocycle₂ ω)
    (g : G) : commPhase ω g 1 = 1 := by
  rw [commPhase, apply_one_right hω g, apply_one_left hω g, mul_inv_cancel]

/-- **The commutator phase is multiplicative in its second argument**: for a two-cocycle and
`g` commuting with `h` and `k`, `c(g, h k) = c(g, h) c(g, k)`. -/
theorem commPhase_mul_right {ω : ScalarCocycle G} (hω : groupCohomology.IsMulCocycle₂ ω)
    {g h k : G} (hgh : g * h = h * g) (hgk : g * k = k * g) :
    commPhase ω g (h * k) = commPhase ω g h * commPhase ω g k := by
  have hc := (isMulCocycle₂_iff ω).mp hω
  have h1 := hc g h k
  have h2 := hc h g k
  have h3 := hc h k g
  rw [← hgh] at h2
  rw [← hgk] at h3
  simp only [commPhase]
  apply Units.ext
  have e1 := congrArg Units.val h1
  have e2 := congrArg Units.val h2
  have e3 := congrArg Units.val h3
  push_cast at e1 e2 e3 ⊢
  set a := (ω (g, h) : ℂ)
  set b := (ω (h, g) : ℂ)
  set c := (ω (g, k) : ℂ)
  set e := (ω (k, g) : ℂ)
  have hT : (ω (h, k) : ℂ) * ((ω (g, h * k) : ℂ) * b * e) =
      (ω (h, k) : ℂ) * (a * c * (ω (h * k, g) : ℂ)) := by
    linear_combination (-(b * e)) * e1 - (a * c) * e3 + (a * e) * e2
  have K := mul_left_cancel₀ (ω (h, k)).ne_zero hT
  have hb : b ≠ 0 := (ω (h, g)).ne_zero
  have he : e ≠ 0 := (ω (k, g)).ne_zero
  have hm : (ω (h * k, g) : ℂ) ≠ 0 := (ω (h * k, g)).ne_zero
  field_simp
  linear_combination K

/-- **The commutator phase is multiplicative in its first argument**: for a two-cocycle and
`k` commuting with `g` and `h`, `c(g h, k) = c(g, k) c(h, k)`. -/
theorem commPhase_mul_left {ω : ScalarCocycle G} (hω : groupCohomology.IsMulCocycle₂ ω)
    {g h k : G} (hgk : g * k = k * g) (hhk : h * k = k * h) :
    commPhase ω (g * h) k = commPhase ω g k * commPhase ω h k := by
  rw [commPhase_swap, commPhase_mul_right hω hgk.symm hhk.symm, commPhase_swap ω g,
    commPhase_swap ω h, mul_inv, inv_inv, inv_inv]

/-- **Powers in the first argument**: `c(gⁿ, h) = c(g, h)ⁿ` for commuting `g` and `h`. -/
theorem commPhase_pow_left {ω : ScalarCocycle G} (hω : groupCohomology.IsMulCocycle₂ ω)
    {g h : G} (hgh : g * h = h * g) (n : ℕ) : commPhase ω (g ^ n) h = commPhase ω g h ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, commPhase_swap, commPhase_one_right hω, inv_one]
  | succ n ih =>
    rw [pow_succ, commPhase_mul_left hω ((Commute.pow_left hgh n).eq) hgh, ih, pow_succ]

end ScalarCocycle

end TNLean.Algebra
