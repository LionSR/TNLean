/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

/-!
# Operator convexity of `a ↦ a ^ p` for `p ∈ [1, 2]`

For an element `a` of a unital C⋆-algebra, the map `a ↦ a ^ p` is operator
convex (convex for the Löwner order) when `p ∈ [1, 2]`. This complements
Mathlib's `CFC.concaveOn_rpow`, which proves operator concavity for
`p ∈ [0, 1]`, and discharges the TODO recorded in
`Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order`
("Show operator convexity of `rpow` over `Icc 1 2`").

The proof mirrors the concave case. It uses the integral representation of
`x ↦ x ^ p` on `(1, 2)` already in Mathlib
(`CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₁₂`,
Carlen 2010 Lemma 2.8), together with the operator convexity of the
integrand `rpowIntegrand₁₂`, which decomposes into a linear term, a scalar
multiple of the resolvent `x ↦ (t • 1 + x)⁻¹` (operator convex by
`CStarAlgebra.convexOn_ringInverse_algebraMap_add`), and a constant. Operator
convexity is propagated through the Bochner integral by
`integral_convexOn_of_integrand_ae`.

The endpoint `p = 2` is handled separately: `a ^ (2 : ℝ≥0) = a * a`, and
`a ↦ a * a` is operator convex because for `0 ≤ x, y` and a convex
combination with weights `s, r`,
`s • (x*x) + r • (y*y) - (s•x + r•y) * (s•x + r•y) = (s*r) • (x - y) * (x - y)`,
whose right-hand side is positive since `x - y` is self-adjoint.

## Main declarations

* `CFC.convexOn_mul_self` — `a ↦ a * a` is operator convex on `Ici 0`.
* `CFC.convexOn_cfc_rpowIntegrand₁₂` / `CFC.convexOn_cfcₙ_rpowIntegrand₁₂` —
  operator convexity of the `(1, 2)` integrand.
* `CFC.convexOn_nnrpow`, `CFC.convexOn_rpow` — operator convexity of
  `a ↦ a ^ p` for `p ∈ [1, 2]`.

## References

* [Bhatia, *Matrix Analysis*, Chapter V]
* [carlen2010] Eric A. Carlen, "Trace inequalities and quantum entropies: An
  introductory course" (Lemma 2.8)
-/

open Set
open scoped NNReal

namespace CFC

open Real MeasureTheory CStarAlgebra

section UnitalCStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- `a ↦ a * a` is operator convex on the positive elements of a unital
C⋆-algebra. -/
lemma convexOn_mul_self : ConvexOn ℝ (Ici (0 : A)) (fun a : A => a * a) := by
  refine ⟨convex_Ici 0, fun x hx y hy s r hs hr hsr => ?_⟩
  dsimp only
  have e1 : (s • x + r • y) * (s • x + r • y)
      = (s * s) • (x * x) + (s * r) • (x * y) + (r * s) • (y * x)
        + (r * r) • (y * y) := by
    simp only [add_mul, mul_add, smul_mul_smul_comm]
    abel
  have e2 : (x - y) * (x - y) = x * x - x * y - y * x + y * y := by noncomm_ring
  have key : s • (x * x) + r • (y * y) - (s • x + r • y) * (s • x + r • y)
      = (s * r) • ((x - y) * (x - y)) := by
    rw [e1, e2]
    have hr' : r = 1 - s := by linarith
    subst hr'
    match_scalars <;> ring
  have hnn : (0 : A) ≤ (s * r) • ((x - y) * (x - y)) := by
    refine smul_nonneg (mul_nonneg hs hr) ?_
    have hsa : IsSelfAdjoint (x - y) := (hx.isSelfAdjoint).sub (hy.isSelfAdjoint)
    have h := mul_star_self_nonneg (x - y)
    rwa [hsa.star_eq] at h
  rw [← key] at hnn
  exact sub_nonneg.mp hnn

/-- The `(1, 2)` integrand `rpowIntegrand₁₂ p t` is operator convex on the
positive elements of a unital C⋆-algebra, for any `p` and `0 < t`. The convexity
of the integrand does not use `p ∈ (1, 2)`; that constraint is only needed for
the integral representation in `convexOn_nnrpow_Ioo`. -/
lemma convexOn_cfc_rpowIntegrand₁₂ {p t : ℝ} (ht : 0 < t) :
    ConvexOn ℝ (Ici (0 : A)) (cfc (rpowIntegrand₁₂ p t)) := by
  have h₁ : (Ici (0 : A)).EqOn (cfc (rpowIntegrand₁₂ p t))
      (fun x : A => t ^ (p - 2) • x
        + (t ^ p • Ring.inverse (algebraMap ℝ A t + x) - algebraMap ℝ A (t ^ (p - 1)))) := by
    intro x hx
    have hxnn : (0 : A) ≤ x := hx
    have hscalar : rpowIntegrand₁₂ p t
        = fun z => t ^ (p - 2) * z + (t ^ p * (t + z)⁻¹ - t ^ (p - 1)) := by
      funext z
      simp only [rpowIntegrand₁₂]
      have e1 : t ^ (p - 1) * t⁻¹ = t ^ (p - 2) := by
        rw [← Real.rpow_neg_one t, ← Real.rpow_add ht]; congr 1; ring
      have e2 : t ^ (p - 1) * t = t ^ p := by
        nth_rewrite 2 [← Real.rpow_one t]
        rw [← Real.rpow_add ht]; congr 1; ring
      rw [mul_sub, mul_add, mul_one,
        show t ^ (p - 1) * (t⁻¹ * z) = (t ^ (p - 1) * t⁻¹) * z by ring, e1,
        show t ^ (p - 1) * (t * (t + z)⁻¹) = (t ^ (p - 1) * t) * (t + z)⁻¹ by ring, e2]
      ring
    rw [hscalar]
    have hspectrum : ∀ r ∈ spectrum ℝ x, t + r ≠ 0 := by
      intro r hr
      have hr0 : 0 ≤ r := spectrum_nonneg_of_nonneg hxnn hr
      positivity
    have hcont_lin : ContinuousOn (fun z : ℝ => t ^ (p - 2) * z) (spectrum ℝ x) := by
      fun_prop
    have hg : ContinuousOn (fun z : ℝ => (t + z)⁻¹) (spectrum ℝ x) :=
      (continuousOn_const.add continuousOn_id).inv₀ (fun r hr => hspectrum r hr)
    have hcont_inv : ContinuousOn (fun z : ℝ => t ^ p * (t + z)⁻¹ - t ^ (p - 1))
        (spectrum ℝ x) := (continuousOn_const.mul hg).sub continuousOn_const
    rw [cfc_add (a := x) (f := fun z : ℝ => t ^ (p - 2) * z)
        (g := fun z : ℝ => t ^ p * (t + z)⁻¹ - t ^ (p - 1)) (hf := hcont_lin) (hg := hcont_inv)]
    rw [cfc_const_mul (t ^ (p - 2)) (fun z : ℝ => z) x, cfc_id' (R := ℝ) (a := x)]
    rw [cfc_sub (a := x) (f := fun z : ℝ => t ^ p * (t + z)⁻¹) (g := fun z : ℝ => t ^ (p - 1))]
    rw [cfc_const_mul (t ^ p) (fun z : ℝ => (t + z)⁻¹) x]
    rw [cfc_inv (f := fun z : ℝ => t + z) (a := x) hspectrum]
    rw [cfc_const_add t (fun z : ℝ => z) x, cfc_id' (R := ℝ) (a := x)]
    rw [cfc_const (t ^ (p - 1)) x]
  refine ConvexOn.congr ?_ h₁.symm
  refine ConvexOn.add ?_ ?_
  · exact (convexOn_id (convex_Ici 0)).smul (by positivity)
  · refine ConvexOn.sub ?_ (concaveOn_const _ (convex_Ici 0))
    exact ConvexOn.smul (by positivity) (CStarAlgebra.convexOn_ringInverse_algebraMap_add ht)

end UnitalCStarAlgebra

section NonUnitalCStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The non-unital form of `convexOn_cfc_rpowIntegrand₁₂`. -/
lemma convexOn_cfcₙ_rpowIntegrand₁₂ {p t : ℝ} (ht : 0 < t) :
    ConvexOn ℝ (Ici (0 : A)) (cfcₙ (rpowIntegrand₁₂ p t)) := by
  apply convexOn_cfcₙ_of_convexOn_cfc
  refine ConvexOn.subset (convexOn_cfc_rpowIntegrand₁₂ ht) inr_map_Ici_zero ?_
  exact Convex.linear_image (convex_Ici _) (Unitization.inrHom ℝ ℂ A)

/-- This is an intermediate result; use the more general `CFC.convexOn_nnrpow` instead. -/
private lemma convexOn_nnrpow_Ioo {p : ℝ≥0} (hp : p ∈ Ioo 1 2) :
    ConvexOn ℝ (Ici (0 : A)) (fun a : A => a ^ p) := by
  obtain ⟨μ, hμ⟩ := CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₁₂ A hp
  have h₃' : (Ici 0).EqOn (fun a : A => a ^ p)
      (fun a : A => ∫ t in Ioi 0, cfcₙ (rpowIntegrand₁₂ p t) a ∂μ) :=
    fun a ha => (hμ a ha).2
  refine ConvexOn.congr ?_ h₃'.symm
  refine integral_convexOn_of_integrand_ae (convex_Ici _) ?_ fun a ha => (hμ a ha).1
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact convexOn_cfcₙ_rpowIntegrand₁₂ ht

end NonUnitalCStarAlgebra

section UnitalCStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- `a ↦ a ^ p` is operator convex for `p ∈ [1, 2]` (nonnegative real exponent). -/
lemma convexOn_nnrpow {p : ℝ≥0} (hp : p ∈ Icc 1 2) :
    ConvexOn ℝ (Ici (0 : A)) (fun a : A => a ^ p) := by
  obtain ⟨h1, h2⟩ := hp
  rcases eq_or_lt_of_le h1 with rfl | h1'
  · exact ConvexOn.congr (convexOn_id (convex_Ici _)) (fun a ha => (nnrpow_one a ha).symm)
  rcases eq_or_lt_of_le h2 with rfl | h2'
  · exact ConvexOn.congr convexOn_mul_self (fun a ha => (nnrpow_two a ha).symm)
  · exact convexOn_nnrpow_Ioo ⟨h1', h2'⟩

/-- **Operator convexity of `a ↦ a ^ p` for `p ∈ [1, 2]`.**

For an element `a` of a unital C⋆-algebra, the map `a ↦ a ^ p` is convex for
the Löwner order when `1 ≤ p ≤ 2`. This is the convex counterpart of
`CFC.concaveOn_rpow` (which covers `p ∈ [0, 1]`). -/
lemma convexOn_rpow {p : ℝ} (hp : p ∈ Icc 1 2) :
    ConvexOn ℝ (Ici (0 : A)) (fun a : A => a ^ p) := by
  have hp0 : (0 : ℝ) < p := by have := hp.1; linarith
  let q : ℝ≥0 := ⟨p, hp0.le⟩
  have hq0 : 0 < q := by exact_mod_cast hp0
  change ConvexOn ℝ (Ici (0 : A)) (fun a : A => a ^ (q : ℝ))
  simp_rw [← CFC.nnrpow_eq_rpow hq0]
  exact convexOn_nnrpow ⟨by exact_mod_cast hp.1, by exact_mod_cast hp.2⟩

end UnitalCStarAlgebra

end CFC
