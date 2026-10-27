/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CocycleCohomology

/-!
# Arbitrary scalar cochains modulo Mathlib coboundaries

The quotient comparisons below have no cocycle or normalization premise.
In particular, a two-cochain that is not a cocycle still has a quotient class;
this quotient is not degree-two group cohomology.
-/

open TNLean.Algebra
open scoped TNLean.Algebra.ScalarCohomology

section
variable {G : Type} [Group G]

-- The numerator is the first representative, matching the additive difference.
example (ω η : G × G → ℂˣ) :
    groupCohomology.IsMulCoboundary₂ (ω / η) ↔
      (Submodule.Quotient.mk ((@Additive.ofMul ℂˣ) ∘ ω) :
        (G × G → Rep.ofMulDistribMulAction G ℂˣ) ⧸
          groupCohomology.coboundaries₂ (Rep.ofMulDistribMulAction G ℂˣ)) =
        Submodule.Quotient.mk ((@Additive.ofMul ℂˣ) ∘ η) :=
  isMulCoboundary₂_div_iff_quotient_mk_eq ω η

example (ω : G × G → ℂˣ) : groupCohomology.IsMulCoboundary₂ (ω / ω) :=
  (isMulCoboundary₂_div_iff_quotient_mk_eq ω ω).mpr rfl

example (ω η : G × G → ℂˣ) (h : groupCohomology.IsMulCoboundary₂ (ω / η)) :
    groupCohomology.IsMulCoboundary₂ (η / ω) :=
  (isMulCoboundary₂_div_iff_quotient_mk_eq η ω).mpr
    ((isMulCoboundary₂_div_iff_quotient_mk_eq ω η).mp h).symm

example (ω η ζ : G × G → ℂˣ)
    (hωη : groupCohomology.IsMulCoboundary₂ (ω / η))
    (hηζ : groupCohomology.IsMulCoboundary₂ (η / ζ)) :
    groupCohomology.IsMulCoboundary₂ (ω / ζ) :=
  (isMulCoboundary₂_div_iff_quotient_mk_eq ω ζ).mpr
    (((isMulCoboundary₂_div_iff_quotient_mk_eq ω η).mp hωη).trans
      ((isMulCoboundary₂_div_iff_quotient_mk_eq η ζ).mp hηζ))
end

private def nonCocycle : Multiplicative ℤ × Multiplicative ℤ → ℂˣ :=
  fun p ↦ if p.1 = 1 then 1 else -1

-- A cochain depending nontrivially on only the first coordinate is not a cocycle.
example : ¬ groupCohomology.IsMulCocycle₂ nonCocycle := by
  intro h
  have h' := (isMulCocycle₂_iff _).mp h (Multiplicative.ofAdd 1) 1 1
  have hval := congrArg Units.val h'
  norm_num [nonCocycle] at hval

-- Nevertheless its class modulo two-coboundaries is well-defined.
example : groupCohomology.IsMulCoboundary₂ (nonCocycle / nonCocycle) :=
  (isMulCoboundary₂_div_iff_quotient_mk_eq nonCocycle nonCocycle).mpr rfl
