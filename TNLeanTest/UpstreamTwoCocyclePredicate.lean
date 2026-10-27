/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CocycleCohomology

/-!
# Regression checks for upstream scalar two-cocycles

These check the source equation, unnormalized constant cocycles, the zero class,
and the different hypotheses required by arbitrary-cochain coboundaries and
cohomology classes. The acting group is arbitrary, not assumed finite or commutative.
-/

open TNLean.Algebra
open scoped TNLean.Algebra.ScalarCohomology

section
variable {G : Type} [Group G]

-- The old source equation and the upstream predicate have exactly the same hypotheses.
example (ω : G × G → ℂˣ) : groupCohomology.IsMulCocycle₂ ω ↔
    ∀ g h k, ω (g, h) * ω (g * h, k) = ω (g, h * k) * ω (h, k) :=
  isMulCocycle₂_iff ω

-- Normalization is not an extra premise: every constant nonzero value is a cocycle.
example (z : ℂˣ) : groupCohomology.IsMulCocycle₂ (fun _ : G × G ↦ z) := by
  apply (isMulCocycle₂_iff _).mpr
  intro g h k
  rfl

-- The unit cocycle has the zero class directly, with no conversion bridge.
example : groupCohomology.H2π (Rep.ofMulDistribMulAction G ℂˣ)
    (groupCohomology.cocyclesOfIsMulCocycle₂
      (show groupCohomology.IsMulCocycle₂ (1 : G × G → ℂˣ) from fun _ _ _ ↦ rfl)) = 0 :=
  ScalarCocycle.H2π_one _

-- The arbitrary-cochain coboundary comparison still takes no cocycle hypotheses.
example (ω η : G × G → ℂˣ) : ScalarCocycle.CohomologousTo ω η ↔
    groupCohomology.IsMulCoboundary₂ (ω / η) :=
  ScalarCocycle.cohomologousTo_iff_isMulCoboundary₂_div ω η

-- Class equality still requires both genuine cocycle hypotheses.
example (ω η : G × G → ℂˣ) (hω : groupCohomology.IsMulCocycle₂ ω)
    (hη : groupCohomology.IsMulCocycle₂ η) :
    ScalarCocycle.CohomologousTo ω η ↔
      groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂ hω) =
      groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂ hη) :=
  ScalarCocycle.cohomologousTo_iff_H2π_eq hω hη
end
