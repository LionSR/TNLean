/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.GeneralizedCocycle
import TNLean.MPS.Symmetry.ProjectivePathInvariance

/-!
# Cohomology along continuous finite-group cocycle paths

Every scalar two-cocycle of a finite group has its regular projective representation.
Its determinant gives a continuous nonzero cochain whose coboundary is the group-order
power of the cocycle. The determinant-root argument therefore proves endpoint class
invariance directly from continuity of the cocycles, without supplied virtual matrices.

This combines the regular determinant construction of arXiv:2502.20257,
`lemma:G_cocycle`, with the path-lifting argument of arXiv:1010.3732, Section II.F.2.
The application to physical paths still requires continuity of their actual cocycles.
-/

open scoped Matrix TNLean.Algebra.ScalarCohomology

namespace TNLean.Algebra

/-- A continuous scalar two-cocycle path on a finite group has cohomologous endpoints.
The regular representation is constructed from the cocycle; no virtual path is assumed.
Source ingredients: arXiv:2502.20257, `lemma:G_cocycle`, and arXiv:1010.3732, Section II.F.2. -/
theorem isMulCoboundary₂_div_of_continuous_cocyclePath
    {G : Type} [Group G] [Finite G]
    (ω : unitInterval → ScalarCocycle G)
    (hω : ∀ t, groupCohomology.IsMulCocycle₂ (ω t))
    (hc : ∀ g h, Continuous fun t ↦ (ω t (g, h) : ℂ)) :
    groupCohomology.IsMulCoboundary₂ (ω 1 / ω 0) := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  let Ω : unitInterval → LSymbol G Unit := fun t _ g h ↦ ω t (g, h)
  have hΩ (t : unitInterval) : LSymbol.IsGeneralizedCocycle (Ω t) := by
    intro x g h k
    simpa only [Ω, one_mul] using ((isMulCocycle₂_iff (ω t)).1 (hω t) g h k).symm
  have hmatrix (g : G) : Continuous fun t ↦ LSymbol.regularMatrix (Ω t) g () := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro k
    by_cases hik : i = g * k
    · simpa only [LSymbol.regularMatrix, hik, ↓reduceIte, Ω] using hc g k
    · simpa only [LSymbol.regularMatrix, hik, ↓reduceIte] using
        (continuous_const : Continuous fun _ : unitInterval ↦ (0 : ℂ))
  apply MPSTensor.projectiveFactor_endpoints_cohomologous_of_det_path (D := Fintype.card G)
    Fintype.card_pos ω (fun t g ↦ LSymbol.regularDeterminant (Ω t) g ()) hc
  · intro g
    exact (hmatrix g).matrix_det
  · intro t g
    exact LSymbol.regularDeterminant_ne_zero (Ω t) g ()
  · intro t g h
    have heq := congrArg Matrix.det (LSymbol.regularMatrix_mul (hΩ t) () g h)
    simpa only [Matrix.det_mul, Matrix.det_smul, LSymbol.regularDeterminant, Ω] using heq

/-- The native degree-two classes at the ends of a continuous finite-group cocycle path
are equal. This concerns cocycles; existence of a continuous cocycle along a physical
Hamiltonian path is not part of the statement. -/
theorem H2π_eq_of_continuous_cocyclePath
    {G : Type} [Group G] [Finite G]
    (ω : unitInterval → ScalarCocycle G)
    (hω : ∀ t, groupCohomology.IsMulCocycle₂ (ω t))
    (hc : ∀ g h, Continuous fun t ↦ (ω t (g, h) : ℂ)) :
    groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂ (hω 1)) =
      groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂ (hω 0)) :=
  (H2π_eq_iff_isMulCoboundary₂_div (hω 1) (hω 0)).2
    (isMulCoboundary₂_div_of_continuous_cocyclePath ω hω hc)

end TNLean.Algebra
