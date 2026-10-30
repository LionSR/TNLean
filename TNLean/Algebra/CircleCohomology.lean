/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import QICLean.Algebra.ComplexPhasePositivity
import TNLean.Algebra.CocycleCohomology
import TNLean.Algebra.PositiveGeneralizedCocycle

/-!
# Circle and complex-unit coefficients in degree-two group cohomology

For a finite group with trivial coefficient action, inclusion of unit-modulus
complex numbers into the nonzero complex numbers induces an equivalence

`H²(G, Circle) ≃ H²(G, Units ℂ)`.

The proof is algebraic.  The unit phase of a nonzero complex number is a
retraction of `Circle.toUnits`, so the induced map is injective for every
group.  For a finite group, the positive norm part of a complex-valued
cocycle is a coboundary by the positive generalized-cocycle theorem.  Dividing
by this coboundary gives a unit-modulus representative.

This differs from the explanation in arXiv:2502.20257, line 1931 and its
footnote.  There the coefficient spaces are treated as topological abelian
groups and compared in sheaf cohomology over a CW complex.  Here `G` is a
finite discrete group, the cohomology is algebraic group cohomology, and the
comparison is proved directly from cocycles.  See
`docs/paper-gaps/fbc25_circle_complex_units_cohomology.tex`.
-/

noncomputable section

open CategoryTheory

namespace TNLean.Algebra

open scoped ScalarCohomology

variable {G : Type} [Group G]

/-- Taking the unit phase retracts the inclusion of the circle into the
nonzero complex numbers. -/
@[simp]
theorem Complex.unitsPhase_toUnits (z : Circle) :
    Complex.unitsPhase (Circle.toUnits z) = z := by
  apply Circle.ext
  change (z : ℂ) / ‖(z : ℂ)‖ = (z : ℂ)
  rw [Circle.norm_coe]
  change (z : ℂ) / (1 : ℂ) = (z : ℂ)
  exact div_one _

/-- Polar decomposition of a nonzero complex number, expressed in the unit
group: the quotient by its unit phase is its positive norm. -/
theorem Complex.div_toUnits_unitsPhase (z : Units ℂ) :
    z / Circle.toUnits (Complex.unitsPhase z) =
      PositiveUnits.embedding (PositiveUnits.norm z) := by
  apply Units.ext
  change (z : ℂ) / ((z : ℂ) / ‖(z : ℂ)‖) = ((‖(z : ℂ)‖ : ℝ) : ℂ)
  field_simp

/-! ### Cocycle representatives -/

/-- The pointwise unit phase of a complex-unit-valued scalar two-cochain. -/
noncomputable def ScalarCocycle.circlePhase (ω : ScalarCocycle G) :
    G × G → Circle :=
  fun p ↦ Complex.unitsPhase (ω p)

/-- Include the pointwise unit phase of a scalar two-cochain back into
`ℂˣ`. -/
noncomputable def ScalarCocycle.circlePhaseInclusion (ω : ScalarCocycle G) :
    ScalarCocycle G :=
  fun p ↦ Circle.toUnits (ω.circlePhase p)

/-- The positive radial part left after dividing a scalar two-cochain by its
pointwise unit phase, regarded as an L-symbol over one block. -/
noncomputable def ScalarCocycle.positiveResidual (ω : ScalarCocycle G) :
    LSymbol G PUnit.{1} :=
  fun _ g h ↦ ω (g, h) / ω.circlePhaseInclusion (g, h)

/-- Taking pointwise unit phase preserves the scalar cocycle equation. -/
theorem ScalarCocycle.circlePhase_isMulCocycle₂ {ω : ScalarCocycle G}
    (hω : groupCohomology.IsMulCocycle₂ ω) :
    groupCohomology.IsMulCocycle₂ ω.circlePhase := by
  intro g h k
  change Complex.unitsPhase (ω (g * h, k)) * Complex.unitsPhase (ω (g, h)) =
    Complex.unitsPhase (ω (h, k)) * Complex.unitsPhase (ω (g, h * k))
  simpa only [map_mul, mul_comm] using
    congrArg Complex.unitsPhase ((isMulCocycle₂_iff _).mp hω g h k)

/-- Including the pointwise unit phase preserves the scalar cocycle equation. -/
theorem ScalarCocycle.circlePhaseInclusion_isMulCocycle₂ {ω : ScalarCocycle G}
    (hω : groupCohomology.IsMulCocycle₂ ω) :
    groupCohomology.IsMulCocycle₂ ω.circlePhaseInclusion := by
  apply (isMulCocycle₂_iff _).mpr
  intro g h k
  simpa only [circlePhaseInclusion, circlePhase, map_mul] using
    congrArg (fun z : ℂˣ ↦ Circle.toUnits (Complex.unitsPhase z))
      ((isMulCocycle₂_iff _).mp hω g h k)

/-- The radial residual of a scalar cocycle is a generalized cocycle on the
one-point block space. -/
theorem ScalarCocycle.positiveResidual_isGeneralizedCocycle
    {ω : ScalarCocycle G} (hω : groupCohomology.IsMulCocycle₂ ω) :
    LSymbol.IsGeneralizedCocycle ω.positiveResidual := by
  intro x g h k
  change ω.positiveResidual x g (h * k) * ω.positiveResidual x h k =
    1 * ω.positiveResidual (k • x) g h * ω.positiveResidual x (g * h) k
  simp only [one_mul, positiveResidual, circlePhaseInclusion, circlePhase,
    div_mul_div_comm]
  congr 1
  · exact ((isMulCocycle₂_iff _).mp hω g h k).symm
  · simpa only [map_mul] using (congrArg
      (fun z : Units ℂ ↦ Circle.toUnits (Complex.unitsPhase z))
      ((isMulCocycle₂_iff _).mp hω g h k)).symm

omit [Group G] in
/-- The radial residual of any scalar two-cochain takes values in the positive
subgroup of `ℂˣ`. -/
theorem ScalarCocycle.positiveResidual_isPositiveValued (ω : ScalarCocycle G) :
    LSymbol.IsPositiveValued ω.positiveResidual := by
  intro x g h
  exact ⟨PositiveUnits.norm (ω (g, h)), (Complex.div_toUnits_unitsPhase (ω (g, h))).symm⟩

/-- Every `ℂˣ`-valued scalar cocycle of a finite group has the same `H²` class as
the inclusion of its pointwise `U(1)` phase.

The radial residual is a coboundary, by the one-block specialization of the positive
generalized cocycle trivialization.

This is the finite-discrete algebraic comparison used for
arXiv:2502.20257, line 1931.  It does not use the sheaf-cohomology argument in
the source footnote. -/
theorem ScalarCocycle.H2π_circlePhaseInclusion [Finite G]
    {ω : ScalarCocycle G} (hω : groupCohomology.IsMulCocycle₂ ω) :
    groupCohomology.H2π (Rep.ofMulDistribMulAction G ℂˣ)
        (groupCohomology.cocyclesOfIsMulCocycle₂ hω) =
      groupCohomology.H2π (Rep.ofMulDistribMulAction G ℂˣ)
        (groupCohomology.cocyclesOfIsMulCocycle₂ (circlePhaseInclusion_isMulCocycle₂ hω)) := by
  apply (H2π_eq_iff_isMulCoboundary₂_div hω (circlePhaseInclusion_isMulCocycle₂ hω)).mpr
  apply (isMulCoboundary₂_div_iff ω ω.circlePhaseInclusion).mpr
  obtain ⟨χ, _, hχ⟩ := LSymbol.exists_positive_coboundary
    (positiveResidual_isGeneralizedCocycle hω)
    (positiveResidual_isPositiveValued ω)
  refine ⟨fun g ↦ χ g PUnit.unit, fun g h ↦ ?_⟩
  have hχApply := congrFun (congrFun (congrFun hχ PUnit.unit) g) h
  change ω (g, h) / ω.circlePhaseInclusion (g, h) =
    χ g PUnit.unit * χ h PUnit.unit / χ (g * h) PUnit.unit at hχApply
  rw [div_eq_iff_eq_mul] at hχApply
  rw [hχApply, div_eq_mul_inv]

/-- Inclusion of circle coefficients as a morphism of trivial
representations. -/
def circleToComplexUnitsRepHom (G : Type) [Group G] :
    Rep.ofMulDistribMulAction G Circle ⟶ Rep.ofMulDistribMulAction G ℂˣ := by
  apply Rep.ofHom
  refine ⟨Circle.toUnits.toAdditive.toIntLinearMap, ?_⟩
  intro g
  rfl

/-- Unit phase as a morphism of trivial representations. -/
def complexUnitsPhaseRepHom (G : Type) [Group G] :
    Rep.ofMulDistribMulAction G ℂˣ ⟶ Rep.ofMulDistribMulAction G Circle := by
  apply Rep.ofHom
  refine ⟨Complex.unitsPhase.toAdditive.toIntLinearMap, ?_⟩
  intro g
  rfl

/-- Unit phase is a left inverse to inclusion at the representation level. -/
theorem circleToComplexUnitsRepHom_comp_complexUnitsPhaseRepHom (G : Type) [Group G] :
    circleToComplexUnitsRepHom G ≫ complexUnitsPhaseRepHom G =
      𝟙 (Rep.ofMulDistribMulAction G Circle) := by
  ext z
  exact Complex.unitsPhase_toUnits z

/-! ### Canonical degree-two cohomology -/

/-- The Mathlib circle-valued cocycle obtained by taking the pointwise phase
of a complex-unit-valued cocycle. -/
noncomputable def ScalarCocycle.circlePhaseMathlibCocycle {G : Type} [Group G]
    (ω : groupCohomology.cocycles₂ (Rep.ofMulDistribMulAction G ℂˣ)) :
    groupCohomology.cocycles₂ (Rep.ofMulDistribMulAction G Circle) :=
  groupCohomology.mapCocycles₂ (MonoidHom.id G)
    (complexUnitsPhaseRepHom G) ω

/-- For a finite group, the included pointwise-phase representative of a scalar cocycle `ω`
and `ω` itself determine the same class in `H²(G, ℂˣ)`. -/
theorem ScalarCocycle.H2π_map_circlePhaseMathlibCocycle
    {G : Type} [Group G] [Finite G] {ω : ScalarCocycle G}
    (hω : groupCohomology.IsMulCocycle₂ ω) :
    groupCohomology.H2π (Rep.ofMulDistribMulAction G ℂˣ)
        (groupCohomology.mapCocycles₂ (MonoidHom.id G)
          (circleToComplexUnitsRepHom G)
          (ScalarCocycle.circlePhaseMathlibCocycle
            (groupCohomology.cocyclesOfIsMulCocycle₂ hω))) =
      groupCohomology.H2π (Rep.ofMulDistribMulAction G ℂˣ)
        (groupCohomology.cocyclesOfIsMulCocycle₂ hω) := by
  exact (ScalarCocycle.H2π_circlePhaseInclusion hω).symm

/-- Taking coefficient phase after coefficient inclusion is the identity on
`H²(G, U(1))`.  No finiteness hypothesis on `G` is needed. -/
theorem complexUnitsPhase_map_leftInverse (G : Type) [Group G] :
    Function.LeftInverse (groupCohomology.map (A := Rep.ofMulDistribMulAction G ℂˣ)
        (B := Rep.ofMulDistribMulAction G Circle) (MonoidHom.id G)
        (complexUnitsPhaseRepHom G) 2)
      (groupCohomology.map (A := Rep.ofMulDistribMulAction G Circle)
        (B := Rep.ofMulDistribMulAction G ℂˣ) (MonoidHom.id G)
        (circleToComplexUnitsRepHom G) 2) := by
  intro x
  change (groupCohomology.map (A := Rep.ofMulDistribMulAction G Circle)
        (B := Rep.ofMulDistribMulAction G ℂˣ) (MonoidHom.id G)
        (circleToComplexUnitsRepHom G) 2 ≫
    groupCohomology.map (A := Rep.ofMulDistribMulAction G ℂˣ)
        (B := Rep.ofMulDistribMulAction G Circle) (MonoidHom.id G)
        (complexUnitsPhaseRepHom G) 2) x = x
  rw [← groupCohomology.map_id_comp,
    circleToComplexUnitsRepHom_comp_complexUnitsPhaseRepHom]
  rw [groupCohomology.map_id]
  rfl

/-- Coefficient inclusion is injective on degree-two group cohomology for any
group. -/
theorem circleToComplexUnits_map_injective (G : Type) [Group G] :
    Function.Injective (groupCohomology.map (A := Rep.ofMulDistribMulAction G Circle)
        (B := Rep.ofMulDistribMulAction G ℂˣ) (MonoidHom.id G)
        (circleToComplexUnitsRepHom G) 2) :=
  (complexUnitsPhase_map_leftInverse G).injective

/-- For a finite group, every `ℂˣ`-valued degree-two cohomology class has the
included pointwise-phase cocycle as a `U(1)`-valued representative. -/
theorem circleToComplexUnits_map_surjective (G : Type) [Group G] [Finite G] :
    Function.Surjective
      (groupCohomology.map (A := Rep.ofMulDistribMulAction G Circle)
        (B := Rep.ofMulDistribMulAction G ℂˣ) (MonoidHom.id G)
        (circleToComplexUnitsRepHom G) 2) := by
  intro x
  obtain ⟨ω, hω, rfl⟩ := ScalarCocycle.exists_H2π_eq x
  refine ⟨groupCohomology.H2π (Rep.ofMulDistribMulAction G Circle)
    (ScalarCocycle.circlePhaseMathlibCocycle
      (groupCohomology.cocyclesOfIsMulCocycle₂ hω)), ?_⟩
  rw [groupCohomology.H2π_comp_map_apply]
  exact ScalarCocycle.H2π_map_circlePhaseMathlibCocycle hω

/-- For a finite group with trivial coefficient action, Mathlib's cohomology
map induced by circle inclusion is bijective in degree two.

This is the finite-discrete algebraic comparison asserted in
arXiv:2502.20257, line 1931. The source footnote instead discusses sheaf
cohomology with topological coefficient groups; see
`docs/paper-gaps/fbc25_circle_complex_units_cohomology.tex`.

Mathlib's low-degree interface places the acting group and coefficient ring in
the same universe, so the comparison is stated for `G : Type`. -/
theorem circleToComplexUnits_map_bijective (G : Type) [Group G] [Finite G] :
    Function.Bijective
      (groupCohomology.map (A := Rep.ofMulDistribMulAction G Circle)
        (B := Rep.ofMulDistribMulAction G ℂˣ) (MonoidHom.id G)
        (circleToComplexUnitsRepHom G) 2) :=
  ⟨circleToComplexUnits_map_injective G, circleToComplexUnits_map_surjective G⟩

end TNLean.Algebra
