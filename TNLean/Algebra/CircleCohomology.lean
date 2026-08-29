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

variable {G : Type*} [Group G]

set_option warn.classDefReducibility false in
/-- The trivial action of `G` on the circle group. -/
def Circle.trivialMulDistribMulAction : MulDistribMulAction G Circle where
  smul _ z := z
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

/-- The representation of `G` on the circle group with trivial action. -/
abbrev circleH2Representation (G : Type*) [Group G] : Rep ℤ G :=
  @Rep.ofMulDistribMulAction G Circle _ _
    (Circle.trivialMulDistribMulAction (G := G))

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
    G → G → Circle :=
  fun g h ↦ Complex.unitsPhase (ω g h)

/-- Include the pointwise unit phase of a scalar two-cochain back into
`ℂˣ`. -/
noncomputable def ScalarCocycle.circlePhaseInclusion (ω : ScalarCocycle G) :
    ScalarCocycle G :=
  fun g h ↦ Circle.toUnits (ω.circlePhase g h)

/-- The positive radial part left after dividing a scalar two-cochain by its
pointwise unit phase, regarded as an L-symbol over one block. -/
noncomputable def ScalarCocycle.positiveResidual (ω : ScalarCocycle G) :
    LSymbol G PUnit.{1} :=
  fun _ g h ↦ ω g h / ω.circlePhaseInclusion g h

/-- Taking pointwise unit phase preserves the scalar cocycle equation. -/
theorem ScalarCocycle.circlePhase_isMulCocycle₂ {ω : ScalarCocycle G}
    (hω : ω.IsCocycle) :
    @groupCohomology.IsMulCocycle₂ G Circle _ _
      (Circle.trivialMulDistribMulAction (G := G)).toSMul
      (Function.uncurry ω.circlePhase) := by
  intro g h k
  change Complex.unitsPhase (ω (g * h) k) * Complex.unitsPhase (ω g h) =
    Complex.unitsPhase (ω h k) * Complex.unitsPhase (ω g (h * k))
  simpa only [map_mul, mul_comm] using congrArg Complex.unitsPhase (hω g h k)

/-- The radial residual of a scalar cocycle is a generalized cocycle on the
one-point block space. -/
theorem ScalarCocycle.positiveResidual_isGeneralizedCocycle
    {ω : ScalarCocycle G} (hω : ω.IsCocycle) :
    LSymbol.IsGeneralizedCocycle ω.positiveResidual := by
  intro x g h k
  change ω.positiveResidual x g (h * k) * ω.positiveResidual x h k =
    1 * ω.positiveResidual (k • x) g h * ω.positiveResidual x (g * h) k
  simp only [one_mul, positiveResidual, circlePhaseInclusion, circlePhase,
    div_mul_div_comm]
  congr 1
  · exact (hω g h k).symm
  · simpa only [map_mul] using (congrArg
      (fun z : Units ℂ ↦ Circle.toUnits (Complex.unitsPhase z)) (hω g h k)).symm

omit [Group G] in
/-- The radial residual of any scalar two-cochain takes values in the positive
subgroup of `ℂˣ`. -/
theorem ScalarCocycle.positiveResidual_isPositiveValued (ω : ScalarCocycle G) :
    LSymbol.IsPositiveValued ω.positiveResidual := by
  intro x g h
  exact ⟨PositiveUnits.norm (ω g h), (Complex.div_toUnits_unitsPhase (ω g h)).symm⟩

/-- For a finite group, the radial residual of a scalar cocycle is a
coboundary.  This is the one-block specialization of the positive generalized
cocycle trivialization. -/
theorem ScalarCocycle.positiveResidual_isCoboundary [Finite G]
    {ω : ScalarCocycle G} (hω : ω.IsCocycle) :
    ScalarCocycle.IsCoboundary
      (fun g h ↦ ω.positiveResidual PUnit.unit g h) := by
  obtain ⟨χ, _, hχ⟩ := LSymbol.exists_positive_coboundary
    (positiveResidual_isGeneralizedCocycle hω)
    (positiveResidual_isPositiveValued ω)
  refine ⟨fun g ↦ χ g PUnit.unit, fun g h ↦ ?_⟩
  have hχApply := congrFun (congrFun (congrFun hχ PUnit.unit) g) h
  simpa [ActionTensorGauge.coboundary, div_eq_mul_inv] using hχApply

/-- Every `ℂˣ`-valued scalar cocycle of a finite group is cohomologous to the
inclusion of its pointwise `U(1)` phase.

This is the finite-discrete algebraic comparison used for
arXiv:2502.20257, line 1931.  It does not use the sheaf-cohomology argument in
the source footnote. -/
theorem ScalarCocycle.cohomologousTo_circlePhaseInclusion [Finite G]
    {ω : ScalarCocycle G} (hω : ω.IsCocycle) :
    ω.CohomologousTo ω.circlePhaseInclusion := by
  rw [ScalarCocycle.cohomologousTo_iff_isCoboundary_div]
  change ScalarCocycle.IsCoboundary
    (fun g h ↦ ω g h / ω.circlePhaseInclusion g h)
  exact positiveResidual_isCoboundary hω

/-- Inclusion of circle coefficients as a morphism of trivial
representations. -/
def circleToComplexUnitsRepHom (G : Type*) [Group G] :
    circleH2Representation G ⟶ scalarH2Representation G := by
  apply Rep.ofHom
  refine ⟨Circle.toUnits.toAdditive.toIntLinearMap, ?_⟩
  intro g
  rfl

/-- Unit phase as a morphism of trivial representations. -/
def complexUnitsPhaseRepHom (G : Type*) [Group G] :
    scalarH2Representation G ⟶ circleH2Representation G := by
  apply Rep.ofHom
  refine ⟨Complex.unitsPhase.toAdditive.toIntLinearMap, ?_⟩
  intro g
  rfl

/-- Unit phase is a left inverse to inclusion at the representation level. -/
theorem circleToComplexUnitsRepHom_comp_complexUnitsPhaseRepHom (G : Type*) [Group G] :
    circleToComplexUnitsRepHom G ≫ complexUnitsPhaseRepHom G =
      𝟙 (circleH2Representation G) := by
  ext z
  exact Complex.unitsPhase_toUnits z

/-! ### Canonical degree-two cohomology -/

/-- The Mathlib circle-valued cocycle obtained by taking the pointwise phase
of a complex-unit-valued cocycle. -/
noncomputable def ScalarCocycle.circlePhaseMathlibCocycle {G : Type} [Group G]
    (ω : groupCohomology.cocycles₂ (scalarH2Representation G)) :
    groupCohomology.cocycles₂ (circleH2Representation G) :=
  groupCohomology.mapCocycles₂ (MonoidHom.id G)
    (complexUnitsPhaseRepHom G) ω

/-- Mapping the phase representative back to complex units gives the
pointwise phase inclusion of the original curried representative. -/
theorem ScalarCocycle.ofMathlibCocycle_map_circlePhaseMathlibCocycle
    {G : Type} [Group G]
    (ω : groupCohomology.cocycles₂ (scalarH2Representation G)) :
    (ScalarCocycle.ofMathlibCocycle
      (groupCohomology.mapCocycles₂ (MonoidHom.id G)
        (circleToComplexUnitsRepHom G)
        (ScalarCocycle.circlePhaseMathlibCocycle ω))).1 =
      (ScalarCocycle.ofMathlibCocycle ω).1.circlePhaseInclusion := by
  rfl

/-- For a finite group, the included pointwise-phase representative and the
original complex-unit-valued representative determine the same canonical
degree-two cohomology class. -/
theorem ScalarCocycle.H2π_map_circlePhaseMathlibCocycle
    {G : Type} [Group G] [Finite G]
    (ω : groupCohomology.cocycles₂ (scalarH2Representation G)) :
    groupCohomology.H2π (scalarH2Representation G)
        (groupCohomology.mapCocycles₂ (MonoidHom.id G)
          (circleToComplexUnitsRepHom G)
          (ScalarCocycle.circlePhaseMathlibCocycle ω)) =
      groupCohomology.H2π (scalarH2Representation G) ω := by
  let ωphase := groupCohomology.mapCocycles₂ (MonoidHom.id G)
    (circleToComplexUnitsRepHom G)
    (ScalarCocycle.circlePhaseMathlibCocycle ω)
  have hcoh :
      (ScalarCocycle.ofMathlibCocycle ωphase).1.CohomologousTo
        (ScalarCocycle.ofMathlibCocycle ω).1 := by
    rw [ofMathlibCocycle_map_circlePhaseMathlibCocycle]
    exact (ScalarCocycle.cohomologousTo_circlePhaseInclusion
      (ScalarCocycle.ofMathlibCocycle ω).2).symm
  exact (ScalarCocycle.cohomologousTo_iff_H2π_eq
    (ScalarCocycle.ofMathlibCocycle ωphase)
    (ScalarCocycle.ofMathlibCocycle ω)).mp hcoh

/-- The coefficient-inclusion map
`H²(G, U(1)) → H²(G, ℂˣ)`. -/
noncomputable def circleH2ToComplexUnitsH2 (G : Type) [Group G] :
    groupCohomology.H2 (circleH2Representation G) ⟶
      groupCohomology.H2 (scalarH2Representation G) :=
  groupCohomology.map (MonoidHom.id G) (circleToComplexUnitsRepHom G) 2

/-- The coefficient phase map
`H²(G, ℂˣ) → H²(G, U(1))`. -/
noncomputable def complexUnitsH2ToCircleH2 (G : Type) [Group G] :
    groupCohomology.H2 (scalarH2Representation G) ⟶
      groupCohomology.H2 (circleH2Representation G) :=
  groupCohomology.map (MonoidHom.id G) (complexUnitsPhaseRepHom G) 2

/-- Taking coefficient phase after coefficient inclusion is the identity on
`H²(G, U(1))`.  No finiteness hypothesis on `G` is needed. -/
theorem complexUnitsH2ToCircleH2_leftInverse (G : Type) [Group G] :
    Function.LeftInverse (complexUnitsH2ToCircleH2 G)
      (circleH2ToComplexUnitsH2 G) := by
  intro x
  change (groupCohomology.map (MonoidHom.id G)
      (circleToComplexUnitsRepHom G) 2 ≫
    groupCohomology.map (MonoidHom.id G)
      (complexUnitsPhaseRepHom G) 2) x = x
  rw [← groupCohomology.map_id_comp,
    circleToComplexUnitsRepHom_comp_complexUnitsPhaseRepHom]
  rw [groupCohomology.map_id]
  rfl

/-- Coefficient inclusion is injective on degree-two group cohomology for any
group. -/
theorem circleH2ToComplexUnitsH2_injective (G : Type) [Group G] :
    Function.Injective (circleH2ToComplexUnitsH2 G) :=
  (complexUnitsH2ToCircleH2_leftInverse G).injective

/-- For a finite group, every `ℂˣ`-valued degree-two cohomology class has the
included pointwise-phase cocycle as a `U(1)`-valued representative. -/
theorem circleH2ToComplexUnitsH2_surjective (G : Type) [Group G] [Finite G] :
    Function.Surjective (circleH2ToComplexUnitsH2 G) := by
  intro x
  refine groupCohomology.H2_induction_on
    (C := fun y ↦ ∃ z, circleH2ToComplexUnitsH2 G z = y) x ?_
  intro ω
  refine ⟨groupCohomology.H2π (circleH2Representation G)
    (ScalarCocycle.circlePhaseMathlibCocycle ω), ?_⟩
  change groupCohomology.map (MonoidHom.id G)
      (circleToComplexUnitsRepHom G) 2
        (groupCohomology.H2π (circleH2Representation G)
          (ScalarCocycle.circlePhaseMathlibCocycle ω)) =
    groupCohomology.H2π (scalarH2Representation G) ω
  rw [groupCohomology.H2π_comp_map_apply]
  exact ScalarCocycle.H2π_map_circlePhaseMathlibCocycle ω

/-- For a finite group with trivial coefficient action, inclusion of the
circle into the nonzero complex numbers induces the algebraic comparison

`H²(G, U(1)) ≃ H²(G, ℂˣ)`.

This proves the finite-discrete algebraic comparison asserted in
arXiv:2502.20257, line 1931.  The source footnote instead discusses sheaf
cohomology with topological coefficient groups; see
`docs/paper-gaps/fbc25_circle_complex_units_cohomology.tex`.

Mathlib's low-degree interface places the acting group and coefficient ring in
the same universe, so this canonical comparison is stated for `G : Type`. -/
noncomputable def circleH2EquivComplexUnitsH2 (G : Type) [Group G] [Finite G] :
    groupCohomology.H2 (circleH2Representation G) ≃ₗ[ℤ]
      groupCohomology.H2 (scalarH2Representation G) :=
  LinearEquiv.ofBijective (circleH2ToComplexUnitsH2 G).hom
    ⟨circleH2ToComplexUnitsH2_injective G,
      circleH2ToComplexUnitsH2_surjective G⟩

end TNLean.Algebra
