/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import TNLean.Algebra.ProjectiveRepresentation

/-!
# Coboundary equivalence and cohomology for scalar 2-cocycles

This file defines coboundary equivalence of multiplicative `ℂˣ`-valued 2-cocycles
and establishes the `H²(G, ℂˣ)` cohomology class as a well-defined quotient.

## Main definitions

* `ScalarCocycle.IsCoboundary` : a cocycle `ω` is a coboundary if
  `ω(g,h) = φ(g) * φ(h) * φ(g*h)⁻¹` for some `φ : G → ℂˣ`
* `ScalarCocycle.CohomologousTo` : two cocycles are cohomologous if their ratio
  is a coboundary
* `ScalarCocycle.IsCocycle` : the multiplicative 2-cocycle condition
* `H2` : the second cohomology quotient `H²(G, ℂˣ)` over genuine cocycles
* `scalarH2Representation` : the trivial representation used for Mathlib's
  low-degree group cohomology
* `ProjectiveRepresentation.cocycle` : the cocycle attached to a projective
  representation
* `ProjectivelyEquivalent` : two projective representations are projectively
  equivalent when their factor systems are cohomologous

## Main results

* `ScalarCocycle.CohomologousTo.equivalence` : cohomologous-to is an equivalence
  relation
* `ScalarCocycle.isCoboundary_iff_cohomologousTo_one` : a cocycle is a coboundary
  iff it is cohomologous to the trivial cocycle
* `ScalarCocycle.isCocycle_iff_isMulCocycle₂` : agreement with Mathlib's
  multiplicative 2-cocycle condition
* `h2EquivGroupCohomology` : equivalence with Mathlib's degree-two group cohomology
* `projRep_equiv_iff_cohomologous` : projective equivalence iff cocycles are
  cohomologous

## References

* Pérez-García et al., *String order and symmetries in quantum spin lattices*,
  arXiv:0802.0447
* Chen, Gu, Wen, *Classification of gapped symmetric phases in one-dimensional
  spin systems*, Phys. Rev. B 83, 035107 (2011)
* Franco-Rubio, Bochniak, Cirac, *Symmetry defects and gauging for quantum states
  with matrix product unitary symmetries*, arXiv:2502.20257, lines 1927--1931
-/

namespace TNLean.Algebra

variable {G : Type*} [Group G]
variable {D : ℕ}

/-- The cocycle attached to a projective representation. -/
abbrev ProjectiveRepresentation.cocycle {ω : ScalarCocycle G}
    (_ρ : ProjectiveRepresentation (D := D) ω) : ScalarCocycle G := ω

/-! ### Coboundary and cohomologous definitions -/

/-- A scalar 2-cocycle `ω` is a coboundary if there exists `φ : G → ℂˣ` such that
`ω(g,h) = φ(g) * φ(h) * φ(g*h)⁻¹` for all `g, h`. -/
def ScalarCocycle.IsCoboundary (ω : ScalarCocycle G) : Prop :=
  ∃ φ : G → Units ℂ, ∀ g h, ω g h = φ g * φ h * (φ (g * h))⁻¹

/-- Two cocycles `ω₁` and `ω₂` are cohomologous if their ratio is a coboundary,
i.e., `ω₁(g,h) = φ(g) * φ(h) * φ(g*h)⁻¹ * ω₂(g,h)` for some `φ : G → ℂˣ`. -/
def ScalarCocycle.CohomologousTo (ω₁ ω₂ : ScalarCocycle G) : Prop :=
  ∃ φ : G → Units ℂ, ∀ g h, ω₁ g h = φ g * φ h * (φ (g * h))⁻¹ * ω₂ g h

/-- A scalar 2-cochain `ω : G → G → ℂˣ` satisfies the multiplicative 2-cocycle condition if
`ω g h * ω (g * h) k = ω g (h * k) * ω h k` for all `g h k : G`. -/
def ScalarCocycle.IsCocycle (ω : ScalarCocycle G) : Prop :=
  ∀ g h k : G, ω g h * ω (g * h) k = ω g (h * k) * ω h k

/-- Every projective representation of positive bond dimension has a genuine 2-cocycle
as factor system.  This is the `Units ℂ`-level lift of
`ProjectiveRepresentation.cocycle_of_assoc`: associativity of matrix multiplication
forces the multiplicative 2-cocycle identity on `ω`. -/
theorem ScalarCocycle.isCocycle_of_projRep
    {ω : ScalarCocycle G} (ρ : ProjectiveRepresentation (D := D) ω) (hD : 0 < D) :
    ScalarCocycle.IsCocycle ω := by
  intro g h k
  have hℂ : (ω g h : ℂ) * (ω (g * h) k : ℂ) = (ω g (h * k) : ℂ) * (ω h k : ℂ) :=
    ρ.cocycle_of_assoc (D := D) hD g h k
  have hUcoe : ((ω g h * ω (g * h) k : Units ℂ) : ℂ) =
      ((ω g (h * k) * ω h k : Units ℂ) : ℂ) := by
    push_cast; exact hℂ
  exact Units.ext hUcoe

/-! ### Equivalence relation -/

namespace ScalarCocycle.CohomologousTo

/-- Cohomologous-to is reflexive: every cocycle is cohomologous to itself. -/
theorem refl (ω : ScalarCocycle G) : CohomologousTo ω ω :=
  ⟨fun _ => 1, fun _ _ => by simp⟩

/-- Cohomologous-to is symmetric. -/
theorem symm {ω₁ ω₂ : ScalarCocycle G} (h : CohomologousTo ω₁ ω₂) :
    CohomologousTo ω₂ ω₁ := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨fun g => (φ g)⁻¹, fun g h => ?_⟩
  simp only [inv_inv]
  rw [hφ g h]
  rw [show (φ g)⁻¹ * (φ h)⁻¹ * (φ (g * h)) * (φ g * φ h * (φ (g * h))⁻¹ * ω₂ g h) =
    ((φ g)⁻¹ * φ g) * ((φ h)⁻¹ * φ h) * (φ (g * h) * (φ (g * h))⁻¹) * ω₂ g h from by
    simp only [mul_assoc, mul_comm, mul_left_comm]]
  simp

/-- Cohomologous-to is transitive. -/
theorem trans {ω₁ ω₂ ω₃ : ScalarCocycle G}
    (h₁₂ : CohomologousTo ω₁ ω₂) (h₂₃ : CohomologousTo ω₂ ω₃) :
    CohomologousTo ω₁ ω₃ := by
  obtain ⟨φ, hφ⟩ := h₁₂
  obtain ⟨ψ, hψ⟩ := h₂₃
  refine ⟨fun g => φ g * ψ g, fun g h => ?_⟩
  rw [hφ g h, hψ g h]
  -- `mul_inv_rev` + AC normalization: valid because `Units ℂ` is commutative
  rw [mul_inv_rev]
  simp only [mul_assoc, mul_comm, mul_left_comm]

/-- Cohomologous-to is an equivalence relation. -/
theorem equivalence : Equivalence (CohomologousTo (G := G)) :=
  ⟨refl, symm, trans⟩

end ScalarCocycle.CohomologousTo

/-- The setoid on scalar cocycles induced by cohomologous-to. -/
scoped instance scalarCocycleSetoid : Setoid (ScalarCocycle G) where
  r := ScalarCocycle.CohomologousTo
  iseqv := ScalarCocycle.CohomologousTo.equivalence

/-- Cohomology setoid restricted to genuine cocycles. -/
instance ScalarCocycle.IsCocycle.instSetoid :
    Setoid {ω : ScalarCocycle G // ScalarCocycle.IsCocycle ω} where
  r ω₁ ω₂ := ScalarCocycle.CohomologousTo ω₁.1 ω₂.1
  iseqv := ⟨
    fun ω => ScalarCocycle.CohomologousTo.refl ω.1,
    fun h => ScalarCocycle.CohomologousTo.symm h,
    fun h₁₂ h₂₃ => ScalarCocycle.CohomologousTo.trans h₁₂ h₂₃⟩

/-- The second cohomology quotient `H²(G, ℂˣ)` modelled by scalar 2-cocycles. -/
def H2 (G : Type*) [Group G] :=
  Quotient (ScalarCocycle.IsCocycle.instSetoid (G := G))

/-- Projective-equivalence at the level of factor-system cohomology classes. -/
def ProjectivelyEquivalent
    {D₁ D₂ : ℕ} {ω₁ ω₂ : ScalarCocycle G}
    (ρ₁ : ProjectiveRepresentation (D := D₁) ω₁)
    (ρ₂ : ProjectiveRepresentation (D := D₂) ω₂) : Prop :=
  ScalarCocycle.CohomologousTo (ρ₁.cocycle) (ρ₂.cocycle)

/-- Two projective representations are projectively equivalent iff their cocycles are
cohomologous. -/
theorem projRep_equiv_iff_cohomologous
    {D₁ D₂ : ℕ} {ω₁ ω₂ : ScalarCocycle G}
    (ρ₁ : ProjectiveRepresentation (D := D₁) ω₁)
    (ρ₂ : ProjectiveRepresentation (D := D₂) ω₂) :
    ProjectivelyEquivalent ρ₁ ρ₂ ↔ ScalarCocycle.CohomologousTo ω₁ ω₂ := by
  rfl

/-- A cocycle is a coboundary iff it is cohomologous to the trivial cocycle `fun _ _ => 1`. -/
lemma ScalarCocycle.isCoboundary_iff_cohomologousTo_one (ω : ScalarCocycle G) :
    ω.IsCoboundary ↔ CohomologousTo ω (fun _ _ => 1) := by
  constructor
  -- Both directions: `mul_one` absorbs or introduces the trivial cocycle `1`
  · rintro ⟨φ, hφ⟩
    exact ⟨φ, fun g h => by rw [hφ g h]; simp [mul_one]⟩
  · rintro ⟨φ, hφ⟩
    exact ⟨φ, fun g h => by rw [hφ g h]; simp [mul_one]⟩

/-! ### Comparison with Mathlib's low-degree group cohomology

The coefficient group in `Papers/2502.20257/main.tex:1927--1931` is
`Units ℂ`, or `ℂˣ`, with the trivial group action.  The declarations below
identify the concrete, curried quotient above with Mathlib's degree-two group
cohomology without introducing another quotient.

Mathlib's low-degree comparison theorems currently place the coefficient ring and
the acting group in the same universe.  Consequently, the comparison is stated
for `G : Type`, while the concrete definition `H2` remains universe-polymorphic.
-/

set_option warn.classDefReducibility false in
/-- The trivial action of `G` on the scalar coefficient group `ℂˣ`.

This action is supplied explicitly to each low-degree group-cohomology
construction rather than selected implicitly. -/
def ScalarCocycle.trivialMulDistribMulAction : MulDistribMulAction G (Units ℂ) where
  smul _ z := z
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

/-- The representation of `G` on `ℂˣ` with trivial action, used to form
Mathlib's degree-two scalar group cohomology. -/
abbrev scalarH2Representation (G : Type*) [Group G] : Rep ℤ G :=
  @Rep.ofMulDistribMulAction G (Units ℂ) _ _
    (ScalarCocycle.trivialMulDistribMulAction (G := G))

/-- TNLean's curried scalar 2-cocycle equation is Mathlib's uncurried
multiplicative 2-cocycle equation for the trivial action on `ℂˣ`.

This fixes the equation orientation in the comparison used for
arXiv:2502.20257, lines 1927--1931. -/
theorem ScalarCocycle.isCocycle_iff_isMulCocycle₂ (ω : ScalarCocycle G) :
    letI := ScalarCocycle.trivialMulDistribMulAction (G := G)
    ω.IsCocycle ↔ groupCohomology.IsMulCocycle₂ (Function.uncurry ω) := by
  constructor
  · intro h g k j
    change ω (g * k) j * ω g k = ω k j * ω g (k * j)
    simpa only [mul_comm] using h g k j
  · intro h g k j
    have h' := h g k j
    change ω (g * k) j * ω g k = ω k j * ω g (k * j) at h'
    simpa only [mul_comm] using h'

/-- TNLean's scalar coboundary equation is Mathlib's multiplicative
2-coboundary equation for the trivial action on `ℂˣ`. -/
theorem ScalarCocycle.isCoboundary_iff_isMulCoboundary₂ (ω : ScalarCocycle G) :
    letI := ScalarCocycle.trivialMulDistribMulAction (G := G)
    ω.IsCoboundary ↔ groupCohomology.IsMulCoboundary₂ (Function.uncurry ω) := by
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨φ, ?_⟩
    intro g h
    change φ h / φ (g * h) * φ g = ω g h
    rw [hφ g h]
    simp only [div_eq_mul_inv, mul_assoc, mul_comm]
  · rintro ⟨φ, hφ⟩
    refine ⟨φ, ?_⟩
    intro g h
    have h' := hφ g h
    change φ h / φ (g * h) * φ g = ω g h at h'
    rw [← h']
    simp only [div_eq_mul_inv, mul_assoc, mul_comm]

/-- Two scalar cocycles are cohomologous precisely when their pointwise ratio
is a coboundary. -/
theorem ScalarCocycle.cohomologousTo_iff_isCoboundary_div
    (ω₁ ω₂ : ScalarCocycle G) :
    ω₁.CohomologousTo ω₂ ↔ (ω₁ / ω₂).IsCoboundary := by
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨φ, ?_⟩
    intro g h
    change ω₁ g h / ω₂ g h = φ g * φ h * (φ (g * h))⁻¹
    rw [hφ g h]
    simp [div_eq_mul_inv, mul_assoc]
  · rintro ⟨φ, hφ⟩
    refine ⟨φ, ?_⟩
    intro g h
    have h' := hφ g h
    change ω₁ g h / ω₂ g h = φ g * φ h * (φ (g * h))⁻¹ at h'
    calc
      ω₁ g h = (ω₁ g h / ω₂ g h) * ω₂ g h := by simp
      _ = φ g * φ h * (φ (g * h))⁻¹ * ω₂ g h := by rw [h']

/-- A curried TNLean cocycle representative, regarded as a Mathlib 2-cocycle
representative for the trivial action on `ℂˣ`. -/
def ScalarCocycle.toMathlibCocycle {G : Type} [Group G]
    (ω : {ω : ScalarCocycle G // ω.IsCocycle}) :
    groupCohomology.cocycles₂ (scalarH2Representation G) := by
  letI := ScalarCocycle.trivialMulDistribMulAction (G := G)
  apply groupCohomology.cocyclesOfIsMulCocycle₂
  exact (ScalarCocycle.isCocycle_iff_isMulCocycle₂ ω).mp ω.property

/-- A Mathlib 2-cocycle representative for the trivial action on `ℂˣ`,
regarded as a curried TNLean cocycle representative. -/
def ScalarCocycle.ofMathlibCocycle {G : Type} [Group G]
    (ω : groupCohomology.cocycles₂ (scalarH2Representation G)) :
    {ω : ScalarCocycle G // ω.IsCocycle} := by
  letI := ScalarCocycle.trivialMulDistribMulAction (G := G)
  refine ⟨fun g h ↦ (ω (g, h)).toMul, ?_⟩
  apply (ScalarCocycle.isCocycle_iff_isMulCocycle₂ _).mpr
  have h := groupCohomology.isMulCocycle₂_of_mem_cocycles₂ (G := G) (M := Units ℂ)
    (fun p ↦ ω p) ω.property
  exact h

/-- Curried TNLean cocycle representatives are equivalent to Mathlib's
uncurried cocycle representatives for the trivial action on `ℂˣ`. -/
def ScalarCocycle.representativesEquivMathlib (G : Type) [Group G] :
    {ω : ScalarCocycle G // ω.IsCocycle} ≃
      groupCohomology.cocycles₂ (scalarH2Representation G) where
  toFun := ScalarCocycle.toMathlibCocycle
  invFun := ScalarCocycle.ofMathlibCocycle
  left_inv ω := by
    ext g h
    rfl
  right_inv ω := by
    apply Subtype.ext
    funext p
    rcases p with ⟨g, h⟩
    rfl

set_option linter.style.haveILetI false in
/-- A scalar cochain is a TNLean coboundary precisely when the corresponding
additive cochain belongs to Mathlib's submodule of 2-coboundaries. -/
theorem ScalarCocycle.isCoboundary_iff_mem_mathlibCoboundaries
    {G : Type} [Group G] (ω : ScalarCocycle G) :
    ω.IsCoboundary ↔
      (fun p : G × G ↦ Additive.ofMul (ω p.1 p.2)) ∈
        groupCohomology.coboundaries₂ (scalarH2Representation G) := by
  letI := ScalarCocycle.trivialMulDistribMulAction (G := G)
  constructor
  · intro h
    exact (groupCohomology.coboundariesOfIsMulCoboundary₂
      ((ScalarCocycle.isCoboundary_iff_isMulCoboundary₂ ω).mp h)).property
  · intro h
    apply (ScalarCocycle.isCoboundary_iff_isMulCoboundary₂ ω).mpr
    have h' := groupCohomology.isMulCoboundary₂_of_mem_coboundaries₂
      (G := G) (M := Units ℂ) (Function.uncurry ω) h
    change groupCohomology.IsMulCoboundary₂ (Function.uncurry ω) at h'
    exact h'

/-- Two TNLean cocycle representatives determine the same Mathlib cohomology
class precisely when they are cohomologous. -/
theorem ScalarCocycle.cohomologousTo_iff_H2π_eq {G : Type} [Group G]
    (ω₁ ω₂ : {ω : ScalarCocycle G // ω.IsCocycle}) :
    ω₁.1.CohomologousTo ω₂.1 ↔
      groupCohomology.H2π (scalarH2Representation G)
          (ScalarCocycle.toMathlibCocycle ω₁) =
        groupCohomology.H2π (scalarH2Representation G)
          (ScalarCocycle.toMathlibCocycle ω₂) := by
  rw [groupCohomology.H2π_eq_iff]
  rw [ScalarCocycle.cohomologousTo_iff_isCoboundary_div]
  rw [ScalarCocycle.isCoboundary_iff_mem_mathlibCoboundaries]
  rfl

/-- The canonical map from TNLean's concrete quotient of scalar cocycles to
Mathlib's degree-two group cohomology for the trivial action on `ℂˣ`. -/
noncomputable def h2ToGroupCohomology (G : Type) [Group G] :
    H2 G → groupCohomology.H2 (scalarH2Representation G) :=
  Quotient.lift
    (fun ω ↦ groupCohomology.H2π (scalarH2Representation G)
      (ScalarCocycle.toMathlibCocycle ω))
    fun ω₁ ω₂ h ↦ (ScalarCocycle.cohomologousTo_iff_H2π_eq ω₁ ω₂).mp h

/-- The canonical comparison map is injective. -/
theorem h2ToGroupCohomology_injective (G : Type) [Group G] :
    Function.Injective (h2ToGroupCohomology G) := by
  intro x y h
  induction x using Quotient.inductionOn with
  | _ ω₁ =>
    induction y using Quotient.inductionOn with
    | _ ω₂ =>
      apply Quotient.sound
      exact (ScalarCocycle.cohomologousTo_iff_H2π_eq ω₁ ω₂).mpr h

/-- The canonical comparison map is surjective. -/
theorem h2ToGroupCohomology_surjective (G : Type) [Group G] :
    Function.Surjective (h2ToGroupCohomology G) := by
  intro x
  refine groupCohomology.H2_induction_on
    (C := fun y ↦ ∃ z, h2ToGroupCohomology G z = y) x ?_
  intro ω
  refine ⟨Quotient.mk _ (ScalarCocycle.ofMathlibCocycle ω), ?_⟩
  change groupCohomology.H2π (scalarH2Representation G)
      ((ScalarCocycle.representativesEquivMathlib G)
        ((ScalarCocycle.representativesEquivMathlib G).symm ω)) =
    groupCohomology.H2π (scalarH2Representation G) ω
  rw [Equiv.apply_symm_apply]

/-- TNLean's concrete quotient `H2 G` is equivalent to Mathlib's degree-two
group cohomology for the trivial action on `ℂˣ`.

This is the cohomology group `H²(G, ℂˣ)` used in arXiv:2502.20257,
lines 1927--1931. -/
noncomputable def h2EquivGroupCohomology (G : Type) [Group G] :
    H2 G ≃ groupCohomology.H2 (scalarH2Representation G) :=
  Equiv.ofBijective (h2ToGroupCohomology G)
    ⟨h2ToGroupCohomology_injective G, h2ToGroupCohomology_surjective G⟩

/-! ### Commutator phase and non-triviality of a cohomology class

For a pair of commuting group elements `g`, `h`, the *commutator phase*
`ω(g,h) · ω(h,g)⁻¹` of an `ℂˣ`-valued 2-cocycle is invariant under the
coboundary action and so descends to the cohomology class.  When the phase
differs from `1` the class is non-trivial.  This is the standard discrete
invariant detecting the non-trivial element of `H²(Z₂ × Z₂, ℂˣ) = Z₂`. -/

/-- The commutator phase `ω(g,h) · ω(h,g)⁻¹` of a scalar 2-cocycle. -/
def ScalarCocycle.commPhase (ω : ScalarCocycle G) (g h : G) : Units ℂ :=
  ω g h * (ω h g)⁻¹

omit [Group G] in
/-- The trivial cocycle has commutator phase `1`. -/
lemma ScalarCocycle.commPhase_one (g h : G) :
    ScalarCocycle.commPhase (G := G) (fun _ _ => (1 : Units ℂ)) g h = 1 := by
  simp [ScalarCocycle.commPhase]

/-- The commutator phase at a commuting pair is invariant under coboundary
equivalence: cohomologous cocycles share the same commutator phase. -/
lemma ScalarCocycle.commPhase_eq_of_cohomologousTo {ω₁ ω₂ : ScalarCocycle G}
    (H : ScalarCocycle.CohomologousTo ω₁ ω₂) {g k : G} (hgk : g * k = k * g) :
    ScalarCocycle.commPhase ω₁ g k = ScalarCocycle.commPhase ω₂ g k := by
  obtain ⟨φ, hφ⟩ := H
  -- Substitute the coboundary formula and use `φ (g*k) = φ (k*g)` (from `hgk`).
  simp only [ScalarCocycle.commPhase, hφ g k, hφ k g, hgk]
  -- `Units ℂ` is a commutative group; coerce to `ℂ`, where units are nonzero, and
  -- let `field_simp` cancel the common `φ`-factors in the ratio.
  apply Units.ext
  push_cast
  field_simp

/-- A scalar 2-cocycle has a non-trivial cohomology class when it is not
cohomologous to the trivial cocycle. -/
def ScalarCocycle.IsNontrivialClass (ω : ScalarCocycle G) : Prop :=
  ¬ ScalarCocycle.CohomologousTo ω (fun _ _ => 1)

/-- A non-trivial commutator phase at a commuting pair forces a non-trivial
cohomology class. -/
theorem ScalarCocycle.isNontrivialClass_of_commPhase_ne_one {ω : ScalarCocycle G}
    {g h : G} (hgh : g * h = h * g) (hne : ScalarCocycle.commPhase ω g h ≠ 1) :
    ScalarCocycle.IsNontrivialClass ω := by
  intro H
  apply hne
  rw [ScalarCocycle.commPhase_eq_of_cohomologousTo H hgh,
    ScalarCocycle.commPhase_one]

end TNLean.Algebra
