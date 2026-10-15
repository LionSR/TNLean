/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import TNLean.Algebra.ProjectiveRepresentation

/-!
# Scalar 2-cocycles and Mathlib's `H²(G, ℂˣ)`

The factor system `ω : G → G → ℂˣ` of a projective representation satisfies the
multiplicative 2-cocycle equation.  Its class lives in Mathlib's degree-two group
cohomology `groupCohomology.H2 (Rep.ofMulDistribMulAction G ℂˣ)`, for the trivial
action of `G` on `ℂˣ`; the class of a cocycle `ω` is
`groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂ hω.isMulCocycle₂)`.

The trivial action is the scoped instance
`TNLean.Algebra.ScalarCohomology.trivialMulDistribMulAction`; Mathlib defines no
action of an arbitrary group on `ℂˣ`.  Open it with
`open scoped TNLean.Algebra.ScalarCohomology`.

## Main definitions

* `ScalarCocycle.IsCocycle` : the multiplicative 2-cocycle condition
* `ScalarCocycle.CohomologousTo` : two cochains are cohomologous if their ratio
  is a coboundary
* `ScalarCohomology.trivialMulDistribMulAction` : the trivial action of `G` on `ℂˣ`
* `scalarRepresentationRes` : restriction of the trivial representation on `ℂˣ`
  along a group homomorphism, the coefficient map of Mathlib's restriction
* `ScalarCocycle.commPhase` : the commutator phase `ω(g,h) ω(h,g)⁻¹`

## Main results

* `ScalarCocycle.isCocycle_iff_isMulCocycle₂` : agreement with Mathlib's
  multiplicative 2-cocycle condition
* `ScalarCocycle.cohomologousTo_iff_H2π_eq` : two cocycles are cohomologous iff
  they have the same class in Mathlib's `H²(G, ℂˣ)`
* `ScalarCocycle.exists_H2π_eq` : every class of `H²(G, ℂˣ)` is the class of a
  scalar cocycle
* `ScalarCocycle.H2π_ne_zero_of_commPhase_ne_one` : a non-trivial commutator phase
  of a cocycle at a commuting pair forces a non-zero class in `H²(G, ℂˣ)`

## References

* Pérez-García et al., *String order and symmetries in quantum spin lattices*,
  arXiv:0802.0447
* Chen, Gu, Wen, *Classification of gapped symmetric phases in one-dimensional
  spin systems*, Phys. Rev. B 83, 035107 (2011)
* Franco-Rubio, Bochniak, Cirac, *Symmetry defects and gauging for quantum states
  with matrix product unitary symmetries*, arXiv:2502.20257, lines 1927--1931
-/

namespace TNLean.Algebra

variable {G : Type} [Group G]
variable {D : ℕ}

/-! ### Cocycles and cohomologous cochains -/

/-- Two cocycles `ω₁` and `ω₂` are cohomologous if their ratio is a coboundary,
i.e., `ω₁(g,h) = φ(g) * φ(h) * φ(g*h)⁻¹ * ω₂(g,h)` for some `φ : G → ℂˣ`. -/
def ScalarCocycle.CohomologousTo (ω₁ ω₂ : ScalarCocycle G) : Prop :=
  ∃ φ : G → Units ℂ, ∀ g h, ω₁ g h = φ g * φ h * (φ (g * h))⁻¹ * ω₂ g h

/-- A scalar 2-cochain `ω : G → G → ℂˣ` satisfies the multiplicative 2-cocycle condition if
`ω g h * ω (g * h) k = ω g (h * k) * ω h k` for all `g h k : G`. -/
def ScalarCocycle.IsCocycle (ω : ScalarCocycle G) : Prop :=
  ∀ g h k : G, ω g h * ω (g * h) k = ω g (h * k) * ω h k

/-- A scalar cochain cohomologous to a genuine cocycle satisfies the cocycle equation. -/
theorem ScalarCocycle.IsCocycle.of_cohomologousTo {ω₁ ω₂ : ScalarCocycle G}
    (hω₂ : ω₂.IsCocycle) (h : ω₁.CohomologousTo ω₂) : ω₁.IsCocycle := by
  obtain ⟨φ, hφ⟩ := h
  intro a b c
  simp only [hφ]
  calc
    _ = (φ a * φ b * φ c * (φ (a * (b * c)))⁻¹) *
        (ω₂ a b * ω₂ (a * b) c) := by simp [mul_assoc, mul_comm, mul_left_comm]
    _ = (φ a * φ b * φ c * (φ (a * (b * c)))⁻¹) *
        (ω₂ a (b * c) * ω₂ b c) := by rw [hω₂ a b c]
    _ = _ := by simp [mul_assoc, mul_comm, mul_left_comm]

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

/-! ### Mathlib's degree-two group cohomology with coefficients `ℂˣ`

The coefficient group in `Papers/2502.20257/main.tex:1927--1931` is `ℂˣ` with the
trivial group action.  Mathlib's low-degree comparison theorems place the
coefficient ring and the acting group in the same universe, so the cocycle-bearing
modules use `G : Type` throughout. -/

namespace ScalarCohomology

set_option warn.classDefReducibility false in
/-- The trivial action of `G` on the scalar coefficient group `ℂˣ`, so that
`Rep.ofMulDistribMulAction G ℂˣ` is the coefficient module of `H²(G, ℂˣ)` and
`H³(G, ℂˣ)`.  It is scoped: other actions of particular groups on `ℂˣ` exist. -/
scoped instance trivialMulDistribMulAction : MulDistribMulAction G (Units ℂ) where
  smul _ z := z
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

/-- The group acts trivially on the scalar coefficient module. -/
theorem ofMulDistribMulAction_ρ_apply (a : G) (x : Rep.ofMulDistribMulAction G ℂˣ) :
    (Rep.ofMulDistribMulAction G ℂˣ).ρ a x = x :=
  rfl

end ScalarCohomology

open scoped ScalarCohomology

/-- Restricting the trivial representation on `ℂˣ` along `f : K →* G` gives the trivial
representation of `K`; this is the identity on `Additive ℂˣ` as a representation morphism, the
coefficient map for Mathlib's restriction `groupCohomology.cochainsMap f` and
`groupCohomology.map f`. -/
def scalarRepresentationRes {K : Type} [Group K] (f : K →* G) :
    Rep.res f (Rep.ofMulDistribMulAction G ℂˣ) ⟶
      Rep.ofMulDistribMulAction K ℂˣ := by
  apply Rep.ofHom
  refine ⟨LinearMap.id, ?_⟩
  intro g
  rfl

/-- The curried scalar 2-cocycle equation is Mathlib's uncurried multiplicative
2-cocycle equation for the trivial action on `ℂˣ`.

This fixes the equation orientation in the comparison used for
arXiv:2502.20257, lines 1927--1931. -/
theorem ScalarCocycle.isCocycle_iff_isMulCocycle₂ (ω : ScalarCocycle G) :
    ω.IsCocycle ↔ groupCohomology.IsMulCocycle₂ (Function.uncurry ω) := by
  constructor
  · intro h g k j
    change ω (g * k) j * ω g k = ω k j * ω g (k * j)
    simpa only [mul_comm] using h g k j
  · intro h g k j
    have h' := h g k j
    change ω (g * k) j * ω g k = ω k j * ω g (k * j) at h'
    simpa only [mul_comm] using h'

/-- A scalar cocycle is a Mathlib multiplicative 2-cocycle for the trivial action. -/
theorem ScalarCocycle.IsCocycle.isMulCocycle₂ {ω : ScalarCocycle G} (hω : ω.IsCocycle) :
    groupCohomology.IsMulCocycle₂ (Function.uncurry ω) :=
  (ScalarCocycle.isCocycle_iff_isMulCocycle₂ ω).mp hω

/-- Two scalar cochains are cohomologous precisely when their pointwise ratio is a
Mathlib multiplicative 2-coboundary for the trivial action on `ℂˣ`. -/
theorem ScalarCocycle.cohomologousTo_iff_isMulCoboundary₂_div (ω₁ ω₂ : ScalarCocycle G) :
    ω₁.CohomologousTo ω₂ ↔ groupCohomology.IsMulCoboundary₂ (Function.uncurry (ω₁ / ω₂)) := by
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨φ, fun g h ↦ ?_⟩
    change φ h / φ (g * h) * φ g = ω₁ g h / ω₂ g h
    rw [hφ g h, mul_div_cancel_right, div_mul_eq_mul_div, mul_comm (φ h), div_eq_mul_inv]
  · rintro ⟨φ, hφ⟩
    refine ⟨φ, fun g h ↦ ?_⟩
    have h' := hφ g h
    change φ h / φ (g * h) * φ g = ω₁ g h / ω₂ g h at h'
    rw [eq_div_iff_mul_eq'] at h'
    rw [← h', div_mul_eq_mul_div, mul_comm (φ h), div_eq_mul_inv]

/-- Two scalar cocycles are cohomologous precisely when they have the same class in
Mathlib's `H²(G, ℂˣ)`, by `groupCohomology.H2π_eq_iff`. -/
theorem ScalarCocycle.cohomologousTo_iff_H2π_eq {ω₁ ω₂ : ScalarCocycle G}
    (h₁ : ω₁.IsCocycle) (h₂ : ω₂.IsCocycle) :
    ω₁.CohomologousTo ω₂ ↔
      groupCohomology.H2π (Rep.ofMulDistribMulAction G ℂˣ)
          (groupCohomology.cocyclesOfIsMulCocycle₂ h₁.isMulCocycle₂) =
        groupCohomology.H2π (Rep.ofMulDistribMulAction G ℂˣ)
          (groupCohomology.cocyclesOfIsMulCocycle₂ h₂.isMulCocycle₂) := by
  rw [groupCohomology.H2π_eq_iff, ScalarCocycle.cohomologousTo_iff_isMulCoboundary₂_div]
  constructor
  · intro h
    exact (groupCohomology.coboundariesOfIsMulCoboundary₂ h).property
  · intro h
    exact groupCohomology.isMulCoboundary₂_of_mem_coboundaries₂ (G := G) (M := Units ℂ) _ h

/-- The class of the constant cocycle `1` is zero. -/
theorem ScalarCocycle.H2π_one
    (h : ScalarCocycle.IsCocycle (fun _ _ ↦ (1 : Units ℂ) : ScalarCocycle G)) :
    groupCohomology.H2π (Rep.ofMulDistribMulAction G ℂˣ)
      (groupCohomology.cocyclesOfIsMulCocycle₂ h.isMulCocycle₂) = 0 := by
  have : groupCohomology.cocyclesOfIsMulCocycle₂ h.isMulCocycle₂ = 0 := rfl
  rw [this, map_zero]

/-- A scalar cocycle is cohomologous to the constant cocycle `1` precisely when its
class in Mathlib's `H²(G, ℂˣ)` is zero. -/
theorem ScalarCocycle.cohomologousTo_one_iff_H2π_eq_zero {ω : ScalarCocycle G}
    (hω : ω.IsCocycle) :
    ω.CohomologousTo (fun _ _ ↦ 1) ↔
      groupCohomology.H2π (Rep.ofMulDistribMulAction G ℂˣ)
        (groupCohomology.cocyclesOfIsMulCocycle₂ hω.isMulCocycle₂) = 0 := by
  have h1 : ScalarCocycle.IsCocycle (fun _ _ ↦ (1 : Units ℂ) : ScalarCocycle G) :=
    fun _ _ _ ↦ rfl
  rw [ScalarCocycle.cohomologousTo_iff_H2π_eq hω h1, ScalarCocycle.H2π_one h1]

/-- Every class of Mathlib's `H²(G, ℂˣ)`, for the trivial action, is the class of a
scalar cocycle. -/
theorem ScalarCocycle.exists_H2π_eq
    (x : groupCohomology.H2 (Rep.ofMulDistribMulAction G ℂˣ)) :
    ∃ (ω : ScalarCocycle G) (hω : ω.IsCocycle),
      groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂ hω.isMulCocycle₂) = x := by
  induction x using groupCohomology.H2_induction_on with
  | h α =>
    refine ⟨fun g h ↦ Additive.toMul (α (g, h)),
      (ScalarCocycle.isCocycle_iff_isMulCocycle₂ _).mpr
        (groupCohomology.isMulCocycle₂_of_mem_cocycles₂ (G := G) (M := Units ℂ)
          (fun p ↦ α p) α.property), ?_⟩
    rfl

/-! ### Commutator phase and non-triviality of a cohomology class

For a pair of commuting group elements `g`, `h`, the *commutator phase*
`ω(g,h) · ω(h,g)⁻¹` of an `ℂˣ`-valued 2-cocycle is invariant under the
coboundary action and so descends to the cohomology class.  When the phase
differs from `1` the class is non-zero.  This is the standard discrete
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

/-- A non-trivial commutator phase at a commuting pair forces a non-zero class in
Mathlib's `H²(G, ℂˣ)`. -/
theorem ScalarCocycle.H2π_ne_zero_of_commPhase_ne_one {ω : ScalarCocycle G}
    (hω : ω.IsCocycle) {g h : G} (hgh : g * h = h * g)
    (hne : ScalarCocycle.commPhase ω g h ≠ 1) :
    groupCohomology.H2π (Rep.ofMulDistribMulAction G ℂˣ)
      (groupCohomology.cocyclesOfIsMulCocycle₂ hω.isMulCocycle₂) ≠ 0 := by
  intro H
  apply hne
  rw [ScalarCocycle.commPhase_eq_of_cohomologousTo
    ((ScalarCocycle.cohomologousTo_one_iff_H2π_eq_zero hω).mpr H) hgh,
    ScalarCocycle.commPhase_one]

end TNLean.Algebra
