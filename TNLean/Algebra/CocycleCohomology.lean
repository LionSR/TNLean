/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Algebra.ProjectiveRepresentation

/-!
# Coboundary equivalence and cohomology for scalar 2-cocycles

This file defines coboundary equivalence of multiplicative `U(1)`-valued 2-cocycles
and establishes the `H²(G, U(1))` cohomology class as a well-defined quotient.

## Main definitions

* `ScalarCocycle.IsCoboundary` : a cocycle `ω` is a coboundary if
  `ω(g,h) = φ(g) * φ(h) * φ(g*h)⁻¹` for some `φ : G → ℂˣ`
* `ScalarCocycle.CohomologousTo` : two cocycles are cohomologous if their ratio
  is a coboundary

## Main results

* `ScalarCocycle.CohomologousTo.equivalence` : cohomologous-to is an equivalence
  relation
* `ScalarCocycle.isCoboundary_iff_cohomologousTo_one` : a cocycle is a coboundary
  iff it is cohomologous to the trivial cocycle

## References

* Pérez-García et al., *String order and symmetries in quantum spin lattices*,
  arXiv:0802.0447
* Chen, Gu, Wen, *Classification of gapped symmetric phases in one-dimensional
  spin systems*, Phys. Rev. B 83, 035107 (2011)
-/

namespace TNLean.Algebra

variable {G : Type*} [Group G]

/-! ### Coboundary and cohomologous definitions -/

/-- A scalar 2-cocycle `ω` is a coboundary if there exists `φ : G → ℂˣ` such that
`ω(g,h) = φ(g) * φ(h) * φ(g*h)⁻¹` for all `g, h`. -/
def ScalarCocycle.IsCoboundary (ω : ScalarCocycle G) : Prop :=
  ∃ φ : G → Units ℂ, ∀ g h, ω g h = φ g * φ h * (φ (g * h))⁻¹

/-- Two cocycles `ω₁` and `ω₂` are cohomologous if their ratio is a coboundary,
i.e., `ω₁(g,h) = φ(g) * φ(h) * φ(g*h)⁻¹ * ω₂(g,h)` for some `φ : G → ℂˣ`. -/
def ScalarCocycle.CohomologousTo (ω₁ ω₂ : ScalarCocycle G) : Prop :=
  ∃ φ : G → Units ℂ, ∀ g h, ω₁ g h = φ g * φ h * (φ (g * h))⁻¹ * ω₂ g h

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

/-- A cocycle is a coboundary iff it is cohomologous to the trivial cocycle `fun _ _ => 1`. -/
lemma ScalarCocycle.isCoboundary_iff_cohomologousTo_one (ω : ScalarCocycle G) :
    ω.IsCoboundary ↔ CohomologousTo ω (fun _ _ => 1) := by
  constructor
  -- Both directions: `mul_one` absorbs or introduces the trivial cocycle `1`
  · rintro ⟨φ, hφ⟩
    exact ⟨φ, fun g h => by rw [hφ g h]; simp [mul_one]⟩
  · rintro ⟨φ, hφ⟩
    exact ⟨φ, fun g h => by rw [hφ g h]; simp [mul_one]⟩

end TNLean.Algebra
