/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ProjectiveRepresentation

/-!
# Multiplicative scalar 3-cocycles

This file isolates the scalar algebra of the fusion-tensor gauge freedom in
arXiv:2502.20257, equations `eq:scalar_fus_ten`, `eq:3-cocycle`, and
`eq:omegagauge`. It does not assert the existence of fusion tensors or attach
these scalars to a matrix product unitary.

For a group `G`, a scalar 3-cochain has values in `ℂˣ`. A scalar 2-cochain is
represented by the existing function type `ScalarCocycle G`; its name and
2-cocycle interpretation are unchanged.

## Main definitions

* `ScalarThreeCochain`: multiplicative scalar 3-cochains.
* `ScalarThreeCochain.IsCocycle`: the associativity 3-cocycle equation.
* `ScalarThreeCochain.IsNormalized`: triviality when any argument is the identity.
* `ScalarThreeCochain.coboundary`: the 2-cochain coboundary in `eq:omegagauge`.
* `ScalarThreeCochain.fusionGauge`: the scalar fusion-tensor gauge action.
* `ScalarThreeCochain.GaugeEquivalent`: equality up to a fusion gauge.
* `ScalarThreeCochain.IsNonanomalous`: triviality of the scalar gauge class.
-/

namespace TNLean.Algebra

variable {G : Type*} [Group G]

/-- A multiplicative scalar 3-cochain `G × G × G → ℂˣ`.

This is the scalar function denoted by `ω` in arXiv:2502.20257,
`eq:3-cocycle`. -/
abbrev ScalarThreeCochain (G : Type*) := G → G → G → Units ℂ

namespace ScalarCocycle

/-- A scalar 2-cochain is normalized when it is one whenever either argument
is the identity. This is the normalization required for its coboundary to
preserve normalized 3-cochains. -/
def IsNormalized (β : ScalarCocycle G) : Prop :=
  (∀ g, β 1 g = 1) ∧ (∀ g, β g 1 = 1)

end ScalarCocycle

namespace ScalarThreeCochain

/-- The multiplicative scalar 3-cocycle equation

`ω(gh,k,l) ω(g,h,kl) = ω(g,h,k) ω(g,hk,l) ω(h,k,l)`

from arXiv:2502.20257, `eq:3-cocycle`. -/
def IsCocycle (ω : ScalarThreeCochain G) : Prop :=
  ∀ g h k l,
    ω (g * h) k l * ω g h (k * l) =
      ω g h k * ω g (h * k) l * ω h k l

/-- A scalar 3-cochain is normalized when it equals one whenever any argument
is the identity. This is the normalization stated after arXiv:2502.20257,
`eq:triv_omegas` (whose displayed formula repeats its third case). -/
def IsNormalized (ω : ScalarThreeCochain G) : Prop :=
  (∀ h k, ω 1 h k = 1) ∧
    (∀ g k, ω g 1 k = 1) ∧
      (∀ g h, ω g h 1 = 1)

/-- The multiplicative 3-coboundary of a scalar 2-cochain:

`(dβ)(g,h,k) = β(g,hk) β(h,k) / (β(g,h) β(gh,k))`.

The factor order is exactly arXiv:2502.20257, `eq:omegagauge`, induced by the
fusion-tensor scalar freedom in `eq:scalar_fus_ten`. -/
def coboundary (β : ScalarCocycle G) : ScalarThreeCochain G :=
  fun g h k => (β g (h * k) * β h k) / (β g h * β (g * h) k)

/-- The fusion-tensor scalar gauge action from arXiv:2502.20257,
`eq:omegagauge`: `ω ↦ dβ · ω`. -/
def fusionGauge (β : ScalarCocycle G) (ω : ScalarThreeCochain G) :
    ScalarThreeCochain G :=
  fun g h k => coboundary β g h k * ω g h k

/-- The trivial scalar 2-cochain acts identically. -/
@[simp]
theorem fusionGauge_one (ω : ScalarThreeCochain G) :
    fusionGauge (fun _ _ => 1) ω = ω := by
  funext g h k
  simp [fusionGauge, coboundary]

/-- Successive fusion gauges multiply their scalar 2-cochains pointwise. -/
theorem fusionGauge_comp (β γ : ScalarCocycle G) (ω : ScalarThreeCochain G) :
    fusionGauge γ (fusionGauge β ω) = fusionGauge (β * γ) ω := by
  funext g h k
  simp only [fusionGauge, coboundary, Pi.mul_apply, div_eq_mul_inv, mul_inv_rev]
  simp only [mul_assoc, mul_comm, mul_left_comm]

/-- The coboundary of every scalar 2-cochain is a scalar 3-cocycle. -/
theorem isCocycle_coboundary (β : ScalarCocycle G) : IsCocycle (coboundary β) := by
  intro g h k l
  simp only [coboundary, mul_assoc]
  apply Units.ext
  push_cast
  field_simp

/-- The pointwise product of scalar 3-cocycles is a scalar 3-cocycle. -/
theorem IsCocycle.mul {ω η : ScalarThreeCochain G}
    (hω : IsCocycle ω) (hη : IsCocycle η) : IsCocycle (ω * η) := by
  intro g h k l
  simp only [Pi.mul_apply]
  calc
    _ = (ω (g * h) k l * ω g h (k * l)) *
        (η (g * h) k l * η g h (k * l)) := by ac_rfl
    _ = (ω g h k * ω g (h * k) l * ω h k l) *
        (η g h k * η g (h * k) l * η h k l) := by rw [hω, hη]
    _ = _ := by ac_rfl

/-- Fusion-tensor scalar gauge transformations preserve the 3-cocycle equation. -/
theorem IsCocycle.fusionGauge {ω : ScalarThreeCochain G} (hω : IsCocycle ω)
    (β : ScalarCocycle G) : IsCocycle (fusionGauge β ω) :=
  (isCocycle_coboundary β).mul hω

/-- A normalized scalar 2-cochain has normalized 3-coboundary. -/
theorem isNormalized_coboundary {β : ScalarCocycle G}
    (hβ : β.IsNormalized) : IsNormalized (coboundary β) := by
  rcases hβ with ⟨hβl, hβr⟩
  refine ⟨fun h k => ?_, fun g k => ?_, fun g h => ?_⟩
  · simp [ScalarThreeCochain.coboundary, hβl]
  · simp [ScalarThreeCochain.coboundary, hβl, hβr]
  · simp [ScalarThreeCochain.coboundary, hβr]

/-- Pointwise multiplication preserves normalized scalar 3-cochains. -/
theorem IsNormalized.mul {ω η : ScalarThreeCochain G}
    (hω : IsNormalized ω) (hη : IsNormalized η) : IsNormalized (ω * η) := by
  rcases hω with ⟨hω₁, hω₂, hω₃⟩
  rcases hη with ⟨hη₁, hη₂, hη₃⟩
  refine ⟨fun h k => ?_, fun g k => ?_, fun g h => ?_⟩
  · simp [hω₁, hη₁]
  · simp [hω₂, hη₂]
  · simp [hω₃, hη₃]

/-- A fusion gauge preserves normalization when its scalar 2-cochain is normalized. -/
theorem IsNormalized.fusionGauge {ω : ScalarThreeCochain G}
    (hω : IsNormalized ω) {β : ScalarCocycle G} (hβ : β.IsNormalized) :
    IsNormalized (fusionGauge β ω) :=
  (isNormalized_coboundary hβ).mul hω

/-- Two scalar 3-cochains are fusion-gauge equivalent when one is obtained from
the other by the action in arXiv:2502.20257, `eq:omegagauge`. -/
def GaugeEquivalent (ω η : ScalarThreeCochain G) : Prop :=
  ∃ β : ScalarCocycle G, fusionGauge β ω = η

namespace GaugeEquivalent

/-- Scalar fusion-gauge equivalence is reflexive. -/
theorem refl (ω : ScalarThreeCochain G) : GaugeEquivalent ω ω :=
  ⟨fun _ _ => 1, fusionGauge_one ω⟩

/-- Scalar fusion-gauge equivalence is symmetric. -/
theorem symm {ω η : ScalarThreeCochain G} (h : GaugeEquivalent ω η) :
    GaugeEquivalent η ω := by
  obtain ⟨β, rfl⟩ := h
  refine ⟨β⁻¹, ?_⟩
  rw [fusionGauge_comp, mul_inv_cancel]
  change fusionGauge (fun _ _ => 1) ω = ω
  exact fusionGauge_one ω

/-- Scalar fusion-gauge equivalence is transitive. -/
theorem trans {ω η θ : ScalarThreeCochain G}
    (hωη : GaugeEquivalent ω η) (hηθ : GaugeEquivalent η θ) :
    GaugeEquivalent ω θ := by
  obtain ⟨β, rfl⟩ := hωη
  obtain ⟨γ, rfl⟩ := hηθ
  exact ⟨β * γ, (fusionGauge_comp β γ ω).symm⟩

/-- Scalar fusion-gauge equivalence is an equivalence relation. -/
theorem equivalence : Equivalence (GaugeEquivalent (G := G)) :=
  ⟨refl, symm, trans⟩

end GaugeEquivalent

/-- A scalar 3-cochain has trivial gauge class when it is fusion-gauge
equivalent to the constant cochain one. -/
def IsTrivialGaugeClass (ω : ScalarThreeCochain G) : Prop :=
  GaugeEquivalent ω (fun _ _ _ => 1)

/-- At the scalar algebra level, nonanomalous means that the 3-cochain has
trivial gauge class, matching the terminology following arXiv:2502.20257,
`eq:omegagauge`. No existence claim about MPU fusion tensors is included. -/
def IsNonanomalous (ω : ScalarThreeCochain G) : Prop :=
  IsTrivialGaugeClass ω

/-- Scalar nonanomalousness is exactly triviality of the fusion-gauge class. -/
theorem isNonanomalous_iff_isTrivialGaugeClass (ω : ScalarThreeCochain G) :
    IsNonanomalous ω ↔ IsTrivialGaugeClass ω :=
  Iff.rfl

end ScalarThreeCochain

end TNLean.Algebra
