/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Complex.Basic
import Mathlib.SetTheory.Cardinal.Order

/-!
# Signs for fixed-point-free involutions

A fixed-point-free involution partitions a set into two-element orbits. A
classical well-order orients every orbit, which gives opposite signs to its two
points. Conversely, an equation with product `-1` at a fixed point is
impossible for a sign valued in `{1, -1}`.

This isolates the sign choice in arXiv:2502.20257,
Proposition `prop:def_tens_anomalous`, equation `eq:defects_Z2b`, lines
2979--2981. The results apply to arbitrary types; finiteness of the block set
is not needed for this choice.
-/

namespace TNLean.Algebra

/-- A complex unit is a sign when it is either `1` or `-1`. -/
def IsComplexUnitSign (z : Units ℂ) : Prop :=
  z = 1 ∨ z = -1

/-- An involution admits an anomalous sign when its points can be labelled by
complex-unit signs whose values on each orbit multiply to `-1`.

This is the `{±1}`-valued condition on `ξ_g` in arXiv:2502.20257,
`eq:defects_Z2b`, lines 2979--2981, specialized to an order-two action. -/
def HasAnomalousInvolutionSign {X : Type*} (f : X → X) : Prop :=
  ∃ ξ : X → Units ℂ,
    (∀ x, IsComplexUnitSign (ξ x)) ∧ ∀ x, ξ x * ξ (f x) = -1

section Involution

variable {X : Type*} {f : X → X}

private noncomputable def orientedSign (f : X → X) (x : X) : Units ℂ := by
  classical
  exact if WellOrderingRel x (f x) then 1 else -1

private theorem orientedSign_isSign (x : X) :
    IsComplexUnitSign (orientedSign f x) := by
  classical
  simp only [orientedSign, IsComplexUnitSign]
  split <;> simp

private theorem orientedSign_mul_apply (hf : Function.Involutive f)
    (hfixed : ∀ x, f x ≠ x) (x : X) :
    orientedSign f x * orientedSign f (f x) = -1 := by
  classical
  rcases trichotomous_of WellOrderingRel x (f x) with hlt | heq | hgt
  · have hnot : ¬ WellOrderingRel (f x) x := fun h ↦ (asymm hlt h).elim
    simp [orientedSign, hlt, hf x, hnot]
  · exact (hfixed x heq.symm).elim
  · have hnot : ¬ WellOrderingRel x (f x) := fun h ↦ (asymm h hgt).elim
    simp [orientedSign, hgt, hf x, hnot]

/-- Every fixed-point-free involution admits a `{±1}`-valued function whose
values at paired points multiply to `-1`.

The proof orients each two-element orbit using a classical well-order. This
formalizes the sign choice in arXiv:2502.20257, `eq:defects_Z2b`, lines
2979--2981. -/
theorem hasAnomalousInvolutionSign_of_fixedPointFree (hf : Function.Involutive f)
    (hfixed : ∀ x, f x ≠ x) : HasAnomalousInvolutionSign f := by
  refine ⟨orientedSign f, orientedSign_isSign, ?_⟩
  exact orientedSign_mul_apply hf hfixed

/-- A fixed point obstructs the anomalous product equation for every genuinely
`{±1}`-valued complex-unit function. The range hypothesis is essential:
arbitrary complex units can have square `-1`.

This is the converse to the sign choice used in arXiv:2502.20257,
`eq:defects_Z2b`, lines 2979--2981. -/
theorem not_hasAnomalousInvolutionSign_of_fixedPoint {x : X} (hx : f x = x) :
    ¬ HasAnomalousInvolutionSign f := by
  rintro ⟨ξ, hsign, hmul⟩
  rcases hsign x with hone | hneg
  · simpa [hx, IsComplexUnitSign, hone] using hmul x
  · simpa [hx, IsComplexUnitSign, hneg] using hmul x

/-- For an involution, anomalous `{±1}` signs exist exactly when there are no
fixed points. This is the precise sign-valued form of the choice in
arXiv:2502.20257, `eq:defects_Z2b`, lines 2979--2981. -/
theorem hasAnomalousInvolutionSign_iff_fixedPointFree (hf : Function.Involutive f) :
    HasAnomalousInvolutionSign f ↔ ∀ x, f x ≠ x := by
  constructor
  · intro hsign x hx
    exact not_hasAnomalousInvolutionSign_of_fixedPoint hx hsign
  · exact hasAnomalousInvolutionSign_of_fixedPointFree hf

end Involution

section GroupAction

variable {G X : Type*} [Group G] [MulAction G X]

/-- Acting by an element whose square is the identity defines an involution. -/
theorem involutive_smul_of_mul_self_eq_one {g : G} (hg : g * g = 1) :
    Function.Involutive (fun x : X ↦ g • x) := by
  intro x
  change g • (g • x) = x
  rw [← mul_smul, hg, one_smul]

/-- For an order-two group element, an anomalous `{±1}` sign on the block set
exists exactly when that element fixes no block.

This is the group-action specialization of the function `ξ_g` required in
arXiv:2502.20257, Proposition `prop:def_tens_anomalous`, equation
`eq:defects_Z2b`, lines 2979--2981. -/
theorem hasAnomalousInvolutionSign_smul_iff {g : G} (hg : g * g = 1) :
    HasAnomalousInvolutionSign (fun x : X ↦ g • x) ↔ ∀ x : X, g • x ≠ x :=
  hasAnomalousInvolutionSign_iff_fixedPointFree
    (involutive_smul_of_mul_self_eq_one hg)

end GroupAction

end TNLean.Algebra
