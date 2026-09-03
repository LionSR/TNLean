/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Group.Action.Pretransitive
import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Stabilizer representatives and transition elements

This file formalizes the representative calculation preceding
arXiv:2502.20257, Lemma `lemma:h1h2` and Equation `eq:h1h2` (lines 7028–7042).
For a basepoint `x₀` in a transitive left `G`-set, representatives `k_x` satisfy
`k_x • x₀ = x` and `k_x₀ = 1`. Their transition element is
`t_k(g,x) = k_(g • x)⁻¹ g k_x`.

The transition element stabilizes `x₀` and obeys
`t_k(g₁g₂,x) = t_k(g₁,g₂ • x)t_k(g₂,x)`. The resulting specializations are
`h₂ = t_k(g₂,x)` and `h₁ = t_k(g₁,g₂ • x)`. In particular, the representative
in `h₁` is `k_(g₂ • x)`, correcting the printed `k_(g₁ • x)`.

No finiteness or normality assumption is used.
-/

namespace TNLean.Algebra

variable (G X : Type*) [Group G] [MulAction G X]

/-- Chosen representatives `k_x` for a transitive left action, normalized by
`k_x₀ = 1`, as used before arXiv:2502.20257, Lemma `lemma:h1h2`. -/
structure StabilizerRepresentatives (x₀ : X) where
  /-- The representative `k_x`. -/
  k : X → G
  /-- Each `k_x` carries the basepoint to `x`. -/
  k_smul_x₀ : ∀ x, k x • x₀ = x
  /-- The representative of the basepoint is the identity. -/
  k_x₀ : k x₀ = 1

namespace StabilizerRepresentatives

variable {G X : Type*} [Group G] [MulAction G X] {x₀ : X}

/-- A pretransitive action admits representatives normalized at any chosen
basepoint. -/
noncomputable def ofPretransitive [MulAction.IsPretransitive G X] (x₀ : X) :
    StabilizerRepresentatives G X x₀ := by
  classical
  exact {
    k := fun x ↦ if x = x₀ then 1
      else Classical.choose (MulAction.exists_smul_eq G x₀ x)
    k_smul_x₀ := fun x ↦ by
      by_cases hx : x = x₀
      · simp [hx]
      · simp only [hx, ↓reduceIte]
        exact Classical.choose_spec (MulAction.exists_smul_eq G x₀ x)
    k_x₀ := by simp }


/-- The paper's transition element
`t_k(g,x) = k_(g • x)⁻¹ g k_x`. -/
def transitionElement (K : StabilizerRepresentatives G X x₀) (g : G) (x : X) : G :=
  (K.k (g • x))⁻¹ * g * K.k x

/-- Every transition element belongs to the stabilizer of the basepoint. -/
theorem transitionElement_mem_stabilizer (K : StabilizerRepresentatives G X x₀)
    (g : G) (x : X) : transitionElement K g x ∈ MulAction.stabilizer G x₀ := by
  rw [MulAction.mem_stabilizer_iff]
  calc
    ((K.k (g • x))⁻¹ * g * K.k x) • x₀ =
        (K.k (g • x))⁻¹ • (g • (K.k x • x₀)) := by
      rw [mul_smul, mul_smul]
    _ = (K.k (g • x))⁻¹ • (g • x) := by rw [K.k_smul_x₀]
    _ = (K.k (g • x))⁻¹ • (K.k (g • x) • x₀) := by rw [K.k_smul_x₀]
    _ = x₀ := by rw [← mul_smul, Group.inv_mul_cancel, one_smul]

/-- The transition elements obey
`t_k(g₁g₂,x) = t_k(g₁,g₂ • x)t_k(g₂,x)`. -/
theorem transitionElement_mul (K : StabilizerRepresentatives G X x₀)
    (g₁ g₂ : G) (x : X) :
    transitionElement K (g₁ * g₂) x =
      transitionElement K g₁ (g₂ • x) * transitionElement K g₂ x := by
  simp [transitionElement, mul_smul, mul_assoc]

/-- The factor `h₂` in arXiv:2502.20257, Equation `eq:h1h2`. -/
def h₂ (K : StabilizerRepresentatives G X x₀) (g₂ : G) (x : X) : G :=
  transitionElement K g₂ x

/-- The corrected factor `h₁` in arXiv:2502.20257, Equation `eq:h1h2`.
The final representative is `k_(g₂ • x)`, not the printed `k_(g₁ • x)`. -/
def h₁ (K : StabilizerRepresentatives G X x₀) (g₁ g₂ : G) (x : X) : G :=
  transitionElement K g₁ (g₂ • x)

/-- The explicit representative formula for `h₂`. -/
theorem h₂_eq (K : StabilizerRepresentatives G X x₀) (g₂ : G) (x : X) :
    h₂ K g₂ x = (K.k (g₂ • x))⁻¹ * g₂ * K.k x := rfl

/-- The explicit corrected representative formula for `h₁`. -/
theorem h₁_eq (K : StabilizerRepresentatives G X x₀) (g₁ g₂ : G) (x : X) :
    h₁ K g₁ g₂ x = (K.k ((g₁ * g₂) • x))⁻¹ * g₁ * K.k (g₂ • x) := by
  simp [h₁, transitionElement, mul_smul]

/-- Both factors in Equation `eq:h1h2` belong to the stabilizer. -/
theorem h₁_h₂_mem_stabilizer (K : StabilizerRepresentatives G X x₀)
    (g₁ g₂ : G) (x : X) :
    h₁ K g₁ g₂ x ∈ MulAction.stabilizer G x₀ ∧
      h₂ K g₂ x ∈ MulAction.stabilizer G x₀ := by
  exact ⟨K.transitionElement_mem_stabilizer g₁ (g₂ • x),
    K.transitionElement_mem_stabilizer g₂ x⟩

/-- The transition product law identifies `t_k(g₁g₂,x)` with `h₁h₂`. -/
theorem transitionElement_mul_eq_h₁_mul_h₂
    (K : StabilizerRepresentatives G X x₀) (g₁ g₂ : G) (x : X) :
    transitionElement K (g₁ * g₂) x = h₁ K g₁ g₂ x * h₂ K g₂ x :=
  K.transitionElement_mul g₁ g₂ x

end StabilizerRepresentatives

end TNLean.Algebra
