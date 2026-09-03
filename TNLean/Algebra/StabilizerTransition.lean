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

**Local fix (printed representative index):** The source's `k_(g₁ • x)` is replaced
by `k_(g₂ • x)`, as documented in
`docs/paper-gaps/fbc25_stabilizer_transition_index_typo.tex`.

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


/-- The paper's stabilizer-valued transition element
`t_k(g,x) = k_(g • x)⁻¹ g k_x`. -/
def transitionElement (K : StabilizerRepresentatives G X x₀) (g : G) (x : X) :
    MulAction.stabilizer G x₀ :=
  ⟨(K.k (g • x))⁻¹ * g * K.k x, by
    rw [MulAction.mem_stabilizer_iff]
    calc
      ((K.k (g • x))⁻¹ * g * K.k x) • x₀ =
          (K.k (g • x))⁻¹ • (g • (K.k x • x₀)) := by
        rw [mul_smul, mul_smul]
      _ = (K.k (g • x))⁻¹ • (g • x) := by rw [K.k_smul_x₀]
      _ = (K.k (g • x))⁻¹ • (K.k (g • x) • x₀) := by rw [K.k_smul_x₀]
      _ = x₀ := by rw [← mul_smul, Group.inv_mul_cancel, one_smul]⟩

/-- The underlying group element of `t_k(g,x)` is
`k_(g • x)⁻¹ g k_x`. -/
@[simp]
theorem coe_transitionElement (K : StabilizerRepresentatives G X x₀)
    (g : G) (x : X) :
    (transitionElement K g x : G) = (K.k (g • x))⁻¹ * g * K.k x := rfl

/-- The transition elements obey the subgroup identity
`t_k(g₁g₂,x) = t_k(g₁,g₂ • x)t_k(g₂,x)`. -/
theorem transitionElement_mul (K : StabilizerRepresentatives G X x₀)
    (g₁ g₂ : G) (x : X) :
    transitionElement K (g₁ * g₂) x =
      transitionElement K g₁ (g₂ • x) * transitionElement K g₂ x := by
  apply Subtype.ext
  simp [mul_smul, mul_assoc]

end StabilizerRepresentatives

end TNLean.Algebra
