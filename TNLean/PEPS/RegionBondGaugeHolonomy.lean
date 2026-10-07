/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularWalkHolonomy

/-!
# Holonomy of regionally exact bond labels

If the labels on a region are a vertex coboundary, every walk supported in
that region has the corresponding endpoint transport. In particular every
closed walk there has identity holonomy. This elementary group statement has
no representation, dimension, injectivity, or spanning hypothesis.
-/

namespace TNLean.PEPS

variable {V : Type*} [LinearOrder V] {Γ : SimpleGraph V}
variable {G : Type*} [Group G]

/-- A regionally exact bond assignment transports by its two endpoint labels. -/
theorem regularWalkHolonomy_eq_relative_of_region (R : Finset V)
    (p : Edge Γ → G) (q : V → G)
    (hp : ∀ e : Edge Γ, e.1.1 ∈ R → e.1.2 ∈ R → p e = q e.1.2 * (q e.1.1)⁻¹)
    {v w : V} (γ : Γ.Walk v w) (hγ : ∀ x ∈ γ.support, x ∈ R) :
    regularWalkHolonomy p γ = q w * (q v)⁻¹ := by
  have heq : regularWalkHolonomy p γ =
      regularWalkHolonomy (fun e ↦ q e.1.2 * (q e.1.1)⁻¹) γ := by
    induction γ with
    | nil => rfl
    | @cons v w z h γ ih =>
      have hv : v ∈ R := hγ v (by simp)
      have hw : w ∈ R := hγ w (by simp)
      have htail : (Edge.ofAdj h).1.1 ∈ R := by
        rcases Edge.ofAdj_endpoints h with ⟨ht, _⟩ | ⟨ht, _⟩
        · simpa only [ht] using hv
        · simpa only [ht] using hw
      have hhead : (Edge.ofAdj h).1.2 ∈ R := by
        rcases Edge.ofAdj_endpoints h with ⟨_, hh⟩ | ⟨_, hh⟩
        · simpa only [hh] using hw
        · simpa only [hh] using hv
      rw [regularWalkHolonomy_cons, regularWalkHolonomy_cons,
        ih (fun x hx ↦ hγ x (by simpa using List.mem_cons_of_mem v hx))]
      simp only [regularDirectedTransport, hp _ htail hhead]
  rw [heq, regularWalkHolonomy_gradient]

/-- Every closed walk supported in a regionally exact assignment has trivial holonomy. -/
theorem regularWalkHolonomy_eq_one_of_region (R : Finset V)
    (p : Edge Γ → G) (q : V → G)
    (hp : ∀ e : Edge Γ, e.1.1 ∈ R → e.1.2 ∈ R → p e = q e.1.2 * (q e.1.1)⁻¹)
    {v : V} (γ : Γ.Walk v v) (hγ : ∀ x ∈ γ.support, x ∈ R) :
    regularWalkHolonomy p γ = 1 := by
  rw [regularWalkHolonomy_eq_relative_of_region R p q hp γ hγ, mul_inv_cancel]

end TNLean.PEPS
