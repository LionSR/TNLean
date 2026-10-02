/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularRegionCounting

/-!
# Counting regular bonds carrying group operators

For a regular bond oriented from a source vertex to a target vertex, the head
label is the bond group element times the tail label. Two configurations related
by a vertex translation are compatible precisely when the translations intertwine
the two bond group elements. Once this condition holds, the second configuration
has one free group label per bond.

This is the finite counting step in contractions with group-valued closures in
Schuch, Cirac, and Pérez-García, arXiv:1001.3807, equation
`eq:2d:peps-with-ug-uh` and the proof of Theorem 6.9, lines 1935–1990.
-/

open scoped BigOperators

namespace TNLean.PEPS

variable {E V G : Type*} [Fintype E] [DecidableEq E]
variable [Group G] [Fintype G] [DecidableEq G]

omit [Fintype E] [DecidableEq E] [Fintype G] [DecidableEq G] in
/-- Compatibility of the two ends of a regular bond is equivalent to the
intertwining equation for its vertex translations. -/
theorem regularBond_labels_iff_intertwining (source target : E → V)
    (u w : E → G) (q : V → G) (η θ : E → G) :
    (∀ e, η e = q (source e) * θ e ∧
      u e * η e = q (target e) * w e * θ e) ↔
      η = (fun e => q (source e) * θ e) ∧
        ∀ e, u e * q (source e) = q (target e) * w e := by
  constructor
  · intro h
    refine ⟨funext fun e => (h e).1, fun e => ?_⟩
    apply mul_right_cancel (b := θ e)
    simpa only [(h e).1, ← mul_assoc] using (h e).2
  · rintro ⟨rfl, h⟩ e
    exact ⟨rfl, by rw [← mul_assoc, h e]⟩

/-- Source: SCP10, regular bonds with group closures, lines 1935–1990.
Compatible vertex translations leave one independent label per regular bond;
incompatible translations contribute zero. -/
theorem sum_regularBond_labels_eq_card (source target : E → V)
    (u w : E → G) (q : V → G) :
    (∑ η : E → G, ∑ θ : E → G,
      if ∀ e, η e = q (source e) * θ e ∧
        u e * η e = q (target e) * w e * θ e then (1 : ℂ) else 0) =
      if ∀ e, u e * q (source e) = q (target e) * w e
      then (Fintype.card G : ℂ) ^ Fintype.card E else 0 := by
  classical
  simp only [regularBond_labels_iff_intertwining]
  rw [Finset.sum_comm]
  have hinner (θ : E → G) :
      (∑ η : E → G,
        if η = (fun e => q (source e) * θ e) ∧
          ∀ e, u e * q (source e) = q (target e) * w e then (1 : ℂ) else 0) =
        if ∀ e, u e * q (source e) = q (target e) * w e then 1 else 0 := by
    by_cases h : ∀ e, u e * q (source e) = q (target e) * w e <;> simp [h]
  simp only [hinner]
  split_ifs <;> simp

/-- Source: SCP10, the two directions of regular torus bonds in
`eq:2d:peps-with-ug-uh`. Two independent bond families leave two independent
group labels at each edge index, provided both intertwining equations hold. -/
theorem sum_two_regularBond_labels_eq_card (s₁ t₁ s₂ t₂ : E → V)
    (u₁ w₁ u₂ w₂ : E → G) (q : V → G) :
    (∑ η₁ : E → G, ∑ η₂ : E → G, ∑ θ₁ : E → G, ∑ θ₂ : E → G,
      if (∀ e, η₁ e = q (s₁ e) * θ₁ e ∧
          u₁ e * η₁ e = q (t₁ e) * w₁ e * θ₁ e) ∧
        (∀ e, η₂ e = q (s₂ e) * θ₂ e ∧
          u₂ e * η₂ e = q (t₂ e) * w₂ e * θ₂ e) then (1 : ℂ) else 0) =
      if (∀ e, u₁ e * q (s₁ e) = q (t₁ e) * w₁ e) ∧
        (∀ e, u₂ e * q (s₂ e) = q (t₂ e) * w₂ e)
      then (Fintype.card G : ℂ) ^ (2 * Fintype.card E) else 0 := by
  classical
  let P₁ (η θ : E → G) := ∀ e, η e = q (s₁ e) * θ e ∧
    u₁ e * η e = q (t₁ e) * w₁ e * θ e
  let P₂ (η θ : E → G) := ∀ e, η e = q (s₂ e) * θ e ∧
    u₂ e * η e = q (t₂ e) * w₂ e * θ e
  have hind (η₁ θ₁ η₂ θ₂ : E → G) :
      (if P₁ η₁ θ₁ ∧ P₂ η₂ θ₂ then (1 : ℂ) else 0) =
        (if P₁ η₁ θ₁ then 1 else 0) * (if P₂ η₂ θ₂ then 1 else 0) := by
    by_cases h₁ : P₁ η₁ θ₁ <;> by_cases h₂ : P₂ η₂ θ₂ <;> simp [h₁, h₂]
  change (∑ η₁ : E → G, ∑ η₂ : E → G, ∑ θ₁ : E → G, ∑ θ₂ : E → G,
    if P₁ η₁ θ₁ ∧ P₂ η₂ θ₂ then (1 : ℂ) else 0) = _
  calc
    _ = ∑ η₁ : E → G, ∑ θ₁ : E → G, ∑ η₂ : E → G, ∑ θ₂ : E → G,
        (if P₁ η₁ θ₁ then (1 : ℂ) else 0) * (if P₂ η₂ θ₂ then 1 else 0) := by
      simp only [hind]
      apply Finset.sum_congr rfl
      intro η₁ _
      rw [Finset.sum_comm]
    _ = (∑ η₁ : E → G, ∑ θ₁ : E → G, if P₁ η₁ θ₁ then (1 : ℂ) else 0) *
        (∑ η₂ : E → G, ∑ θ₂ : E → G, if P₂ η₂ θ₂ then (1 : ℂ) else 0) := by
      simp_rw [← Finset.mul_sum]
      simp only [Finset.sum_mul]
    _ = _ := by
      rw [sum_regularBond_labels_eq_card s₁ t₁ u₁ w₁ q,
        sum_regularBond_labels_eq_card s₂ t₂ u₂ w₂ q]
      by_cases h₁ : ∀ e, u₁ e * q (s₁ e) = q (t₁ e) * w₁ e <;>
        by_cases h₂ : ∀ e, u₂ e * q (s₂ e) = q (t₂ e) * w₂ e <;>
        simp [h₁, h₂, ← pow_add, ← two_mul]

end TNLean.PEPS
