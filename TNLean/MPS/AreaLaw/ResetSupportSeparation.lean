/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hamiltonian
import Mathlib.Data.Nat.Dist

/-!
# Separation of the reset support from the chain cores

The complement of two disjoint outer regions and the actual crossing supports
remain farther than `w - R` from the two cores. Their radius-`ℓ` neighborhood
is therefore disjoint from the cores whenever `ℓ + R ≤ w`. Crossing supports
are treated using their actual witnesses on opposite sides of the cut, so the
loss is exactly the interaction range.

## Main result

* `chain_reset_support_separation`: the strict core margin and disjointness of
  the exact real-radius neighborhood of the actual reset support.

**Scope restriction (contiguous chains):** The physical sites are `Fin L`.
The broader source domain may have gaps; see
`docs/paper-gaps/tnlean_one_dimensional_connected_domain_scope.tex`.

Source: TNLean one-dimensional note, `part2a_mps_information.tex`, lines 419–425.
This is a geometric support statement, without a quantum-state assumption.
-/

namespace TNLean.MPS.AreaLaw

/-- The actual localized reset region avoids both cores under the strict
core-to-complement margins. Source: TNLean note,
`part2a_mps_information.tex`, lines 419–425. -/
lemma chain_reset_support_separation
    {L R : ℕ} (D C R₀ C₀ : Finset (Fin L))
    (hDC : Disjoint D C) (w : ℝ)
    (hR : ∀ r ∈ R₀, ∀ y : Fin L, y ∉ D →
      w < (Nat.dist r.val y.val : ℝ))
    (hC : ∀ c ∈ C₀, ∀ x : Fin L, x ∉ C →
      w < (Nat.dist c.val x.val : ℝ)) :
    let Q := (D ∪ C)ᶜ
    let crossing := Entropy.crossingTerms (fun X : ChainSupport L R ↦ X.1) D
    let Z := crossing.biUnion (fun X ↦ X.1)
    (∀ z ∈ Q ∪ Z, ∀ a ∈ R₀ ∪ C₀,
      w - (R : ℝ) < (Nat.dist a.val z.val : ℝ)) ∧
      ∀ ℓ : ℝ, ℓ + (R : ℝ) ≤ w →
        Disjoint
          (Finset.univ.filter (fun y : Fin L ↦
            ∃ z ∈ Q ∪ Z, (Nat.dist z.val y.val : ℝ) ≤ ℓ))
          (R₀ ∪ C₀) := by
  classical
  intro Q crossing Z
  have hmargin (X : ChainSupport L R) (z : Fin L) (hz : z ∈ X.1)
      (y : Fin L) (hy : y ∈ X.1) (a : Fin L)
      (ha : w < (Nat.dist a.val y.val : ℝ)) :
      w - (R : ℝ) < (Nat.dist a.val z.val : ℝ) := by
    have hzy : (Nat.dist z.val y.val : ℝ) ≤ (R : ℝ) := by
      have h₁ := X.2.2 z hz y hy
      have h₂ := X.2.2 y hy z hz
      exact_mod_cast (show Nat.dist z.val y.val ≤ R by
        simp only [Nat.dist]
        omega)
    have htri : (Nat.dist a.val y.val : ℝ) ≤
        (Nat.dist a.val z.val : ℝ) + (Nat.dist z.val y.val : ℝ) := by
      exact_mod_cast Nat.dist.triangle_inequality a.val z.val y.val
    linarith
  have hcross (X : ChainSupport L R) (hX : X ∈ crossing) (z : Fin L) (hz : z ∈ X.1) :
      ∀ a ∈ R₀ ∪ C₀, w - (R : ℝ) < (Nat.dist a.val z.val : ℝ) := by
    have hsplit : (∃ x ∈ X.1, x ∈ D) ∧ ∃ y ∈ X.1, y ∉ D := by
      simpa only [crossing, Entropy.crossingTerms, Finset.mem_filter,
        Finset.mem_univ, true_and] using hX
    obtain ⟨⟨x, hx, hxD⟩, y, hy, hyD⟩ := hsplit
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact hmargin X z hz y hy a (hR a ha y hyD)
    · have hxC : x ∉ C := fun hxC ↦ Finset.disjoint_left.mp hDC hxD hxC
      exact hmargin X z hz x hx a (hC a ha x hxC)
  have hsep : ∀ z ∈ Q ∪ Z, ∀ a ∈ R₀ ∪ C₀,
      w - (R : ℝ) < (Nat.dist a.val z.val : ℝ) := by
    intro z hz a ha
    rcases Finset.mem_union.mp hz with hz | hz
    · have hnot : z ∉ D ∧ z ∉ C := by
        simpa only [Q, Finset.mem_compl, Finset.mem_union, not_or] using hz
      rcases Finset.mem_union.mp ha with ha | ha
      · exact (sub_le_self w (Nat.cast_nonneg R)).trans_lt (hR a ha z hnot.1)
      · exact (sub_le_self w (Nat.cast_nonneg R)).trans_lt (hC a ha z hnot.2)
    · obtain ⟨X, hX, hzX⟩ := Finset.mem_biUnion.mp hz
      exact hcross X hX z hzX a ha
  refine ⟨hsep, ?_⟩
  intro ℓ hℓ
  apply Finset.disjoint_left.mpr
  intro a ha hcore
  obtain ⟨z, hz, hza⟩ := (Finset.mem_filter.mp ha).2
  have hdist := hsep z hz a hcore
  rw [Nat.dist_comm z.val a.val] at hza
  linarith

end TNLean.MPS.AreaLaw
