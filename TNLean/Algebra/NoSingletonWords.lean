/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.EquivFin

/-!
# Words with no singleton letter

A word of length `2 * p` in which each occurring letter appears at least twice
uses at most `p` letters. Every word using at most `p` letters factors through
`Fin p`; hence there are at most `card β ^ p * p ^ (2 * p)` such words over a
finite nonempty alphabet `β`.

This is the combinatorial estimate for an even-moment approach to the sampled
projection in LVV, arXiv:1307.5143v1, Section 2.3.1. The cancellation of words
with a singleton letter and the matrix concentration estimate are separate
results. The source's ground-energy dependence is discussed in
`docs/paper-gaps/lvv13_sampling_ground_energy.tex`.
-/

open Finset

namespace Finset

/-- If every nonempty fiber of a map on a finite set has at least two members,
its image has at most half as many members as the set. -/
theorem card_image_le_half_of_no_singleton {α β : Type*} [DecidableEq β]
    (s : Finset α) (f : α → β)
    (hf : ∀ b ∈ s.image f, 2 ≤ (s.filter fun a ↦ f a = b).card) :
    2 * (s.image f).card ≤ s.card := by
  calc
    2 * (s.image f).card = ∑ _b ∈ s.image f, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ b ∈ s.image f, (s.filter fun a ↦ f a = b).card := sum_le_sum hf
    _ = s.card := (card_eq_sum_card_image f s).symm

end Finset

namespace Fintype

open Classical in
/-- A function with at most `p` values factors through a set of `p` elements. -/
theorem exists_factor_fin_of_card_range_le {α β : Type*} [Fintype α]
    [Nonempty β] {p : ℕ} (f : α → β)
    (hf : Fintype.card (Set.range f) ≤ p) :
    ∃ a : α → Fin p, ∃ b : Fin p → β, b ∘ a = f := by
  classical
  obtain ⟨e⟩ : Nonempty (Set.range f ↪ Fin p) :=
    Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_fin] using hf)
  refine ⟨fun x ↦ e ⟨f x, ⟨x, rfl⟩⟩,
    Function.extend e Subtype.val (fun _ ↦ Classical.arbitrary β), ?_⟩
  funext x
  exact e.injective.extend_apply _ _ _

open Classical in
/-- Counting functions with at most `p` values by their factorizations through `Fin p`. -/
theorem card_functions_of_card_range_le {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty β] (p : ℕ) :
    Fintype.card {f : α → β // Fintype.card (Set.range f) ≤ p} ≤
      Fintype.card β ^ p * p ^ Fintype.card α := by
  classical
  let F : (α → Fin p) × (Fin p → β) → (α → β) := fun ab ↦ ab.2 ∘ ab.1
  have hsub : (Finset.univ.filter fun f : α → β ↦
      Fintype.card (Set.range f) ≤ p) ⊆ Finset.univ.image F := by
    intro f hf
    obtain ⟨a, b, hab⟩ := exists_factor_fin_of_card_range_le f (Finset.mem_filter.mp hf).2
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_univ _, hab⟩
  calc
    _ = (Finset.univ.filter fun f : α → β ↦
        Fintype.card (Set.range f) ≤ p).card := Fintype.card_subtype _
    _ ≤ (Finset.univ.image F).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset ((α → Fin p) × (Fin p → β))).card := Finset.card_image_le
    _ = _ := by simp [Nat.mul_comm]

open Classical in
/-- There are at most `card β ^ p * p ^ (2 * p)` words of length `2 * p` over a finite
nonempty alphabet `β` without a letter that occurs exactly once. This is the counting
step in the even-moment approach to LVV, arXiv:1307.5143v1, Section 2.3.1;
no matrix concentration estimate is asserted here. -/
theorem card_even_words_without_singleton {β : Type*} [Fintype β] [Nonempty β] (p : ℕ) :
    Fintype.card {f : Fin (2 * p) → β //
      ∀ b : β, (Finset.univ.filter fun a ↦ f a = b).card ≠ 1} ≤
      Fintype.card β ^ p * p ^ (2 * p) := by
  classical
  have hbound (f : Fin (2 * p) → β)
      (hf : ∀ b : β, (Finset.univ.filter fun a ↦ f a = b).card ≠ 1) :
      Fintype.card (Set.range f) ≤ p := by
    have hi := Finset.card_image_le_half_of_no_singleton Finset.univ f (by
      intro b hb
      obtain ⟨a, ha, hab⟩ := Finset.mem_image.mp hb
      have hpos : 0 < (Finset.univ.filter fun a ↦ f a = b).card :=
        Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hab⟩⟩
      have := hf b
      omega)
    have hcard : Fintype.card (Set.range f) = (Finset.univ.image f).card :=
      Fintype.card_of_finset' _ (fun _ ↦ by simp)
    rw [hcard]
    simp only [Finset.card_univ, Fintype.card_fin] at hi
    omega
  calc
    _ ≤ Fintype.card {f : Fin (2 * p) → β // Fintype.card (Set.range f) ≤ p} :=
      Fintype.card_subtype_mono _ _ hbound
    _ ≤ _ := by simpa using card_functions_of_card_range_le (α := Fin (2 * p)) (β := β) p

end Fintype
