/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.Templates

/-!
# Inverse images of ordered two-family partitions

Taking the inverse image of an ordered partition preserves its labels and their
order, including labels whose inverse image is empty. In particular, this
restricts a partition of lattice sites to a finite physical domain without
changing the earlier pieces of either family.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states*, proof of Lemma 3.2, `02-information.tex`, lines 197–222, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace TNLean.PEPS.AreaLaw.Geometry.OrderedTwoFamilyPartition

variable {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype β]
  {A : Finset α}

/-- The inverse image of every piece and the residual set, with the original
family labels and their original order. -/
def comap (P : OrderedTwoFamilyPartition A) (f : β → α) :
    OrderedTwoFamilyPartition (Finset.univ.filter fun x ↦ f x ∈ A) where
  pieceCount := P.pieceCount
  family := P.family
  piece i := Finset.univ.filter fun x ↦ f x ∈ P.piece i
  residual := Finset.univ.filter fun x ↦ f x ∈ P.residual
  disjoint i j hij := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact Finset.disjoint_left.mp (P.disjoint i j hij)
      (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
  residual_disjoint i := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact Finset.disjoint_left.mp (P.residual_disjoint i)
      (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
  cover := by
    ext x
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_biUnion] using Finset.ext_iff.mp P.cover (f x)

/-- Restricting the pieces preserves precisely the earlier pieces of the same
family; no new enumeration is introduced. -/
theorem earlierSameFamily_comap (P : OrderedTwoFamilyPartition A) (f : β → α)
    (i : Fin P.pieceCount) :
    (P.comap f).earlierSameFamily i =
      Finset.univ.filter fun x ↦ f x ∈ P.earlierSameFamily i := by
  ext x
  simp only [earlierSameFamily, comap, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, hx⟩
    exact ⟨j, (Finset.mem_filter.mp hj).2, hx⟩
  · rintro ⟨j, hj, hx⟩
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, hx⟩

/-- An injective change of sites cannot increase the number of residual sites. -/
theorem card_residual_comap_le (P : OrderedTwoFamilyPartition A) (f : β → α)
    (hf : Function.Injective f) : (P.comap f).residual.card ≤ P.residual.card := by
  exact Finset.card_le_card_of_injOn f
    (fun _ hx ↦ (Finset.mem_filter.mp hx).2) hf.injOn

end TNLean.PEPS.AreaLaw.Geometry.OrderedTwoFamilyPartition
