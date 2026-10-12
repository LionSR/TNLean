/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.AmbientBoundary
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Tactic.Tauto

/-!
# Physical cut boundaries under set operations

All boundaries consist of actual unordered edges of the induced physical graph.
Changing a site affects at most four edges. This gives the perturbation estimate
used after deterministic-prefix comparison in the scanner.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, Lemma 9.1(2), lines 251–257, at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw

open scoped symmDiff

/-- An unordered physical edge crosses a cut precisely when exactly one endpoint belongs to it. -/
theorem mem_edgeBoundary_pair_iff {Λ : Finset (ℤ × ℤ)} (A : Finset (Site Λ))
    (x y : Site Λ) :
    s(x, y) ∈ edgeBoundary Λ A ↔ (domainGraph Λ).Adj x y ∧
      ((x ∈ A ∧ y ∉ A) ∨ (y ∈ A ∧ x ∉ A)) := by
  classical
  simp only [edgeBoundary, Finset.mem_filter, SimpleGraph.mem_edgeFinset,
    SimpleGraph.mem_edgeSet, Sym2.eq_iff]
  constructor
  · rintro ⟨hxy, x', hx, y', hy, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨hxy, Or.inl ⟨hx, hy⟩⟩
    · exact ⟨hxy, Or.inr ⟨hx, hy⟩⟩
  · rintro ⟨hxy, ⟨hx, hy⟩ | ⟨hy, hx⟩⟩
    · exact ⟨hxy, x, hx, y, hy, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨hxy, y, hy, x, hx, Or.inr ⟨rfl, rfl⟩⟩

/-- Exchanging the two sides of a physical cut preserves its unordered boundary. -/
@[simp] theorem edgeBoundary_compl (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) :
    edgeBoundary Λ Aᶜ = edgeBoundary Λ A := by
  classical
  ext e
  obtain ⟨x, y⟩ := e
  simp only [mem_edgeBoundary_pair_iff, Finset.mem_compl, not_not]
  tauto

/-- A physical crossing edge of a union crosses at least one constituent. -/
theorem edgeBoundary_union_subset (Λ : Finset (ℤ × ℤ)) (A B : Finset (Site Λ)) :
    edgeBoundary Λ (A ∪ B) ⊆ edgeBoundary Λ A ∪ edgeBoundary Λ B := by
  classical
  rintro ⟨x, y⟩
  simp only [Finset.mem_union, mem_edgeBoundary_pair_iff]
  tauto

/-- A physical crossing edge of a difference crosses at least one constituent. -/
theorem edgeBoundary_sdiff_subset (Λ : Finset (ℤ × ℤ)) (A B : Finset (Site Λ)) :
    edgeBoundary Λ (A \ B) ⊆ edgeBoundary Λ A ∪ edgeBoundary Λ B := by
  classical
  rintro ⟨x, y⟩
  simp only [Finset.mem_union, mem_edgeBoundary_pair_iff, Finset.mem_sdiff]
  tauto

/-- Physical cut boundary is subadditive under unions. -/
theorem card_edgeBoundary_union_le (Λ : Finset (ℤ × ℤ)) (A B : Finset (Site Λ)) :
    (edgeBoundary Λ (A ∪ B)).card ≤ (edgeBoundary Λ A).card + (edgeBoundary Λ B).card :=
  (Finset.card_le_card (edgeBoundary_union_subset Λ A B)).trans (Finset.card_union_le _ _)

/-- Physical cut boundary is subadditive under set differences. -/
theorem card_edgeBoundary_sdiff_le (Λ : Finset (ℤ × ℤ)) (A B : Finset (Site Λ)) :
    (edgeBoundary Λ (A \ B)).card ≤ (edgeBoundary Λ A).card + (edgeBoundary Λ B).card :=
  (Finset.card_le_card (edgeBoundary_sdiff_subset Λ A B)).trans (Finset.card_union_le _ _)

/-- A physical endpoint cover bounds the edge boundary by four times its size.
No ambient edge missing from the physical domain is counted. -/
theorem card_edgeBoundary_le_of_endpoint_cover (Λ : Finset (ℤ × ℤ))
    (A R : Finset (Site Λ))
    (hR : ∀ x ∈ A, ∀ y ∉ A, (domainGraph Λ).Adj x y → x ∈ R ∨ y ∈ R) :
    (edgeBoundary Λ A).card ≤ 4 * R.card := by
  classical
  let E (p : ℤ × ℤ) := (latticeNeighbors p).image fun q ↦ s(p, q)
  have hE (p : ℤ × ℤ) : (E p).card ≤ 4 :=
    Finset.card_image_le.trans (card_latticeNeighbors_le p)
  have hsub : (edgeBoundary Λ A).image (Sym2.map Subtype.val) ⊆
      (R.image Subtype.val).biUnion E := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hxy, x, hx, y, hy, rfl⟩ := Finset.mem_filter.mp hf
    have hadj : (domainGraph Λ).Adj x y := by
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hxy
    have hneigh : y.val ∈ latticeNeighbors x.val := mem_latticeNeighbors_iff.mpr hadj
    rcases hR x hx y hy hadj with hxR | hyR
    · exact Finset.mem_biUnion.mpr ⟨x.val, Finset.mem_image.mpr ⟨x, hxR, rfl⟩,
        Finset.mem_image.mpr ⟨y.val, hneigh, rfl⟩⟩
    · exact Finset.mem_biUnion.mpr ⟨y.val, Finset.mem_image.mpr ⟨y, hyR, rfl⟩,
        Finset.mem_image.mpr ⟨x.val, latticeNeighbors_symm hneigh, Sym2.eq_swap⟩⟩
  calc
    (edgeBoundary Λ A).card =
        ((edgeBoundary Λ A).image (Sym2.map Subtype.val)).card :=
      (Finset.card_image_of_injective _ (Sym2.map.injective Subtype.val_injective)).symm
    _ ≤ ((R.image Subtype.val).biUnion E).card := Finset.card_le_card hsub
    _ ≤ (R.image Subtype.val).card * 4 :=
      Finset.card_biUnion_le_card_mul _ _ _ (fun p _ ↦ hE p)
    _ ≤ R.card * 4 := Nat.mul_le_mul_right _ Finset.card_image_le
    _ = 4 * R.card := Nat.mul_comm _ _

/-- Each physical site contributes at most four crossing edges. -/
theorem card_edgeBoundary_le_four_mul_card (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) :
    (edgeBoundary Λ A).card ≤ 4 * A.card :=
  card_edgeBoundary_le_of_endpoint_cover Λ A A (fun _ hx _ _ _ ↦ Or.inl hx)

/-- A new crossing edge either was already crossing or crosses the changed-site set. -/
theorem edgeBoundary_subset_union_symmDiff (Λ : Finset (ℤ × ℤ))
    (A B : Finset (Site Λ)) :
    edgeBoundary Λ A ⊆ edgeBoundary Λ B ∪ edgeBoundary Λ (A ∆ B) := by
  classical
  rintro ⟨x, y⟩
  simp only [Finset.mem_union, mem_edgeBoundary_pair_iff, Finset.mem_symmDiff]
  tauto

/-- Changing sites raises the physical edge boundary by at most four per changed site.
Source: the last step of Lemma 9.1(2), `08-scanner.tex`, lines 254–257. -/
theorem card_edgeBoundary_le_add_four_mul_symmDiff (Λ : Finset (ℤ × ℤ))
    (A B : Finset (Site Λ)) :
    (edgeBoundary Λ A).card ≤ (edgeBoundary Λ B).card + 4 * (A ∆ B).card := by
  calc
    (edgeBoundary Λ A).card ≤
        (edgeBoundary Λ B ∪ edgeBoundary Λ (A ∆ B)).card :=
      Finset.card_le_card (edgeBoundary_subset_union_symmDiff Λ A B)
    _ ≤ (edgeBoundary Λ B).card + (edgeBoundary Λ (A ∆ B)).card := Finset.card_union_le _ _
    _ ≤ (edgeBoundary Λ B).card + 4 * (A ∆ B).card :=
      Nat.add_le_add_left (card_edgeBoundary_le_four_mul_card Λ (A ∆ B)) _

end TNLean.PEPS.AreaLaw
