/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.DyadicExhaustion
import TNLean.PEPS.AreaLaw.Geometry.DyadicRefinement
import Mathlib.Data.Nat.Find
import Mathlib.Order.Monotone.Basic

/-!
# The actual half-open layer partition

Every actual indexed fine cell belongs to its layer. The nested dyadic
neighborhoods determine pairwise disjoint successive layers.
For any lower index, its initial neighborhood is disjoint from all later
layers. When the endpoint set is nonempty and the radius is at least two,
every point outside that neighborhood belongs to exactly one later layer.
The neighborhood and these layers therefore cover the plane.

These conclusions concern the actual half-open sets. Their closures may meet;
no disjointness of closed birth regions is asserted.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `prop:two-families`, lines 154–181.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript:
  preprints/
  A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
  build/
  sections/
  10-geometry.tex
Labels: prop:two-families.
Source lines: 154–181.
Source revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.dyadiclayer_pairwisedisjoint
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.dyadicLayer_pairwiseDisjoint
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.dyadicneighborhood_disjoint_later_layer
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.dyadicNeighborhood_disjoint_later_layer
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.exists_unique_layer_of_not_mem_dyadicneighborhood
Downstream declaration:
  TNLean.PEPS.AreaLaw.Geometry.exists_unique_layer_of_not_mem_dyadicNeighborhood
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.dyadicneighborhood_union_iunion_layers_eq_univ
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.dyadicNeighborhood_union_iUnion_layers_eq_univ
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.dyadiccell_containment
Downstream declaration:
  TNLean.PEPS.AreaLaw.Geometry.dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices
-/


namespace TNLean.PEPS.AreaLaw.Geometry

/-- An actual indexed fine cell is contained in its layer.
Source: area-law Section 11, `prop:two-families`, lines 154–160 and 173–181. -/
theorem dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices
    (o : ℝ × ℝ) (k ℓ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ) (z : ℤ × ℤ)
    (hℓk : ℓ ≤ k) (hz : z ∈ fineLayerIndices o k ℓ Z C) :
    dyadicCell o ℓ z ⊆ dyadicLayer o k Z C := by
  intro x hx
  rw [dyadicLayer_eq_iUnion_fine o k ℓ Z C hℓk]
  exact Set.mem_iUnion₂.mpr ⟨z, hz, hx⟩

private theorem neighborhood_mono (o : ℝ × ℝ) (Z : Finset (ℤ × ℤ)) (C : ℕ) :
    Monotone (fun k ↦ dyadicNeighborhood o k Z C) :=
  monotone_nat_of_le_succ (fun k ↦ dyadicNeighborhood_subset_succ o k Z C)

/-- The actual half-open layers are pairwise disjoint, including for empty endpoint sets.
Source: area-law Section 11, `prop:two-families`, lines 160–177. -/
theorem dyadicLayer_pairwiseDisjoint (o : ℝ × ℝ) (Z : Finset (ℤ × ℤ)) (C : ℕ) :
    Pairwise (fun k h : ℕ ↦ Disjoint (dyadicLayer o k Z C) (dyadicLayer o h Z C)) := by
  have hdisj (k h : ℕ) (hkh : k < h) :
      Disjoint (dyadicLayer o k Z C) (dyadicLayer o h Z C) := by
    refine Set.disjoint_left.mpr ?_
    intro x hx hy
    exact hy.2 (neighborhood_mono o Z C (Nat.succ_le_of_lt hkh) hx.1)
  intro k h hne
  rcases lt_or_gt_of_ne hne with hkh | hhk
  · exact hdisj k h hkh
  · exact (hdisj h k hhk).symm

/-- The initial dummy neighborhood is disjoint from every layer above its lower index.
Source: area-law Section 11, `prop:two-families`, lines 169–177. -/
theorem dyadicNeighborhood_disjoint_later_layer (o : ℝ × ℝ)
    (Z : Finset (ℤ × ℤ)) (C k₀ k : ℕ) (hk : k₀ ≤ k) :
    Disjoint (dyadicNeighborhood o k₀ Z C) (dyadicLayer o k Z C) := by
  refine Set.disjoint_left.mpr ?_
  intro x hx hy
  exact hy.2 (neighborhood_mono o Z C hk hx)

/-- Outside the initial dummy neighborhood there is a unique actual later layer.
Source: area-law Section 11, `prop:two-families`, lines 160–177. -/
theorem exists_unique_layer_of_not_mem_dyadicNeighborhood (o : ℝ × ℝ)
    (Z : Finset (ℤ × ℤ)) (C k₀ : ℕ) (hZ : Z.Nonempty) (hC : 2 ≤ C)
    (x : ℝ × ℝ) (hx : x ∉ dyadicNeighborhood o k₀ Z C) :
    ∃! k : ℕ, k₀ ≤ k ∧ x ∈ dyadicLayer o k Z C := by
  classical
  have hex := exists_mem_dyadicNeighborhood o Z C hZ hC x
  let K := Nat.find hex
  have hxK : x ∈ dyadicNeighborhood o K Z C := Nat.find_spec hex
  have hk₀K : k₀ < K := by
    by_contra! h
    exact hx (neighborhood_mono o Z C h hxK)
  have hprev : x ∉ dyadicNeighborhood o (K - 1) Z C :=
    Nat.find_min hex (by dsimp [K] at hk₀K ⊢; omega)
  have hmem : x ∈ dyadicLayer o (K - 1) Z C := by
    change x ∈ dyadicNeighborhood o (K - 1 + 1) Z C ∧
      x ∉ dyadicNeighborhood o (K - 1) Z C
    have hK : K - 1 + 1 = K := by omega
    exact ⟨hK ▸ hxK, hprev⟩
  refine ⟨K - 1, ⟨by omega, hmem⟩, ?_⟩
  intro k hk
  by_contra hne
  exact (Set.disjoint_left.mp (dyadicLayer_pairwiseDisjoint o Z C hne)) hk.2 hmem

/-- The dummy neighborhood and all later actual layers cover the plane exactly.
Source: area-law Section 11, `prop:two-families`, lines 160–177. -/
theorem dyadicNeighborhood_union_iUnion_layers_eq_univ (o : ℝ × ℝ)
    (Z : Finset (ℤ × ℤ)) (C k₀ : ℕ) (hZ : Z.Nonempty) (hC : 2 ≤ C) :
    dyadicNeighborhood o k₀ Z C ∪ (⋃ k ≥ k₀, dyadicLayer o k Z C) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x ∈ dyadicNeighborhood o k₀ Z C
  · exact Set.mem_union_left _ hx
  · obtain ⟨k, hk, _⟩ :=
      exists_unique_layer_of_not_mem_dyadicNeighborhood o Z C k₀ hZ hC x hx
    exact Set.mem_union_right _ (Set.mem_iUnion₂.mpr ⟨k, hk.1, hk.2⟩)

end TNLean.PEPS.AreaLaw.Geometry
