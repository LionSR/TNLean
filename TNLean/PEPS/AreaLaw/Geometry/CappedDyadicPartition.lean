/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.DyadicRefinement
import Mathlib.Data.Nat.Find

/-!
# Capped maximal-contained dyadic partitions

For every finite subset of the integer lattice, the contained dyadic squares
whose parents are not contained, together with the contained squares at a fixed
cap, form a partition. Coverage, disjointness, cardinality and mixed-parent
association are conclusions. No connectedness or nonemptiness is required.

The cells are the lattice sites of the existing origin-zero dyadic grid,
expressed by its refinement operation. This is the finite geometric partition
step of the shell argument, not the mixed-square estimate, safe clearance or
entropy conclusion of Lemma 9.4.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Section 9, `scanner:templates`, lines 641–649.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript:
  preprints/
  A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
  build/sections/08-scanner.tex
Labels: scanner:templates, scanner:mixed-piece.
Provenance-ID: 8754-tnlean.peps.arealaw.geometry.latticedyadiccell
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.latticeDyadicCell
Provenance-ID: 8754-tnlean.peps.arealaw.geometry.dyadicancestor_eq_cellindex
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.dyadicAncestor_eq_cellIndex
Provenance-ID: 8754-tnlean.peps.arealaw.geometry.mem_latticedyadiccell
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.mem_latticeDyadicCell
Provenance-ID: 8754-tnlean.peps.arealaw.geometry.mem_latticedyadiccell_iff_mem_cell
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.mem_latticeDyadicCell_iff_mem_cell
Provenance-ID: 8754-tnlean.peps.arealaw.geometry.card_latticedyadiccell
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.card_latticeDyadicCell
Provenance-ID: 8754-tnlean.peps.arealaw.geometry.latticedyadiccell_zero
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.latticeDyadicCell_zero
Provenance-ID: 8754-tnlean.peps.arealaw.geometry.latticedyadiccell_subset_of_common_mem
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.latticeDyadicCell_subset_of_common_mem
Provenance-ID: 8754-tnlean.peps.arealaw.geometry.latticedyadiccell_subset_parent
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.latticeDyadicCell_subset_parent
Provenance-ID: 8754-tnlean.peps.arealaw.geometry.cappeddyadicpartition
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.cappedDyadicPartition
Provenance-ID: 8754-tnlean.peps.arealaw.geometry.mem_cappeddyadicpartition
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.mem_cappedDyadicPartition
Provenance-ID: 8754-tnlean.peps.arealaw.geometry.exists_mem_cappeddyadicpartition
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.exists_mem_cappedDyadicPartition
Provenance-ID: 8754-tnlean.peps.arealaw.geometry.biunion_cappeddyadicpartition
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.biUnion_cappedDyadicPartition
Provenance-ID: 8754-tnlean.peps.arealaw.geometry.pairwisedisjoint_cappeddyadicpartition
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.pairwiseDisjoint_cappedDyadicPartition
Provenance-ID: 8754-tnlean.peps.arealaw.geometry.sum_card_cappeddyadicpartition
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.sum_card_cappedDyadicPartition
Provenance-ID: 8754-tnlean.peps.arealaw.geometry.sum_pow_cappeddyadicpartition
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.sum_pow_cappedDyadicPartition
Provenance-ID: 8754-tnlean.peps.arealaw.geometry.card_cappeddyadicpartition_at_cap_le
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.card_cappedDyadicPartition_at_cap_le
Provenance-ID: 8754-tnlean.peps.arealaw.geometry.mixeddyadicindices
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.mixedDyadicIndices
Provenance-ID: 8754-tnlean.peps.arealaw.geometry.mem_mixeddyadicindices
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.mem_mixedDyadicIndices
Provenance-ID: 8754-tnlean.peps.arealaw.geometry.parent_mem_mixeddyadicindices
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.parent_mem_mixedDyadicIndices
Provenance-ID: 8754-tnlean.peps.arealaw.geometry.cappeddyadicpartition_subset_mixed_refinement
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.cappedDyadicPartition_subset_mixed_refinement
Provenance-ID: 8754-tnlean.peps.arealaw.geometry.card_cappeddyadicpartition_below_cap_le
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.card_cappedDyadicPartition_below_cap_le
Provenance-ID: 8754-tnlean.peps.arealaw.geometry.cappeddyadicpartition_empty
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.cappedDyadicPartition_empty
Provenance-ID: 8754-tnlean.peps.arealaw.geometry.cappeddyadicpartition_zero
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.cappedDyadicPartition_zero
-/

open scoped BigOperators

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The lattice sites of an origin-zero dyadic square, obtained by refining its
index down to unit scale. Source: `scanner:templates`, lines 641–649. -/
def latticeDyadicCell (k : ℕ) (z : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  dyadicRefinement {z} k

/-- Integer ancestry agrees with the existing real floor-index convention,
including negative coordinates. -/
theorem dyadicAncestor_eq_cellIndex (k : ℕ) (x : ℤ × ℤ) :
    dyadicAncestor k x = dyadicCellIndex (0, 0) k (x.1, x.2) := by
  simpa [dyadicCellIndex] using
    dyadicCellIndex_of_le (0, 0) 0 k (x.1, x.2) (Nat.zero_le k)

/-- Membership in a lattice square is exactly the existing dyadic ancestry. -/
@[simp] theorem mem_latticeDyadicCell (k : ℕ) (z x : ℤ × ℤ) :
    x ∈ latticeDyadicCell k z ↔ dyadicAncestor k x = z := by
  simp [latticeDyadicCell, mem_dyadicRefinement_iff]

/-- These finite cells are precisely the integer sites of the existing real cells. -/
theorem mem_latticeDyadicCell_iff_mem_cell (k : ℕ) (z x : ℤ × ℤ) :
    x ∈ latticeDyadicCell k z ↔ ((x.1 : ℝ), (x.2 : ℝ)) ∈ dyadicCell (0, 0) k z := by
  rw [mem_latticeDyadicCell, mem_dyadicCell_iff, dyadicAncestor_eq_cellIndex]

/-- A side-`2^k` square has `4^k` lattice sites. -/
@[simp] theorem card_latticeDyadicCell (k : ℕ) (z : ℤ × ℤ) :
    (latticeDyadicCell k z).card = 4 ^ k := by
  simp [latticeDyadicCell, card_dyadicRefinement]

private theorem latticeDyadicCell_nonempty (k : ℕ) (z : ℤ × ℤ) :
    (latticeDyadicCell k z).Nonempty := by
  rw [← Finset.card_pos, card_latticeDyadicCell]
  positivity

/-- Unit squares are singletons. -/
@[simp] theorem latticeDyadicCell_zero (z : ℤ × ℤ) :
    latticeDyadicCell 0 z = {z} := by
  ext x
  simp [dyadicAncestor]

private theorem ancestor_succ (k : ℕ) (x : ℤ × ℤ) :
    dyadicAncestor (k + 1) x = dyadicParent (dyadicAncestor k x) := by
  simp only [dyadicAncestor_eq_cellIndex, dyadicCellIndex_succ]

private theorem ancestor_of_le (k l : ℕ) (x : ℤ × ℤ) (h : k ≤ l) :
    dyadicAncestor (l - k) (dyadicAncestor k x) = dyadicAncestor l x := by
  rw [dyadicAncestor_eq_cellIndex k, dyadicAncestor_eq_cellIndex l]
  exact dyadicCellIndex_of_le _ _ _ _ h

/-- Intersecting dyadic squares are nested in the order of their scales. -/
theorem latticeDyadicCell_subset_of_common_mem {k l : ℕ} {u v x : ℤ × ℤ}
    (hkl : k ≤ l) (hx : x ∈ latticeDyadicCell k u)
    (hy : x ∈ latticeDyadicCell l v) : latticeDyadicCell k u ⊆ latticeDyadicCell l v := by
  simp only [Finset.subset_iff, mem_latticeDyadicCell] at hx hy ⊢
  intro y hyu
  rw [← ancestor_of_le k l y hkl, hyu, ← hx, ancestor_of_le k l x hkl, hy]

/-- Every lattice square is contained in its parent. -/
theorem latticeDyadicCell_subset_parent (k : ℕ) (z : ℤ × ℤ) :
    latticeDyadicCell k z ⊆ latticeDyadicCell (k + 1) (dyadicParent z) := by
  intro x hx
  rw [mem_latticeDyadicCell, ancestor_succ, (mem_latticeDyadicCell k z x).mp hx]

/-- Contained squares up to scale `K`, maximal unless they are at the cap.
Source: `scanner:templates`, lines 641–649. -/
def cappedDyadicPartition (S : Finset (ℤ × ℤ)) (K : ℕ) : Finset (ℕ × (ℤ × ℤ)) :=
  ((Finset.range (K + 1)).biUnion fun k ↦
    (S.image (dyadicAncestor k)).image (Prod.mk k)).filter fun c ↦
      latticeDyadicCell c.1 c.2 ⊆ S ∧
        (c.1 = K ∨ ¬latticeDyadicCell (c.1 + 1) (dyadicParent c.2) ⊆ S)

/-- Selection is characterized by containment and a failed parent below the cap;
occupancy follows from containment and the nonemptiness of every square. -/
theorem mem_cappedDyadicPartition (S : Finset (ℤ × ℤ)) (K k : ℕ) (z : ℤ × ℤ) :
    (k, z) ∈ cappedDyadicPartition S K ↔
      k ≤ K ∧ latticeDyadicCell k z ⊆ S ∧
        (k = K ∨ ¬latticeDyadicCell (k + 1) (dyadicParent z) ⊆ S) := by
  constructor
  · intro h
    obtain ⟨h, hs, hp⟩ := Finset.mem_filter.mp h
    obtain ⟨l, hl, h⟩ := Finset.mem_biUnion.mp h
    obtain ⟨u, hu, he⟩ := Finset.mem_image.mp h
    have hlk : l = k := congrArg Prod.fst he
    subst l
    exact ⟨by simpa using hl, hs, hp⟩
  · rintro ⟨hk, hs, hp⟩
    obtain ⟨x, hx⟩ := latticeDyadicCell_nonempty k z
    refine Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨k, ?_, ?_⟩, hs, hp⟩
    · exact Finset.mem_range.mpr (by omega)
    · exact Finset.mem_image.mpr ⟨z, Finset.mem_image.mpr
        ⟨x, hs hx, (mem_latticeDyadicCell k z x).mp hx⟩, rfl⟩

/-- Every site of `S` lies in a selected square, by taking its largest contained
scale up to the cap. Source: `scanner:templates`, lines 641–644. -/
theorem exists_mem_cappedDyadicPartition (S : Finset (ℤ × ℤ)) (K : ℕ)
    {x : ℤ × ℤ} (hx : x ∈ S) :
    ∃ c ∈ cappedDyadicPartition S K, x ∈ latticeDyadicCell c.1 c.2 := by
  let P : ℕ → Prop := fun k ↦ latticeDyadicCell k (dyadicAncestor k x) ⊆ S
  have hzero : P 0 := by simpa [P, dyadicAncestor] using hx
  let k := Nat.findGreatest P K
  have hk : k ≤ K := Nat.findGreatest_le K
  have hs : P k := Nat.findGreatest_spec (Nat.zero_le K) hzero
  refine ⟨(k, dyadicAncestor k x), ?_, by simp⟩
  rw [mem_cappedDyadicPartition]
  refine ⟨hk, hs, ?_⟩
  by_cases he : k = K
  · exact Or.inl he
  · right
    have hp : ¬P (k + 1) :=
      Nat.findGreatest_is_greatest (n := K) (Nat.lt_succ_self k) (by omega)
    simpa only [P, ancestor_succ] using hp

/-- The selected squares cover exactly the given finite set. -/
theorem biUnion_cappedDyadicPartition (S : Finset (ℤ × ℤ)) (K : ℕ) :
    (cappedDyadicPartition S K).biUnion (fun c ↦ latticeDyadicCell c.1 c.2) = S := by
  ext x
  constructor
  · intro hx
    obtain ⟨⟨k, z⟩, hc, hx⟩ := Finset.mem_biUnion.mp hx
    exact ((mem_cappedDyadicPartition S K k z).mp hc).2.1 hx
  · exact fun hx ↦ Finset.mem_biUnion.mpr (exists_mem_cappedDyadicPartition S K hx)

private theorem selected_scale_eq_of_le {S : Finset (ℤ × ℤ)} {K k l : ℕ}
    {u v x : ℤ × ℤ} (hu : (k, u) ∈ cappedDyadicPartition S K)
    (hv : (l, v) ∈ cappedDyadicPartition S K)
    (hx : x ∈ latticeDyadicCell k u) (hy : x ∈ latticeDyadicCell l v)
    (hkl : k ≤ l) : k = l := by
  obtain ⟨hk, _, hp⟩ := (mem_cappedDyadicPartition S K k u).mp hu
  obtain ⟨hl, hs, _⟩ := (mem_cappedDyadicPartition S K l v).mp hv
  by_contra hne
  have hlt : k < l := lt_of_le_of_ne hkl hne
  have hparent := latticeDyadicCell_subset_parent k u hx
  have hsub := latticeDyadicCell_subset_of_common_mem (by omega : k + 1 ≤ l) hparent hy
  rcases hp with hp | hp
  · omega
  · exact hp (hsub.trans hs)

/-- Distinct selected squares are disjoint, including at unequal scales. -/
theorem pairwiseDisjoint_cappedDyadicPartition (S : Finset (ℤ × ℤ)) (K : ℕ) :
    (cappedDyadicPartition S K : Set (ℕ × (ℤ × ℤ))).PairwiseDisjoint
      (fun c ↦ latticeDyadicCell c.1 c.2) := by
  intro a ha b hb hab
  apply Finset.disjoint_left.mpr
  intro x hxa hxb
  have hk : a.1 = b.1 := by
    rcases le_total a.1 b.1 with h | h
    · exact selected_scale_eq_of_le ha hb hxa hxb h
    · exact (selected_scale_eq_of_le hb ha hxb hxa h).symm
  have hz : a.2 = b.2 := by
    rw [mem_latticeDyadicCell] at hxa hxb
    rw [hk] at hxa
    exact hxa.symm.trans hxb
  exact hab (Prod.ext hk hz)

/-- The sum of the actual selected square cardinalities is exactly `|S|`. -/
theorem sum_card_cappedDyadicPartition (S : Finset (ℤ × ℤ)) (K : ℕ) :
    ∑ c ∈ cappedDyadicPartition S K, (latticeDyadicCell c.1 c.2).card = S.card := by
  rw [← Finset.card_biUnion (pairwiseDisjoint_cappedDyadicPartition S K),
    biUnion_cappedDyadicPartition]

/-- Equivalently, the sum of `4^k` over selected squares is exactly `|S|`. -/
theorem sum_pow_cappedDyadicPartition (S : Finset (ℤ × ℤ)) (K : ℕ) :
    ∑ c ∈ cappedDyadicPartition S K, 4 ^ c.1 = S.card := by
  simpa using sum_card_cappedDyadicPartition S K

/-- The number of cap-scale squares times their area is at most the total area.
This includes cap zero and the empty set. -/
theorem card_cappedDyadicPartition_at_cap_le (S : Finset (ℤ × ℤ)) (K : ℕ) :
    4 ^ K * ((cappedDyadicPartition S K).filter (fun c ↦ c.1 = K)).card ≤ S.card := by
  calc
    _ = ∑ _c ∈ (cappedDyadicPartition S K).filter (fun c ↦ c.1 = K), 4 ^ K := by
      simp [Nat.mul_comm]
    _ = ∑ c ∈ (cappedDyadicPartition S K).filter (fun c ↦ c.1 = K), 4 ^ c.1 :=
      Finset.sum_congr rfl fun c hc ↦ by rw [(Finset.mem_filter.mp hc).2]
    _ ≤ ∑ c ∈ cappedDyadicPartition S K, 4 ^ c.1 :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = S.card := sum_pow_cappedDyadicPartition S K

/-- Indices of squares with both a site in `S` and a site outside `S`.
Source: `scanner:mixed-piece` and `scanner:templates`, lines 622–649. -/
def mixedDyadicIndices (S : Finset (ℤ × ℤ)) (k : ℕ) : Finset (ℤ × ℤ) :=
  (S.image (dyadicAncestor k)).filter fun z ↦ ¬latticeDyadicCell k z ⊆ S

/-- Mixedness asserts actual inside and outside sites in the square. -/
theorem mem_mixedDyadicIndices (S : Finset (ℤ × ℤ)) (k : ℕ) (z : ℤ × ℤ) :
    z ∈ mixedDyadicIndices S k ↔
      (∃ x ∈ latticeDyadicCell k z, x ∈ S) ∧
        ∃ y ∈ latticeDyadicCell k z, y ∉ S := by
  simp only [mixedDyadicIndices, Finset.mem_filter, Finset.mem_image,
    Finset.subset_iff, not_forall, mem_latticeDyadicCell]
  aesop

/-- Below the cap, every selected square has a mixed parent. Both the inside
site and the failure of parent containment follow from selection. -/
theorem parent_mem_mixedDyadicIndices {S : Finset (ℤ × ℤ)} {K k : ℕ} {z : ℤ × ℤ}
    (hz : (k, z) ∈ cappedDyadicPartition S K) (hk : k < K) :
    dyadicParent z ∈ mixedDyadicIndices S (k + 1) := by
  obtain ⟨_, hs, hp⟩ := (mem_cappedDyadicPartition S K k z).mp hz
  have hp' : ¬latticeDyadicCell (k + 1) (dyadicParent z) ⊆ S :=
    hp.resolve_left (by omega)
  obtain ⟨x, hx⟩ := latticeDyadicCell_nonempty k z
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_image.mpr ⟨x, hs hx, ?_⟩, hp'⟩
  exact (mem_latticeDyadicCell _ _ _).mp (latticeDyadicCell_subset_parent k z hx)

/-- Selected indices at any scale strictly below the cap are children of mixed
parents in the existing refinement operation. -/
theorem cappedDyadicPartition_subset_mixed_refinement (S : Finset (ℤ × ℤ))
    (K k : ℕ) (hk : k < K) :
    ((cappedDyadicPartition S K).filter (fun c ↦ c.1 = k)).image Prod.snd ⊆
      dyadicRefinement (mixedDyadicIndices S (k + 1)) 1 := by
  rintro z hz
  obtain ⟨⟨l, u⟩, hu, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨hu, hscale⟩ := Finset.mem_filter.mp hu
  dsimp at hscale ⊢
  subst l
  rw [mem_dyadicRefinement_iff]
  simpa [dyadicAncestor, dyadicParent] using parent_mem_mixedDyadicIndices hu hk

/-- There are at most four selected squares per mixed parent below the cap. -/
theorem card_cappedDyadicPartition_below_cap_le (S : Finset (ℤ × ℤ))
    (K k : ℕ) (hk : k < K) :
    ((cappedDyadicPartition S K).filter (fun c ↦ c.1 = k)).card ≤
      4 * (mixedDyadicIndices S (k + 1)).card := by
  have hinj : Set.InjOn Prod.snd
      (↑((cappedDyadicPartition S K).filter (fun c ↦ c.1 = k)) : Set (ℕ × (ℤ × ℤ))) := by
    intro a ha b hb hab
    exact Prod.ext ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm) hab
  calc
    _ = (((cappedDyadicPartition S K).filter (fun c ↦ c.1 = k)).image Prod.snd).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (dyadicRefinement (mixedDyadicIndices S (k + 1)) 1).card :=
      Finset.card_le_card (cappedDyadicPartition_subset_mixed_refinement S K k hk)
    _ = _ := by simp [card_dyadicRefinement]

/-- The empty set has no selected squares, for every cap. -/
@[simp] theorem cappedDyadicPartition_empty (K : ℕ) : cappedDyadicPartition ∅ K = ∅ := by
  simp [cappedDyadicPartition]

/-- At cap zero the partition consists exactly of the singleton sites. -/
@[simp] theorem cappedDyadicPartition_zero (S : Finset (ℤ × ℤ)) :
    cappedDyadicPartition S 0 = S.image (fun x ↦ (0, x)) := by
  ext ⟨k, z⟩
  simp only [mem_cappedDyadicPartition, Nat.le_zero, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨rfl, hs, _⟩
    exact ⟨z, hs (by simp), rfl, rfl⟩
  · rintro ⟨x, hx, hk, rfl⟩
    subst k
    simp [hx]

end TNLean.PEPS.AreaLaw.Geometry
