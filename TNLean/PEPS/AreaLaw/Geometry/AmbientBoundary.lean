/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.TemplateRows

/-!
# Unordered ambient lattice boundaries

The ambient boundary uses the existing induced-domain edge boundary on the
one-step ambient dilation. Mapping subtype endpoints back to lattice points
preserves each unordered edge and its cardinality. Four neighbors per lattice
point give boundary estimates from either endpoint of each crossing edge.

Original formalization of the geometric argument in manuscript Lemma 9.4;
no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw

/-- The four nearest neighbors of an integer lattice point. -/
def latticeNeighbors (p : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  {(p.1 + 1, p.2), (p.1 - 1, p.2), (p.1, p.2 + 1), (p.1, p.2 - 1)}

/-- Neighbor membership agrees with the coordinate convention of `domainGraph`. -/
theorem mem_latticeNeighbors_iff {p q : ℤ × ℤ} :
    q ∈ latticeNeighbors p ↔
      (p.2 = q.2 ∧ (p.1 + 1 = q.1 ∨ q.1 + 1 = p.1)) ∨
      (p.1 = q.1 ∧ (p.2 + 1 = q.2 ∨ q.2 + 1 = p.2)) := by
  simp only [latticeNeighbors, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
  omega

/-- Nearest-neighbor incidence is symmetric. -/
theorem latticeNeighbors_symm {p q : ℤ × ℤ} (h : q ∈ latticeNeighbors p) :
    p ∈ latticeNeighbors q := by
  rw [mem_latticeNeighbors_iff] at h ⊢
  omega

/-- Every lattice site has at most four nearest neighbors. -/
theorem card_latticeNeighbors_le (p : ℤ × ℤ) : (latticeNeighbors p).card ≤ 4 :=
  Finset.card_le_four

/-- Taking one nearest-neighbor step increases the ambient radius by at most one. -/
theorem neighbor_mem_ambientDilation_succ {S : Finset (ℤ × ℤ)} {r : ℕ}
    {p q : ℤ × ℤ} (hp : p ∈ ambientDilation S r) (hq : q ∈ latticeNeighbors p) :
    q ∈ ambientDilation S (r + 1) := by
  obtain ⟨a, ha, hp⟩ := mem_ambientDilation_iff.mp hp
  have hq' := mem_latticeNeighbors_iff.mp hq
  exact mem_ambientDilation_iff.mpr ⟨a, ha, by omega⟩

/-- The finite-domain representative of an ambient region in its one-step dilation. -/
def ambientBoundaryRegion (S : Finset (ℤ × ℤ)) :
    Finset (Site (ambientDilation S 1)) :=
  Finset.univ.filter fun p ↦ p.1 ∈ S

/-- The actual unordered nearest-neighbor boundary in the infinite lattice,
computed in a finite enclosure containing every crossing edge.
Source: Lemma 9.4, the ambient boundary of the template dilations. -/
noncomputable def ambientBoundary (S : Finset (ℤ × ℤ)) : Finset (Sym2 (ℤ × ℤ)) :=
  (edgeBoundary (ambientDilation S 1) (ambientBoundaryRegion S)).image
    (Sym2.map Subtype.val)

/-- Mapping endpoints back to the lattice neither identifies nor duplicates edges. -/
theorem card_ambientBoundary (S : Finset (ℤ × ℤ)) :
    (ambientBoundary S).card =
      (edgeBoundary (ambientDilation S 1) (ambientBoundaryRegion S)).card := by
  classical
  exact Finset.card_image_of_injective _ (Sym2.map.injective Subtype.val_injective)

/-- Exact crossing membership, with the inside endpoint first. No edge of the
infinite lattice crossing the region is lost by the finite enclosure. -/
theorem mem_ambientBoundary_iff {S : Finset (ℤ × ℤ)} {e : Sym2 (ℤ × ℤ)} :
    e ∈ ambientBoundary S ↔
      ∃ p ∈ S, ∃ q ∉ S, q ∈ latticeNeighbors p ∧ e = s(p, q) := by
  classical
  constructor
  · intro he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hf, p, hp, q, hq, rfl⟩ := Finset.mem_filter.mp hf
    simp only [ambientBoundaryRegion, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    have hadj : (domainGraph (ambientDilation S 1)).Adj p q := by
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hf
    exact ⟨p.1, hp, q.1, hq, mem_latticeNeighbors_iff.mpr hadj, rfl⟩
  · rintro ⟨p, hp, q, hq, hpq, rfl⟩
    have hpD : p ∈ ambientDilation S 1 :=
      mem_ambientDilation_iff.mpr ⟨p, hp, by omega⟩
    have hqD : q ∈ ambientDilation S 1 := by
      exact neighbor_mem_ambientDilation_succ (r := 0)
        (by simpa only [ambientDilation_zero] using hp) hpq
    let a : Site (ambientDilation S 1) := ⟨p, hpD⟩
    let b : Site (ambientDilation S 1) := ⟨q, hqD⟩
    refine Finset.mem_image.mpr ⟨s(a, b), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply SimpleGraph.mem_edgeFinset.mpr
      change (domainGraph (ambientDilation S 1)).Adj a b
      exact mem_latticeNeighbors_iff.mp hpq
    · exact ⟨a, by simpa [ambientBoundaryRegion, a] using hp,
        b, by simpa [ambientBoundaryRegion, b] using hq, rfl⟩

/-- The inside/outside orientation of an unordered crossing edge is unique. -/
theorem ambientBoundary_orientation_unique {S : Finset (ℤ × ℤ)}
    {p q p' q' : ℤ × ℤ} (hp : p ∈ S)
    (hq' : q' ∉ S) (h : s(p, q) = s(p', q')) :
    p = p' ∧ q = q' := by
  rcases Sym2.eq_iff.mp h with h | h
  · exact h
  · exact (hq' (h.1 ▸ hp)).elim

/-- The empty ambient region has no crossing edges. -/
@[simp] theorem ambientBoundary_empty : ambientBoundary ∅ = ∅ := by
  ext e
  simp [mem_ambientBoundary_iff]

/-- A set meeting every crossing edge bounds the boundary by four times its size. -/
theorem card_ambientBoundary_le_of_endpoint_cover (S R : Finset (ℤ × ℤ))
    (hR : ∀ p ∈ S, ∀ q ∉ S, q ∈ latticeNeighbors p → p ∈ R ∨ q ∈ R) :
    (ambientBoundary S).card ≤ 4 * R.card := by
  classical
  let E (p : ℤ × ℤ) := (latticeNeighbors p).image fun q ↦ s(p, q)
  have hE (p : ℤ × ℤ) : (E p).card ≤ 4 :=
    Finset.card_image_le.trans (card_latticeNeighbors_le p)
  have hsub : ambientBoundary S ⊆ R.biUnion E := by
    intro e he
    obtain ⟨p, hp, q, hq, hpq, rfl⟩ := mem_ambientBoundary_iff.mp he
    rcases hR p hp q hq hpq with hpR | hqR
    · exact Finset.mem_biUnion.mpr ⟨p, hpR, Finset.mem_image.mpr ⟨q, hpq, rfl⟩⟩
    · exact Finset.mem_biUnion.mpr
        ⟨q, hqR, Finset.mem_image.mpr ⟨p, latticeNeighbors_symm hpq, Sym2.eq_swap⟩⟩
  calc
    (ambientBoundary S).card ≤ (R.biUnion E).card := Finset.card_le_card hsub
    _ ≤ R.card * 4 := Finset.card_biUnion_le_card_mul _ _ _ (fun p _ ↦ hE p)
    _ = 4 * R.card := Nat.mul_comm _ _

/-- Every outer endpoint lies in the first ambient layer. This estimate includes
empty and disconnected regions without any regularity condition. -/
theorem card_ambientBoundary_le_outer_layer (S : Finset (ℤ × ℤ)) :
    (ambientBoundary S).card ≤ 4 * (ambientDilation S 1 \ S).card := by
  apply card_ambientBoundary_le_of_endpoint_cover
  intro p hp q hq hpq
  right
  apply Finset.mem_sdiff.mpr
  refine ⟨?_, hq⟩
  exact neighbor_mem_ambientDilation_succ (r := 0)
    (by simpa only [ambientDilation_zero] using hp) hpq

/-- At positive radius, every crossing edge has its inside endpoint in the
current dilation layer. No estimate at the next radius is used. -/
theorem card_ambientBoundary_dilation_le_layer (S : Finset (ℤ × ℤ))
    (j : ℕ) (hj : 1 ≤ j) :
    (ambientBoundary (ambientDilation S j)).card ≤
      4 * (ambientDilation S j \ ambientDilation S (j - 1)).card := by
  apply card_ambientBoundary_le_of_endpoint_cover
  intro p hp q hq hpq
  left
  refine Finset.mem_sdiff.mpr ⟨hp, ?_⟩
  intro hpold
  have h := neighbor_mem_ambientDilation_succ hpold hpq
  have hj' : j - 1 + 1 = j := by omega
  exact hq (hj' ▸ h)

/-- A crossing edge of a set difference crosses at least one of the two sets. -/
theorem ambientBoundary_sdiff_subset (S U : Finset (ℤ × ℤ)) :
    ambientBoundary (S \ U) ⊆ ambientBoundary S ∪ ambientBoundary U := by
  intro e he
  obtain ⟨p, hp, q, hq, hpq, rfl⟩ := mem_ambientBoundary_iff.mp he
  obtain ⟨hpS, hpU⟩ := Finset.mem_sdiff.mp hp
  by_cases hqS : q ∈ S
  · have hqU : q ∈ U := by
      by_contra hn
      exact hq (Finset.mem_sdiff.mpr ⟨hqS, hn⟩)
    apply Finset.mem_union_right
    exact mem_ambientBoundary_iff.mpr
      ⟨q, hqU, p, hpU, latticeNeighbors_symm hpq, Sym2.eq_swap⟩
  · exact Finset.mem_union_left _
      (mem_ambientBoundary_iff.mpr ⟨p, hpS, q, hqS, hpq, rfl⟩)

/-- Ambient edge boundary is subadditive under set difference. -/
theorem card_ambientBoundary_sdiff_le (S U : Finset (ℤ × ℤ)) :
    (ambientBoundary (S \ U)).card ≤ (ambientBoundary S).card + (ambientBoundary U).card :=
  (Finset.card_le_card (ambientBoundary_sdiff_subset S U)).trans (Finset.card_union_le _ _)

end TNLean.PEPS.AreaLaw
