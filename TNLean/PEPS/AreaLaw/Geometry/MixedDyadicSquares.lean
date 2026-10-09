/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.CappedDyadicPartition

/-!
# Mixed dyadic squares of finite unions and differences

Mixedness of the existing lattice dyadic cells is subadditive under finite
unions and differences. The witnesses are actual integer sites; no geometric
regularity or connectedness is assumed.

Original proofs from `scanner:mixed-piece`, lines 622–649 of `08-scanner.tex`,
OpenAI, *A two-dimensional area law from a global spectral gap*, September 24,
2026, at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
No upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Integer coordinate bounds for the existing half-open dyadic square. -/
theorem mem_latticeDyadicCell_iff_bounds (k : ℕ) (z x : ℤ × ℤ) :
    x ∈ latticeDyadicCell k z ↔
      z.1 * 2 ^ k ≤ x.1 ∧ x.1 < z.1 * 2 ^ k + 2 ^ k ∧
      z.2 * 2 ^ k ≤ x.2 ∧ x.2 < z.2 * 2 ^ k + 2 ^ k := by
  rcases z with ⟨a, b⟩
  rw [mem_latticeDyadicCell]
  simp only [dyadicAncestor, Prod.mk.injEq,
    Int.ediv_eq_iff_of_pos (show (0 : ℤ) < 2 ^ k by positivity)]
  tauto

/-- The empty set has no mixed dyadic squares. -/
@[simp] theorem mixedDyadicIndices_empty (k : ℕ) : mixedDyadicIndices ∅ k = ∅ := by
  simp [mixedDyadicIndices]

/-- A square mixed for a finite union is mixed for one of its constituents. -/
theorem mixedDyadicIndices_biUnion_subset {ι : Type*} (I : Finset ι)
    (S : ι → Finset (ℤ × ℤ)) (k : ℕ) :
    mixedDyadicIndices (I.biUnion S) k ⊆ I.biUnion (fun i ↦ mixedDyadicIndices (S i) k) := by
  classical
  intro z hz
  obtain ⟨⟨x, hx, hxin⟩, y, hy, hyout⟩ := (mem_mixedDyadicIndices _ _ _).mp hz
  obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hxin
  refine Finset.mem_biUnion.mpr ⟨i, hi, (mem_mixedDyadicIndices _ _ _).mpr ?_⟩
  exact ⟨⟨x, hx, hxi⟩, y, hy, fun h ↦ hyout (Finset.mem_biUnion.mpr ⟨i, hi, h⟩)⟩

/-- Mixed-square counts are subadditive over arbitrary finite unions. -/
theorem card_mixedDyadicIndices_biUnion_le {ι : Type*} (I : Finset ι)
    (S : ι → Finset (ℤ × ℤ)) (k : ℕ) :
    (mixedDyadicIndices (I.biUnion S) k).card ≤
      ∑ i ∈ I, (mixedDyadicIndices (S i) k).card :=
  (Finset.card_le_card (mixedDyadicIndices_biUnion_subset I S k)).trans
    Finset.card_biUnion_le

/-- A square mixed for a difference is mixed for at least one of the two sets. -/
theorem mixedDyadicIndices_sdiff_subset (S U : Finset (ℤ × ℤ)) (k : ℕ) :
    mixedDyadicIndices (S \ U) k ⊆ mixedDyadicIndices S k ∪ mixedDyadicIndices U k := by
  intro z hz
  obtain ⟨⟨x, hx, hxin⟩, y, hy, hyout⟩ := (mem_mixedDyadicIndices _ _ _).mp hz
  obtain ⟨hxS, hxU⟩ := Finset.mem_sdiff.mp hxin
  by_cases hyS : y ∈ S
  · have hyU : y ∈ U := by
      by_contra h
      exact hyout (Finset.mem_sdiff.mpr ⟨hyS, h⟩)
    exact Finset.mem_union_right _ ((mem_mixedDyadicIndices _ _ _).mpr
      ⟨⟨y, hy, hyU⟩, x, hx, hxU⟩)
  · exact Finset.mem_union_left _ ((mem_mixedDyadicIndices _ _ _).mpr
      ⟨⟨x, hx, hxS⟩, y, hy, hyS⟩)

/-- The mixed-square count of a difference is bounded by the sum of the counts. -/
theorem card_mixedDyadicIndices_sdiff_le (S U : Finset (ℤ × ℤ)) (k : ℕ) :
    (mixedDyadicIndices (S \ U) k).card ≤
      (mixedDyadicIndices S k).card + (mixedDyadicIndices U k).card :=
  (Finset.card_le_card (mixedDyadicIndices_sdiff_subset S U k)).trans
    (Finset.card_union_le _ _)

end TNLean.PEPS.AreaLaw.Geometry
