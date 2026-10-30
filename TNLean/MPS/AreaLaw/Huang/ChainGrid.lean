/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Basic
import TNLean.MPS.AreaLaw.IntervalNeighborhoodEntropy

/-!
# Uniform blocks and disjoint boundary buffers on a chain

Blocks of width `w` cover the chain, with internal cuts at positive multiples of `w`.
The radius-`r` neighborhood of the pair adjacent to a cut is an interval of width at
most `2r+2`. When `2r+2 ≤ w`, these boundary buffers are pairwise disjoint. Every
nearest-neighbor edge is contained in one block or crosses one of the enumerated cuts.

These are the explicit support layouts used in the two-layer decomposition of Osborne,
arXiv:quant-ph/0508031v2, Figure 2, and the propagator approximation in Huang,
arXiv:1406.6355v6, Section 5.4, Lemma 19. No partition is supplied as a hypothesis.
-/

namespace TNLean.MPS.AreaLaw

/-- The `j`-th clipped block of a uniform grid. Osborne, Figure 2. -/
def chainGridBlock (L w j : ℕ) : Finset (Fin L) := interval L (j * w) ((j + 1) * w)

/-- The positive grid cut after the `k`-th block. Osborne, Figure 2. -/
def chainGridCut (w k : ℕ) : ℕ := (k + 1) * w

/-- The adjacent pair at a cut, written as a clipped interval. Osborne, Figure 1. -/
def chainCutPair (L cut : ℕ) : Finset (Fin L) := interval L (cut - 1) (cut + 1)

/-- The radius-`r` interval buffer around the adjacent pair at a cut. Osborne, Figure 2. -/
def chainCutBuffer (L cut r : ℕ) : Finset (Fin L) :=
  interval L (cut - 1 - r) (cut + r + 1)

/-- The block label of a site is its quotient by the grid width. Osborne, Figure 2. -/
def chainGridOwner {L : ℕ} (w : ℕ) (x : Fin L) : Fin (L / w + 1) :=
  ⟨x.val / w, Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt x.isLt))⟩

/-- Each grid block has at most `w` sites. Osborne, Figure 2. -/
theorem card_chainGridBlock_le (L w j : ℕ) : (chainGridBlock L w j).card ≤ w := by
  have h := card_interval_le (L := L) (j * w) ((j + 1) * w)
  simpa [chainGridBlock, Nat.add_mul] using h

/-- The nominal endpoint width of a block is exactly the grid width. Osborne, Figure 2. -/
theorem chainGridBlock_width (w j : ℕ) : (j + 1) * w - j * w = w := by
  simp [Nat.add_mul]

/-- The grid blocks are pairwise disjoint, including the possible empty last block.
Osborne, arXiv:quant-ph/0508031v2, Figure 2. -/
theorem pairwise_disjoint_chainGridBlock (L w : ℕ) :
    Pairwise (fun j k : ℕ ↦ Disjoint (chainGridBlock L w j) (chainGridBlock L w k)) := by
  intro j k hjk
  apply Finset.disjoint_left.mpr
  intro x hxj hxk
  rw [chainGridBlock, mem_interval] at hxj hxk
  rcases lt_or_gt_of_ne hjk with h | h
  · have hmul := Nat.mul_le_mul_right w (Nat.succ_le_of_lt h)
    simp only [Nat.succ_eq_add_one] at hmul
    omega
  · have hmul := Nat.mul_le_mul_right w (Nat.succ_le_of_lt h)
    simp only [Nat.succ_eq_add_one] at hmul
    omega

/-- Every site lies in its explicitly assigned block. Osborne, Figure 2. -/
theorem mem_chainGridBlock_owner {L w : ℕ} (hw : 0 < w) (x : Fin L) :
    x ∈ chainGridBlock L w (chainGridOwner w x).val := by
  rw [chainGridBlock, mem_interval]
  change x.val / w * w ≤ x.val ∧ x.val < (x.val / w + 1) * w
  have hdiv := Nat.div_add_mod x.val w
  have hmod := Nat.mod_lt x.val hw
  exact ⟨Nat.div_mul_le_self _ _, by nlinarith⟩

/-- The finite list of block labels covers the chain. Osborne, Figure 2. -/
theorem iUnion_chainGridBlock_eq_univ {L w : ℕ} (hw : 0 < w) :
    (⋃ j : Fin (L / w + 1), (chainGridBlock L w j.val : Set (Fin L))) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact Set.mem_iUnion.mpr ⟨chainGridOwner w x, mem_chainGridBlock_owner hw x⟩

/-- There are at most `L+1` block labels and at most `L` internal-cut labels.
Osborne, Figure 2, with the explicit finite-chain indexing. -/
theorem chainGrid_label_counts (L w : ℕ) :
    L / w + 1 ≤ L + 1 ∧ (L - 1) / w ≤ L := by
  exact ⟨Nat.add_le_add_right (Nat.div_le_self L w) 1,
    (Nat.div_le_self (L - 1) w).trans (Nat.sub_le L 1)⟩

/-- Every enumerated internal cut is positive and strictly inside the chain.
Osborne, arXiv:quant-ph/0508031v2, Figure 2. -/
theorem chainGridCut_bounds {L w : ℕ} (hw : 0 < w) (k : Fin ((L - 1) / w)) :
    0 < chainGridCut w k.val ∧ chainGridCut w k.val < L := by
  have hmul : (k.val + 1) * w ≤ L - 1 :=
    (Nat.le_div_iff_mul_le hw).mp (Nat.succ_le_of_lt k.isLt)
  have hL : 0 < L := by
    by_contra h
    have hzero : L = 0 := by omega
    subst L
    have hk := k.isLt
    simp at hk
  exact ⟨Nat.mul_pos (Nat.succ_pos _) hw, by dsimp only [chainGridCut]; omega⟩

/-- The nominal buffer width is at most `2r+2`, including clipping at the left end.
Osborne, Figure 2. -/
theorem chainCutBuffer_width_le (cut r : ℕ) :
    cut + r + 1 - (cut - 1 - r) ≤ 2 * r + 2 := by omega

/-- Every boundary buffer contains at most `2r+2` sites. Osborne, Figure 2. -/
theorem card_chainCutBuffer_le (L cut r : ℕ) :
    (chainCutBuffer L cut r).card ≤ 2 * r + 2 :=
  (card_interval_le (cut - 1 - r) (cut + r + 1)).trans (chainCutBuffer_width_le cut r)

/-- The actual closed neighborhood of the adjacent pair is exactly its interval buffer.
Osborne, Figures 1--2; Huang, Section 5.4, the Lieb--Robinson truncation in Lemma 19. -/
theorem chainNeighborhood_chainCutPair_eq {L cut : ℕ} (_hcut0 : 0 < cut) (hcutL : cut < L)
    (r : ℕ) : chainNeighborhood (chainCutPair L cut) (r : ℝ) = chainCutBuffer L cut r := by
  have hnonempty : (interval L (cut - 1) (cut + 1)).Nonempty :=
    ⟨⟨cut, hcutL⟩, mem_interval.mpr (show cut - 1 ≤ cut ∧ cut < cut + 1 by omega)⟩
  rw [chainCutPair, chainNeighborhood_interval_eq _ _ _ (Nat.cast_nonneg r),
    ite_eq_left hnonempty]
  simp only [Nat.floor_natCast, chainCutBuffer]
  congr 1
  omega

private theorem chainGridCut_spacing {w j k : ℕ} (hjk : j < k) :
    chainGridCut w j + w ≤ chainGridCut w k := by
  have hmul := Nat.mul_le_mul_right w (Nat.succ_le_of_lt hjk)
  simp only [Nat.succ_eq_add_one] at hmul
  dsimp only [chainGridCut]
  nlinarith

/-- Boundary buffers at different grid cuts are disjoint when their full widths do not
exceed the grid spacing. Osborne, arXiv:quant-ph/0508031v2, Figure 2. -/
theorem pairwise_disjoint_chainGridBuffer (L : ℕ) {w r : ℕ} (hwidth : 2 * r + 2 ≤ w) :
    Pairwise (fun j k : ℕ ↦ Disjoint
      (chainCutBuffer L (chainGridCut w j) r) (chainCutBuffer L (chainGridCut w k) r)) := by
  intro j k hjk
  apply Finset.disjoint_left.mpr
  intro x hxj hxk
  rw [chainCutBuffer, mem_interval] at hxj hxk
  rcases lt_or_gt_of_ne hjk with h | h
  · have hspace := chainGridCut_spacing (w := w) h
    omega
  · have hspace := chainGridCut_spacing (w := w) h
    omega

/-- The enumerated cut pair is exactly the two adjacent sites. Osborne, Figure 1. -/
theorem chainCutPair_eq_pair {L cut : ℕ} (hcut0 : 0 < cut) (hcutL : cut < L) :
    chainCutPair L cut = {⟨cut - 1, by omega⟩, ⟨cut, hcutL⟩} := by
  ext x
  simp only [chainCutPair, mem_interval, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  omega

/-- Every nearest-neighbor edge is contained in one grid block or meets an enumerated
grid cut. The partition and the cut label are constructed from the edge position.
Osborne, arXiv:quant-ph/0508031v2, the decomposition preceding Figure 2. -/
theorem chainGrid_edge_classification {L w i : ℕ} (hw : 0 < w) (hi : i + 1 < L) :
    (∃ j : Fin (L / w + 1), interval L i (i + 2) ⊆ chainGridBlock L w j.val) ∨
      ∃ k : Fin ((L - 1) / w), chainGridCut w k.val = i + 1 := by
  have hdiv := Nat.div_add_mod i w
  have hmod := Nat.mod_lt i hw
  have hilower : i / w * w ≤ i := Nat.div_mul_le_self i w
  have hiupper : i < (i / w + 1) * w := by nlinarith
  by_cases hinside : i + 1 < (i / w + 1) * w
  · left
    let j : Fin (L / w + 1) :=
      ⟨i / w, Nat.lt_succ_of_le (Nat.div_le_div_right (by omega : i ≤ L))⟩
    refine ⟨j, ?_⟩
    intro x hx
    rw [mem_interval] at hx
    rw [chainGridBlock, mem_interval]
    change i / w * w ≤ x.val ∧ x.val < (i / w + 1) * w
    omega
  · right
    have hcut : (i / w + 1) * w = i + 1 := by omega
    have hlabel : i / w + 1 ≤ (L - 1) / w :=
      (Nat.le_div_iff_mul_le hw).mpr (by omega)
    exact ⟨⟨i / w, by omega⟩, hcut⟩

/-- At an enumerated boundary, the neighboring edge is the designated cut pair.
Osborne, Figures 1--2. -/
theorem chainGrid_boundary_edge_eq_pair {L w i : ℕ}
    (k : Fin ((L - 1) / w)) (hcut : chainGridCut w k.val = i + 1) :
    interval L i (i + 2) = chainCutPair L (chainGridCut w k.val) := by
  simp [chainCutPair, hcut, Nat.add_assoc]

/-- An edge across a grid cut is contained in no single grid block.
Osborne, arXiv:quant-ph/0508031v2, Figures 1--2. -/
theorem chainGrid_pair_not_subset_block {L w : ℕ} (hw : 0 < w)
    (k : Fin ((L - 1) / w)) (j : ℕ) :
    ¬ chainCutPair L (chainGridCut w k.val) ⊆ chainGridBlock L w j := by
  intro hsub
  obtain ⟨hc0, hcL⟩ := chainGridCut_bounds hw k
  have hleft : (⟨chainGridCut w k.val - 1, by omega⟩ : Fin L) ∈
      chainCutPair L (chainGridCut w k.val) := by
    rw [chainCutPair, mem_interval]
    change chainGridCut w k.val - 1 ≤ chainGridCut w k.val - 1 ∧
      chainGridCut w k.val - 1 < chainGridCut w k.val + 1
    omega
  have hright : (⟨chainGridCut w k.val, hcL⟩ : Fin L) ∈
      chainCutPair L (chainGridCut w k.val) := by
    rw [chainCutPair, mem_interval]
    change chainGridCut w k.val - 1 ≤ chainGridCut w k.val ∧
      chainGridCut w k.val < chainGridCut w k.val + 1
    omega
  have hleft' := mem_interval.mp (hsub hleft)
  have hright' := mem_interval.mp (hsub hright)
  change j * w ≤ chainGridCut w k.val - 1 ∧
    chainGridCut w k.val - 1 < (j + 1) * w at hleft'
  change j * w ≤ chainGridCut w k.val ∧
    chainGridCut w k.val < (j + 1) * w at hright'
  rcases le_or_gt j k.val with hjk | hkj
  · have hmul := Nat.mul_le_mul_right w (Nat.add_le_add_right hjk 1)
    dsimp only [chainGridCut] at hright'
    omega
  · have hmul := Nat.mul_le_mul_right w (Nat.succ_le_of_lt hkj)
    simp only [Nat.succ_eq_add_one] at hmul
    dsimp only [chainGridCut] at hc0 hleft'
    omega

/-- The block-internal edges are exactly those not crossing an enumerated grid cut.
This is the exhaustive nearest-neighbor classification for Osborne's decomposition,
arXiv:quant-ph/0508031v2, Figure 2. -/
theorem chainGrid_edge_in_block_iff {L w i : ℕ} (hw : 0 < w) (hi : i + 1 < L) :
    (∃ j : Fin (L / w + 1), interval L i (i + 2) ⊆ chainGridBlock L w j.val) ↔
      ¬ ∃ k : Fin ((L - 1) / w), chainGridCut w k.val = i + 1 := by
  constructor
  · rintro ⟨j, hj⟩ ⟨k, hk⟩
    rw [chainGrid_boundary_edge_eq_pair k hk] at hj
    exact chainGrid_pair_not_subset_block hw k j.val hj
  · intro hnot
    rcases chainGrid_edge_classification hw hi with h | h
    · exact h
    · exact (hnot h).elim

end TNLean.MPS.AreaLaw
