/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Counting
import TNLean.MPS.AreaLaw.EntropyInequalities
import Mathlib.Data.Nat.Order.Lemmas

/-!
# Interactions crossing an arbitrary chain region

A finite-range support meeting both sides of a region lies in a window of
`2R` sites about a boundary edge. Counting the possible subsets of
these windows gives at most `2^(2R)` crossing supports per boundary edge.
The region need not be an interval. The estimates include zero range and an
empty boundary, with no additional assumptions.

## Main results

* `IsChainSupport.exists_boundary_window_of_split`: a window about a
  boundary edge contains every site of a split support.
* `card_crossingTerms_le_mul_card_boundaryEdges`: the crossing count with
  coefficient `2^(2R)` per edge.

**Scope restriction (contiguous chains):** The sites are `Fin L`. The broader
finite induced domains of the source may have gaps; see
`docs/paper-gaps/tnlean_one_dimensional_connected_domain_scope.tex`.

Source: TNLean one-dimensional note, `part1_arealaw.tex`, `eq:count`, lines
27–40, and `part2a_mps_information.tex`, lines 355–363. This module is purely
geometric and does not assert a partial-swap operator decomposition.
-/

namespace TNLean.MPS.AreaLaw

/-- A support split by a region lies in a window about one of its
boundary edges. Source: TNLean note, `eq:count`, and
`part2a_mps_information.tex`, lines 359–363. -/
lemma IsChainSupport.exists_boundary_window_of_split
    {L R : ℕ} {X D : Finset (Fin L)} (hX : IsChainSupport L R X)
    (hsplit : (∃ u ∈ X, u ∈ D) ∧ ∃ v ∈ X, v ∉ D) :
    ∃ p ∈ boundaryEdges L D,
      X ⊆ interval L (p + 1 - R) (p + 1 + R) := by
  classical
  let P (m : ℕ) := ∃ i ∈ D, i.val = m
  have hordered (u v : Fin L) (hu : u ∈ X) (hv : v ∈ X) (huv : u.val < v.val)
      (hmem : ¬ (P u.val ↔ P v.val)) :
      ∃ p ∈ boundaryEdges L D, X ⊆ interval L (p + 1 - R) (p + 1 + R) := by
    let Q (n : ℕ) := u.val + n ≤ v.val ∧ (P (u.val + n) ↔ P v.val)
    have hQ0 : ¬ Q 0 := by simpa only [Q, Nat.add_zero, huv.le, true_and] using hmem
    have hQex : ∃ n, Q n := ⟨v.val - u.val, by
      simp only [Q, Nat.add_sub_of_le huv.le, le_refl, iff_self, and_self]⟩
    obtain ⟨n, hn, hn1⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists hQ0 hQex
    simp only [Q] at hn hn1
    refine ⟨u.val + n, mem_boundaryEdges.mpr ⟨by have := v.isLt; omega, ?_⟩, ?_⟩
    · change ¬ (P (u.val + n) ↔ P (u.val + n + 1))
      intro he
      exact hn ⟨by omega, he.trans (by simpa only [Nat.add_assoc] using hn1.2)⟩
    · intro z hz
      rw [mem_interval]
      have huz := hX.2 u hu z hz
      have hzv := hX.2 z hz v hv
      omega
  obtain ⟨⟨u, hu, huD⟩, v, hv, hvD⟩ := hsplit
  have hPu : P u.val := ⟨u, huD, rfl⟩
  have hPv : ¬ P v.val := by
    rintro ⟨i, hi, hiv⟩
    exact hvD (Fin.ext hiv ▸ hi)
  rcases lt_trichotomy u.val v.val with huv | huv | hvu
  · exact hordered u v hu hv huv (fun he ↦ hPv (he.mp hPu))
  · exact (hPv (huv ▸ hPu)).elim
  · exact hordered v u hv hu hvu (fun he ↦ hPv (he.mpr hPu))

/-- The number of supports crossing a region is at most `2^(2R)` times its
boundary cardinality. Source: TNLean note, `eq:count`, and
`part2a_mps_information.tex`, lines 359–360, before counting the two replicas. -/
lemma card_crossingTerms_le_mul_card_boundaryEdges
    (L R : ℕ) (D : Finset (Fin L)) :
    (Entropy.crossingTerms (fun X : ChainSupport L R ↦ X.1) D).card ≤
      2 ^ (2 * R) * (boundaryEdges L D).card := by
  classical
  let W (p : ℕ) := interval L (p + 1 - R) (p + 1 + R)
  let F (p : ℕ) := Finset.univ.filter (fun X : ChainSupport L R ↦ X.1 ⊆ W p)
  have hcover : Entropy.crossingTerms (fun X : ChainSupport L R ↦ X.1) D ⊆
      (boundaryEdges L D).biUnion F := by
    intro X hX
    simp only [Entropy.crossingTerms, Finset.mem_filter, Finset.mem_univ, true_and] at hX
    obtain ⟨p, hp, hsub⟩ := X.2.exists_boundary_window_of_split hX
    exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsub⟩⟩
  have hcard (p : ℕ) : (F p).card ≤ 2 ^ (2 * R) :=
    (card_filter_subset_le (W p)).trans
      (Nat.pow_le_pow_right (by norm_num) ((card_interval_le _ _).trans (by omega)))
  exact (Finset.card_le_card hcover).trans
    ((Finset.card_biUnion_le_card_mul (boundaryEdges L D) F (2 ^ (2 * R))
      (fun p _ ↦ hcard p)).trans_eq (Nat.mul_comm _ _))

end TNLean.MPS.AreaLaw
