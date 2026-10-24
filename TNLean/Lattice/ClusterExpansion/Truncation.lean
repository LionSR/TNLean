/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ClusterExpansion.ClusterPart
import TNLean.Lattice.ConnectedSetCount

/-!
# The truncated high-temperature expansion as an inclusion–exclusion sum

Hastings, *Solving gapped Hamiltonians locally* (arXiv:cond-mat/0508554v3,
`References/cond-mat_0508554/proj3new.tex`, lines 1090–1114 and 1197–1225), expands
`e^{-βH} = ∑_n (-β)^n/n! (∑_k h_k)^n` as a sum over words `h_{k_1} ⋯ h_{k_n}`. The terms of a word
are joined into clusters when their supports overlap, and `ρ(β, l_proj)` keeps the words none of
whose clusters is large. The remark added at lines 1218–1224 writes
`ρ(β, l_proj) = ρ - ρ_1 + ρ_2 - ⋯`, where `ρ_m` sums the operators `ρ(β, C_1, …, C_m)` over
families of `m` large clusters; a word with `k` large clusters is counted `binom(k, m)` times
in `ρ_m`.

This file proves that identity. The terms are labelled by `κ`, and a graph `G` on `κ` records
which terms overlap. For a set `A` of terms, a *cluster* of `A` is a connected subset `C ⊆ A`
with no term of `A` adjacent to `C` outside `C`, that is, `A` avoids the boundary
`clusterBoundary (G.neighborFinset ·) C`. Which clusters are large is a predicate `large`
(in the source, diameter larger than `l_proj`). The proof has three steps.

* For one word with letter set `A`, `[no large cluster] = ∑_U (-1)^{|U|}`, the sum over the
  families `U` of large connected sets that are all clusters of `A`.
* A family `U` consists of clusters of `A` exactly when `⋃U ⊆ A` and `A` avoids `⋃_{C ∈ U} ∂C`.
  This forces `⋃∂U ∩ ⋃U = ∅` (the family is *admissible*), and then the members of `U` are
  pairwise disjoint.
* By inclusion and exclusion over the letters, the words of length `n` containing every letter
  of `C` and none of `B` sum to `∑_{D ⊆ C} (-1)^{|D|} (H - H_B - H_D)^n`, keeping word order and
  repeated letters. Summed against `(-β)^n/n!` this is `clusterPart H h B C β`.

Hence the power series of `ρ(β, l)` sums to
`∑_U (-1)^{|U|} clusterPart H h (⋃∂U) (⋃U) β` over the admissible families of large connected
sets, and `e^{-βH} - ρ(β, l)` is the same sum over the nonempty families.

**Local fix (the boundary of a cluster):** the source defines `B(C)` as the terms `j ∉ C` with
`H_j` acting on a site of `C` (lines 1130–1133), and claims that a word containing `H_C` and
avoiding `H_{B(C)}` has a cluster consisting of exactly the sites of `H_C` (lines 1134–1138).
That fails: on a chain with `H_i` acting on `{i-1, i, i+1}`, `C = {1}` has `B(C) = {0, 2}`, and
the word `H_1 H_3` avoids `B(C)` while `H_3` overlaps `H_1` at site `2`. The boundary used here
is the set of terms whose support meets the support of `H_C`, the neighbours of `C` in the
overlap graph (`overlapGraph`); with it the claim holds for connected `C`. The count
`n_C + n_B ≤ S n_C` of equation `percb2` then needs `S` to count the terms within `2R` of a term.
Documented in `docs/paper-gaps/hastings05_cluster_boundary.tex`.

## Main results

* `TNLean.Lattice.ClusterExpansion.sum_pow_eq_sum_words`: `(∑_{k ∈ s} a_k)^n` as the sum of the
  ordered products of the words of length `n` in `s`.
* `TNLean.Lattice.ClusterExpansion.sum_words_contain_avoid`: inclusion and exclusion over the
  letters of a word.
* `TNLean.Lattice.ClusterExpansion.overlapGraph`, `mem_boundary_overlapGraph`: the graph of
  overlapping supports, in which the boundary of `C` is the set of terms meeting the support of
  `H_C`.
* `TNLean.Lattice.ClusterExpansion.IsCluster`, `eq_of_isCluster_of_inter_nonempty`: clusters
  of a set of terms, and two clusters that meet are equal.
* `TNLean.Lattice.ClusterExpansion.ite_noLargeCluster_eq_sum`: inclusion and exclusion over the
  large clusters of one word.
* `TNLean.Lattice.ClusterExpansion.pairwiseDisjoint_of_admissible`,
  `card_add_card_biUnion_boundary_le`: the members of an admissible family are pairwise
  disjoint, and the boundary count passes to their union.
* `TNLean.Lattice.ClusterExpansion.hasSum_truncatedExpTerm`, `truncatedExp_eq_sum`: the
  inclusion–exclusion identity `ρ(β, l) = ∑_U (-1)^{|U|} ρ(β, U)` (lines 1197–1225).
* `TNLean.Lattice.ClusterExpansion.exp_sub_truncatedExp`: `e^{-βH} - ρ(β, l)` as the sum over
  nonempty families.
* `TNLean.Lattice.ClusterExpansion.norm_trace_mul_exp_sub_truncatedExp_le`: the bound
  `‖O‖ Z ∑_{U ≠ ∅} ∏_{C ∈ U} y^{n_C}` that equation `perc2` sums.

## References

* M. B. Hastings, *Solving gapped Hamiltonians locally*, Phys. Rev. B 73 (2006) 085115,
  arXiv:cond-mat/0508554v3, Section IV, lines 1090–1138 and 1197–1225.
-/

open Finset Matrix
open scoped Matrix.Norms.L2Operator

namespace TNLean.Lattice.ClusterExpansion

section Words

variable {κ R : Type*} [Fintype κ] [DecidableEq κ] [Ring R]

/-- **The power of a sum as a sum over words.** In a ring that need not be commutative,
`(∑_{k ∈ s} a_k)^n` is the sum, over the words `w` of length `n` in the letters of `s`, of the
ordered products `a_{w_0} ⋯ a_{w_{n-1}}`. -/
theorem sum_pow_eq_sum_words (s : Finset κ) (a : κ → R) (n : ℕ) :
    (∑ k ∈ s, a k) ^ n =
      ∑ w : Fin n → κ with ∀ i, w i ∈ s, (List.ofFn fun i ↦ a (w i)).prod := by
  induction n with
  | zero => simp [Finset.filter_true_of_mem]
  | succ n ih =>
    rw [pow_succ', ih, Finset.sum_mul_sum, Finset.sum_filter,
      ← (Fin.consEquiv fun _ ↦ κ).sum_comp, Fintype.sum_prod_type,
      ← Finset.sum_subset (Finset.subset_univ s) fun k _ hk ↦
        Finset.sum_eq_zero fun v _ ↦ by simp [Fin.forall_fin_succ, Fin.consEquiv, hk]]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    simp [Fin.forall_fin_succ, Fin.consEquiv, hk, List.ofFn_succ]

omit [Fintype κ] in
/-- Inclusion and exclusion for one set of letters: `∑_{D ⊆ C} (-1)^{|D|} [X ∩ D = ∅]` is
`1` when `C ⊆ X` and `0` otherwise. -/
theorem sum_powerset_neg_one_pow_card_disjoint (X C : Finset κ) :
    ∑ D ∈ C.powerset, (if Disjoint X D then (-1 : ℤ) ^ #D else 0) =
      if C ⊆ X then 1 else 0 := by
  rw [← Finset.sum_filter]
  have : {D ∈ C.powerset | Disjoint X D} = (C \ X).powerset := by
    ext D
    simp only [mem_filter, mem_powerset, subset_sdiff]
    exact ⟨fun h ↦ ⟨h.1, h.2.symm⟩, fun h ↦ ⟨h.1, h.2.symm⟩⟩
  rw [this, Finset.sum_powerset_neg_one_pow_card]
  exact if_congr sdiff_eq_empty_iff_subset rfl rfl

/-- **Inclusion and exclusion over the letters of a word.** For disjoint `B` and `C`, the words of
length `n` containing every letter of `C` and no letter of `B` have ordered products summing to
`∑_{D ⊆ C} (-1)^{|D|} (∑_{k ∉ B ∪ D} a_k)^n`. Word order and repeated letters are kept. -/
theorem sum_words_contain_avoid (a : κ → R) (B C : Finset κ) (n : ℕ) :
    ∑ w : Fin n → κ with C ⊆ univ.image w ∧ Disjoint (univ.image w) B,
        (List.ofFn fun i ↦ a (w i)).prod =
      ∑ D ∈ C.powerset, (-1 : ℤ) ^ #D • (∑ k ∈ (B ∪ D)ᶜ, a k) ^ n := by
  simp_rw [sum_pow_eq_sum_words, Finset.smul_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  have hw : ∀ D : Finset κ, (∀ i, w i ∈ (B ∪ D)ᶜ) ↔
      Disjoint (univ.image w) B ∧ Disjoint (univ.image w) D := by
    intro D
    constructor
    · intro h
      refine ⟨Finset.disjoint_left.mpr ?_, Finset.disjoint_left.mpr ?_⟩ <;>
      · intro x hx
        obtain ⟨i, -, rfl⟩ := mem_image.mp hx
        have := h i
        simp_all
    · rintro ⟨h1, h2⟩ i
      have hi : w i ∈ univ.image w := mem_image_of_mem w (mem_univ i)
      simpa [not_or] using ⟨Finset.disjoint_left.mp h1 hi, Finset.disjoint_left.mp h2 hi⟩
  simp_rw [hw]
  by_cases hB : Disjoint (univ.image w) B
  · have key := sum_powerset_neg_one_pow_card_disjoint (univ.image w) C
    simp only [hB, and_true, true_and]
    calc (if C ⊆ univ.image w then (List.ofFn fun i ↦ a (w i)).prod else 0)
        = ((if C ⊆ univ.image w then 1 else 0 : ℤ)) • (List.ofFn fun i ↦ a (w i)).prod := by
          split_ifs <;> simp
      _ = _ := by
          rw [← key, Finset.sum_smul]
          refine Finset.sum_congr rfl fun D _ ↦ ?_
          split_ifs <;> simp
  · simp [hB]

end Words

section Clusters

variable {κ : Type*} [Fintype κ] [DecidableEq κ] (G : SimpleGraph κ) [DecidableRel G.Adj]

/-- The boundary of a set `C` of terms in the overlap graph `G`: the terms outside `C` adjacent
to a term of `C`. This is `clusterBoundary` with the neighbours in `G`. -/
abbrev boundary (C : Finset κ) : Finset κ :=
  clusterBoundary (fun j ↦ G.neighborFinset j) C

theorem mem_boundary {C : Finset κ} {j : κ} :
    j ∈ boundary G C ↔ j ∉ C ∧ ∃ i ∈ C, G.Adj j i := by
  simp [boundary, clusterBoundary]

/-- A *cluster* of a set `A` of terms: a connected set `C ⊆ A` of terms such that no term of `A`
outside `C` is adjacent to `C`. These are the connected components of the terms of `A` joined by
overlaps (Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1096–1101). -/
def IsCluster (A C : Finset κ) : Prop :=
  C ⊆ A ∧ (G.induce (C : Set κ)).Connected ∧ Disjoint A (boundary G C)

/-- A connected set `C` meeting `C'` and avoiding the boundary of `C'` lies in `C'`. -/
theorem subset_of_connected_of_disjoint_boundary {C C' : Finset κ}
    (hC : (G.induce (C : Set κ)).Connected) (hCC' : (C ∩ C').Nonempty)
    (hdisj : Disjoint C (boundary G C')) : C ⊆ C' := by
  obtain ⟨x, hx⟩ := hCC'
  rw [Finset.mem_inter] at hx
  have key : ∀ (u v : (C : Set κ)), (G.induce (C : Set κ)).Walk u v →
      (u : κ) ∈ C' → (v : κ) ∈ C' := by
    intro u v p
    induction p with
    | nil => exact id
    | @cons u w v hadj p ih =>
      intro hu
      apply ih
      by_contra hw
      have hb : (w : κ) ∈ boundary G C' :=
        (mem_boundary G).2 ⟨hw, u, hu, (SimpleGraph.comap_adj.mp hadj).symm⟩
      exact Finset.disjoint_left.mp hdisj w.2 hb
  intro y hy
  obtain ⟨p⟩ := hC.preconnected ⟨x, hx.1⟩ ⟨y, hy⟩
  exact key _ _ p hx.2

/-- **Two clusters that meet are equal.** -/
theorem eq_of_isCluster_of_inter_nonempty {A C C' : Finset κ} (hC : IsCluster G A C)
    (hC' : IsCluster G A C') (h : (C ∩ C').Nonempty) : C = C' := by
  refine Finset.Subset.antisymm ?_ ?_
  · exact subset_of_connected_of_disjoint_boundary G hC.2.1 h
      (hC'.2.2.mono_left hC.1)
  · exact subset_of_connected_of_disjoint_boundary G hC'.2.1 (by rwa [inter_comm])
      (hC.2.2.mono_left hC'.1)

/-- A family `U` of sets of terms is *admissible* when no member meets the boundary of a
member: `⋃_{C ∈ U} ∂C` is disjoint from `⋃U`. -/
def IsAdmissible (U : Finset (Finset κ)) : Prop :=
  Disjoint (U.biUnion (boundary G)) (U.biUnion id)

instance (U : Finset (Finset κ)) : Decidable (IsAdmissible G U) := by
  unfold IsAdmissible; infer_instance

/-- **The members of an admissible family of connected sets are pairwise disjoint.** If two
members meet, each lies in the other, since a connected set leaving the other one would step
into its boundary. -/
theorem pairwiseDisjoint_of_admissible {U : Finset (Finset κ)} (hU : IsAdmissible G U)
    (hconn : ∀ C ∈ U, (G.induce (C : Set κ)).Connected) :
    (U : Set (Finset κ)).PairwiseDisjoint id := by
  intro C hC C' hC' hne
  rw [Function.onFun, id, id, Finset.disjoint_iff_inter_eq_empty]
  by_contra h
  have hn : (C ∩ C').Nonempty := Finset.nonempty_iff_ne_empty.mpr h
  have hd : ∀ {E E' : Finset κ}, E ∈ U → E' ∈ U → Disjoint E (boundary G E') :=
    fun hE hE' ↦ (Finset.disjoint_of_subset_left (Finset.subset_biUnion_of_mem id hE)
      (Finset.disjoint_of_subset_right (Finset.subset_biUnion_of_mem (boundary G) hE')
        hU.symm))
  exact hne (Finset.Subset.antisymm
    (subset_of_connected_of_disjoint_boundary G (hconn C hC) hn (hd hC hC'))
    (subset_of_connected_of_disjoint_boundary G (hconn C' hC') (by rwa [inter_comm])
      (hd hC' hC)))

/-- For an admissible family, the union of the boundaries is the boundary of the union. -/
theorem biUnion_boundary_eq_of_admissible {U : Finset (Finset κ)} (hU : IsAdmissible G U) :
    U.biUnion (boundary G) = boundary G (U.biUnion id) := by
  ext j
  constructor
  · intro hj
    obtain ⟨C, hC, hjC⟩ := mem_biUnion.mp hj
    obtain ⟨-, i, hi, hji⟩ := (mem_boundary G).1 hjC
    refine (mem_boundary G).2 ⟨fun hjU ↦ Finset.disjoint_left.mp hU hj hjU, i,
      mem_biUnion.mpr ⟨C, hC, hi⟩, hji⟩
  · intro hj
    obtain ⟨hjU, i, hiU, hji⟩ := (mem_boundary G).1 hj
    obtain ⟨C, hC, hi⟩ := mem_biUnion.mp hiU
    exact mem_biUnion.mpr ⟨C, hC, (mem_boundary G).2
      ⟨fun hjC ↦ hjU (mem_biUnion.mpr ⟨C, hC, hjC⟩), i, hi, hji⟩⟩

/-- No cluster of the set `A` of terms is large. -/
def NoLargeCluster (large : Finset κ → Prop) (A : Finset κ) : Prop :=
  ∀ C, IsCluster G A C → ¬ large C

open Classical in
/-- The connected sets of terms that are large: the possible large clusters. -/
noncomputable def largeConnected (large : Finset κ → Prop) : Finset (Finset κ) :=
  {C | (G.induce (C : Set κ)).Connected ∧ large C}

theorem mem_largeConnected {large : Finset κ → Prop} {C : Finset κ} :
    C ∈ largeConnected G large ↔ (G.induce (C : Set κ)).Connected ∧ large C := by
  classical
  simp [largeConnected]

/-- A family of connected sets consists of clusters of `A` exactly when `A` contains its union
and avoids the union of its boundaries. -/
theorem forall_isCluster_iff {U : Finset (Finset κ)} (A : Finset κ)
    (hconn : ∀ C ∈ U, (G.induce (C : Set κ)).Connected) :
    (∀ C ∈ U, IsCluster G A C) ↔
      U.biUnion id ⊆ A ∧ Disjoint A (U.biUnion (boundary G)) := by
  simp only [IsCluster, Finset.biUnion_subset, id, Finset.disjoint_biUnion_right]
  exact ⟨fun h ↦ ⟨fun C hC ↦ (h C hC).1, fun C hC ↦ (h C hC).2.2⟩,
    fun h C hC ↦ ⟨h.1 C hC, hconn C hC, h.2 C hC⟩⟩

open Classical in
/-- **Inclusion and exclusion over the large clusters of one word.** For a set `A` of terms,
`[no cluster of A is large] = ∑_U (-1)^{|U|}`, the sum over the admissible families `U` of large
connected sets with `⋃U ⊆ A` and `A` disjoint from `⋃∂U`. A set with `k` large clusters is
counted by `binom(k, m)` families of size `m`. Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1218–1224. -/
theorem ite_noLargeCluster_eq_sum (large : Finset κ → Prop) (A : Finset κ) :
    (if NoLargeCluster G large A then (1 : ℤ) else 0) =
      ∑ U ∈ (largeConnected G large).powerset with IsAdmissible G U,
        if U.biUnion id ⊆ A ∧ Disjoint A (U.biUnion (boundary G)) then (-1) ^ #U else 0 := by
  set T := largeConnected G large
  set L := {C ∈ T | IsCluster G A C}
  have hconn : ∀ U ∈ T.powerset, ∀ C ∈ U, (G.induce (C : Set κ)).Connected :=
    fun U hU C hC ↦ ((mem_largeConnected G).1 (mem_powerset.1 hU hC)).1
  -- Drop the admissibility filter: a non-admissible family is never a family of clusters.
  rw [Finset.sum_filter_of_ne fun U hU hne ↦ ?_]
  swap
  · by_contra hadm
    split_ifs at hne with h
    · obtain ⟨j, hjB, hjU⟩ := Finset.not_disjoint_iff.mp hadm
      exact Finset.disjoint_left.mp h.2 (h.1 hjU) hjB
    · exact hne rfl
  -- Rewrite the condition as membership of `U` in the powerset of the large clusters of `A`.
  have hcond : ∀ U ∈ T.powerset,
      (U.biUnion id ⊆ A ∧ Disjoint A (U.biUnion (boundary G))) ↔ U ∈ L.powerset := by
    intro U hU
    rw [← forall_isCluster_iff G A (hconn U hU), mem_powerset]
    constructor
    · intro h C hC
      exact mem_filter.2 ⟨mem_powerset.1 hU hC, h C hC⟩
    · intro h C hC
      exact (mem_filter.1 (h hC)).2
  rw [Finset.sum_congr rfl fun U hU ↦ if_congr (hcond U hU) rfl rfl, ← Finset.sum_filter]
  have hL : {U ∈ T.powerset | U ∈ L.powerset} = L.powerset := by
    ext U
    simp only [mem_filter, mem_powerset, and_iff_right_iff_imp]
    exact fun h ↦ h.trans (filter_subset _ _)
  rw [hL, Finset.sum_powerset_neg_one_pow_card]
  refine if_congr ?_ rfl rfl
  rw [NoLargeCluster, Finset.filter_eq_empty_iff]
  constructor
  · intro h C hCT hCl
    exact h C hCl ((mem_largeConnected G).1 hCT).2
  · intro h C hCl hlarge
    exact h ((mem_largeConnected G).2 ⟨hCl.2.1, hlarge⟩) hCl

/-- For an admissible family of connected sets, the number of terms of the union is the sum of
the sizes of the members. -/
theorem card_biUnion_of_admissible {U : Finset (Finset κ)} (hU : IsAdmissible G U)
    (hconn : ∀ C ∈ U, (G.induce (C : Set κ)).Connected) :
    #(U.biUnion id) = ∑ C ∈ U, #C :=
  Finset.card_biUnion (pairwiseDisjoint_of_admissible G hU hconn)

/-- **The boundary count for a family.** If every member `C` of an admissible family of connected
sets has `n_C + n_{∂C} ≤ S n_C`, then the union has `n_{⋃U} + n_{⋃∂U} ≤ S n_{⋃U}`, the
hypothesis of `norm_trace_mul_clusterPart_le_pow` for `ρ(β, C_1, …, C_m)`. -/
theorem card_add_card_biUnion_boundary_le {U : Finset (Finset κ)} (hU : IsAdmissible G U)
    (hconn : ∀ C ∈ U, (G.induce (C : Set κ)).Connected) {S : ℝ}
    (hS : ∀ C ∈ U, ((#C : ℝ) + #(boundary G C)) ≤ S * #C) :
    ((#(U.biUnion id) : ℝ) + #(U.biUnion (boundary G))) ≤ S * #(U.biUnion id) := by
  rw [card_biUnion_of_admissible G hU hconn]
  push_cast
  rw [Finset.mul_sum]
  calc (∑ C ∈ U, (#C : ℝ)) + #(U.biUnion (boundary G))
      ≤ (∑ C ∈ U, (#C : ℝ)) + ∑ C ∈ U, (#(boundary G C) : ℝ) := by
        gcongr; exact_mod_cast Finset.card_biUnion_le
    _ = ∑ C ∈ U, ((#C : ℝ) + #(boundary G C)) := Finset.sum_add_distrib.symm
    _ ≤ ∑ C ∈ U, S * #C := Finset.sum_le_sum hS

end Clusters

section Overlap

variable {κ σ : Type*} [Fintype κ] [DecidableEq κ] [DecidableEq σ]

/-- The overlap graph of terms whose supports are `acts j`: two distinct terms are adjacent when
their supports meet. The clusters of a word are the clusters of its set of terms in this graph
(Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1096–1101). -/
def overlapGraph (acts : κ → Finset σ) : SimpleGraph κ where
  Adj i j := i ≠ j ∧ (acts i ∩ acts j).Nonempty
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, by rw [inter_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

instance (acts : κ → Finset σ) : DecidableRel (overlapGraph acts).Adj :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- In the overlap graph, the boundary of `C` is the set of terms outside `C` whose support meets
the support `⋃_{i ∈ C} acts i` of `H_C`. This is the boundary for which a word containing `H_C`
and avoiding the boundary has `C` as a cluster; the source's `B(C)` (lines 1130–1133) asks only
that `H_j` act on a site of `C`. -/
theorem mem_boundary_overlapGraph (acts : κ → Finset σ) {C : Finset κ} {j : κ} :
    j ∈ boundary (overlapGraph acts) C ↔ j ∉ C ∧ (acts j ∩ C.biUnion acts).Nonempty := by
  rw [mem_boundary]
  constructor
  · rintro ⟨hj, i, hi, -, x, hx⟩
    refine ⟨hj, x, mem_inter.2 ⟨(mem_inter.1 hx).1, mem_biUnion.2 ⟨i, hi, (mem_inter.1 hx).2⟩⟩⟩
  · rintro ⟨hj, x, hx⟩
    obtain ⟨i, hi, hxi⟩ := mem_biUnion.1 (mem_inter.1 hx).2
    exact ⟨hj, i, hi, fun h ↦ hj (h ▸ hi), x, mem_inter.2 ⟨(mem_inter.1 hx).1, hxi⟩⟩

end Overlap

section Series

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (G : SimpleGraph κ) [DecidableRel G.Adj] (large : Finset κ → Prop)

/-- The exponential series of `-(β X)` with real coefficients `(-β)^n / n!`. -/
theorem hasSum_div_factorial_smul_pow (X : Matrix ι ι ℂ) (β : ℝ) :
    HasSum (fun n ↦ ((-β) ^ n / n.factorial : ℝ) • X ^ n) (NormedSpace.exp (-(β • X))) := by
  convert NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (-(β • X)) using 2 with n
  rw [← neg_smul, smul_pow, RCLike.real_smul_eq_coe_smul (K := ℂ),
    RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  congr 1
  push_cast
  ring

/-- **The cluster part as a word series.** For `H = ∑_k h_k` and disjoint `B`, `C`, the words
containing every term of `C` and no term of `B`, weighted by `(-β)^n / n!`, sum to
`clusterPart H h B C β`. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1174–1177. -/
theorem hasSum_words_clusterPart {H : Matrix ι ι ℂ} {h : κ → Matrix ι ι ℂ}
    (hH : H = ∑ k, h k) {B C : Finset κ} (hBC : Disjoint B C) (β : ℝ) :
    HasSum (fun n ↦ ((-β) ^ n / n.factorial : ℝ) •
        ∑ w : Fin n → κ with C ⊆ univ.image w ∧ Disjoint (univ.image w) B,
          (List.ofFn fun i ↦ h (w i)).prod)
      (clusterPart H h B C β) := by
  simp_rw [sum_words_contain_avoid, Finset.smul_sum]
  refine hasSum_sum fun D hD ↦ ?_
  have hBD : Disjoint B D := hBC.mono_right (mem_powerset.1 hD)
  have hX : ∑ k ∈ (B ∪ D)ᶜ, h k = H - ∑ k ∈ B, h k - ∑ k ∈ D, h k := by
    rw [hH, ← Finset.sum_add_sum_compl (B ∪ D), Finset.sum_union hBD]
    abel
  have hz : ∀ (n : ℕ) (Y : Matrix ι ι ℂ),
      ((-β) ^ n / n.factorial : ℝ) • ((-1 : ℤ) ^ #D • Y) =
        (-1 : ℂ) ^ #D • (((-β) ^ n / n.factorial : ℝ) • Y) := by
    intro n Y
    rw [smul_comm, ← Int.cast_smul_eq_zsmul ℂ]
    push_cast
    rfl
  simp_rw [hz, hX]
  exact (hasSum_div_factorial_smul_pow _ β).const_smul _

open Classical in
/-- The `n`-th term of the power series of `ρ(β, l)`: the words of length `n` none of whose
clusters is large, weighted by `(-β)^n / n!`. Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1101–1104. -/
noncomputable def truncatedExpTerm (h : κ → Matrix ι ι ℂ) (β : ℝ) (n : ℕ) : Matrix ι ι ℂ :=
  ((-β) ^ n / n.factorial : ℝ) •
    ∑ w : Fin n → κ with NoLargeCluster G large (univ.image w),
      (List.ofFn fun i ↦ h (w i)).prod

/-- Hastings' truncated operator `ρ(β, l_proj)`: the sum of the terms of the power series of
`e^{-βH}` none of whose clusters is large. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1101–1104. -/
noncomputable def truncatedExp (h : κ → Matrix ι ι ℂ) (β : ℝ) : Matrix ι ι ℂ :=
  ∑' n, truncatedExpTerm G large h β n

open Classical in
/-- **Inclusion and exclusion over the large clusters** (Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1197–1225). For `H = ∑_k h_k`, the power series of `ρ(β, l)` sums to
`∑_U (-1)^{|U|} ρ(β, U)`, over the admissible families `U` of large connected sets, where
`ρ(β, U) = clusterPart H h (⋃∂U) (⋃U) β` collects the words in which every member of `U` is a
cluster. This is `ρ - ρ_1 + ρ_2 - ⋯` of the remark added at lines 1218–1224, with `ρ_m` the sum
over the families of size `m`. -/
theorem hasSum_truncatedExpTerm {H : Matrix ι ι ℂ} {h : κ → Matrix ι ι ℂ}
    (hH : H = ∑ k, h k) (β : ℝ) :
    HasSum (truncatedExpTerm G large h β)
      (∑ U ∈ (largeConnected G large).powerset with IsAdmissible G U,
        (-1 : ℂ) ^ #U • clusterPart H h (U.biUnion (boundary G)) (U.biUnion id) β) := by
  have key : ∀ n, truncatedExpTerm G large h β n =
      ∑ U ∈ (largeConnected G large).powerset with IsAdmissible G U, (-1 : ℂ) ^ #U •
        (((-β) ^ n / n.factorial : ℝ) •
          ∑ w : Fin n → κ with U.biUnion id ⊆ univ.image w ∧
            Disjoint (univ.image w) (U.biUnion (boundary G)),
            (List.ofFn fun i ↦ h (w i)).prod) := by
    intro n
    rw [truncatedExpTerm, Finset.sum_filter]
    have hite : ∀ w : Fin n → κ,
        (if NoLargeCluster G large (univ.image w) then (List.ofFn fun i ↦ h (w i)).prod
          else 0) =
        (if NoLargeCluster G large (univ.image w) then (1 : ℤ) else 0) •
          (List.ofFn fun i ↦ h (w i)).prod := by
      intro w; split_ifs <;> simp
    simp_rw [hite, ite_noLargeCluster_eq_sum, Finset.sum_smul]
    rw [Finset.sum_comm, Finset.smul_sum]
    refine Finset.sum_congr rfl fun U _ ↦ ?_
    simp only [Finset.sum_filter, Finset.smul_sum]
    refine Finset.sum_congr rfl ?_
    intro w _
    split_ifs
    · rw [← Int.cast_smul_eq_zsmul ℂ, smul_comm]
      push_cast
      rfl
    · simp
  rw [funext key]
  refine hasSum_sum fun U hU ↦ ?_
  exact (hasSum_words_clusterPart hH (mem_filter.1 hU).2 β).const_smul _

open Classical in
/-- `ρ(β, l)` as the finite inclusion–exclusion sum over admissible families of large connected
sets. -/
theorem truncatedExp_eq_sum {H : Matrix ι ι ℂ} {h : κ → Matrix ι ι ℂ}
    (hH : H = ∑ k, h k) (β : ℝ) :
    truncatedExp G large h β =
      ∑ U ∈ (largeConnected G large).powerset with IsAdmissible G U,
        (-1 : ℂ) ^ #U • clusterPart H h (U.biUnion (boundary G)) (U.biUnion id) β :=
  (hasSum_truncatedExpTerm G large hH β).tsum_eq

open Classical in
/-- **The difference `ρ(β) - ρ(β, l)`** (Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1197–1225): `e^{-βH} - ρ(β, l) = -∑_{U ≠ ∅} (-1)^{|U|} ρ(β, U)`, the sum over the nonempty
admissible families of large connected sets. The empty family contributes `e^{-βH}`. -/
theorem exp_sub_truncatedExp {H : Matrix ι ι ℂ} {h : κ → Matrix ι ι ℂ}
    (hH : H = ∑ k, h k) (β : ℝ) :
    NormedSpace.exp (-(β • H)) - truncatedExp G large h β =
      -∑ U ∈ (largeConnected G large).powerset with IsAdmissible G U ∧ U.Nonempty,
        (-1 : ℂ) ^ #U • clusterPart H h (U.biUnion (boundary G)) (U.biUnion id) β := by
  rw [truncatedExp_eq_sum G large hH β, ← Finset.sum_filter_add_sum_filter_not
    {U ∈ (largeConnected G large).powerset | IsAdmissible G U} (fun U ↦ U.Nonempty)
    (fun U ↦ (-1 : ℂ) ^ #U • clusterPart H h (U.biUnion (boundary G)) (U.biUnion id) β),
    Finset.filter_filter, Finset.filter_filter]
  have hempty : {U ∈ (largeConnected G large).powerset | IsAdmissible G U ∧ ¬U.Nonempty} =
      {∅} := by
    ext U
    simp only [mem_filter, mem_powerset, mem_singleton, not_nonempty_iff_eq_empty]
    constructor
    · exact fun h ↦ h.2.2
    · rintro rfl
      exact ⟨empty_subset _, by simp [IsAdmissible], rfl⟩
  rw [hempty, Finset.sum_singleton]
  simp [clusterPart]

open Classical in
/-- **The bound summed by equation `perc2`.** Let `H = ∑_k h_k` be Hermitian with Hermitian terms
of norm at most `J`, let `β ≥ 0`, and let every large connected set `C` have
`n_C + n_{∂C} ≤ S n_C`. Then
`|Tr (O (e^{-βH} - ρ(β, l)))| ≤ ∑_{U ≠ ∅} ‖O‖ (∏_{C ∈ U} y^{n_C}) Tr e^{-βH}`, the sum over the
nonempty admissible families of large connected sets, with `y = (e^{βJ} - 1) e^{SJβ}`.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1197–1225, with the bound of
equation `percb2` for each family. -/
theorem norm_trace_mul_exp_sub_truncatedExp_le {H : Matrix ι ι ℂ} (hHerm : H.IsHermitian)
    {h : κ → Matrix ι ι ℂ} (hH : H = ∑ k, h k) (hh : ∀ k, (h k).IsHermitian) {J : ℝ}
    (hJ : ∀ k, ‖h k‖ ≤ J) (O : Matrix ι ι ℂ) {β : ℝ} (hβ : 0 ≤ β) {S : ℝ}
    (hS : ∀ C ∈ largeConnected G large, ((#C : ℝ) + #(boundary G C)) ≤ S * #C) :
    ‖(O * (NormedSpace.exp (-(β • H)) - truncatedExp G large h β)).trace‖ ≤
      ∑ U ∈ (largeConnected G large).powerset with IsAdmissible G U ∧ U.Nonempty,
        ‖O‖ * (∏ C ∈ U, ((Real.exp (β * J) - 1) * Real.exp (S * J * β)) ^ #C) *
          (NormedSpace.exp (-(β • H))).trace.re := by
  rw [exp_sub_truncatedExp G large hH β, Matrix.mul_neg, Matrix.trace_neg, norm_neg,
    Finset.mul_sum, Matrix.trace_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun U hU ↦ ?_)
  obtain ⟨hUT, hadm, -⟩ : U ⊆ largeConnected G large ∧ IsAdmissible G U ∧ U.Nonempty := by
    simpa only [mem_filter, mem_powerset, and_assoc] using hU
  have hconn : ∀ C ∈ U, (G.induce (C : Set κ)).Connected :=
    fun C hC ↦ ((mem_largeConnected G).1 (hUT hC)).1
  rw [Matrix.mul_smul, Matrix.trace_smul, norm_smul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul]
  exact norm_trace_mul_clusterPart_biUnion_le hHerm (B := boundary G) (C := id)
    (pairwiseDisjoint_of_admissible G hadm hconn) (fun k _ ↦ hh k) (fun k _ ↦ hJ k) O hβ
    (fun C hC ↦ hS C (hUT hC))

end Series

end TNLean.Lattice.ClusterExpansion
