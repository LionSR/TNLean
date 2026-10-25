/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ClusterExpansion.Truncation
import TNLean.Lattice.ProductForm
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# The truncated operator as a sum of products over clusters

Hastings, *Solving gapped Hamiltonians locally* (arXiv:cond-mat/0508554v3,
`References/cond-mat_0508554/proj3new.tex`, lines 1090–1114), observes that "each term in
`ρ(β, l_proj)` is a product of operators, each operator acting on the sites within a given
cluster", and in the matrix product construction (lines 1256–1279) uses that "the sum of all terms
which include a given cluster is some operator acting on the sites in the cluster". This file
proves the algebraic content of these two remarks.

The terms are labelled by `κ`, and a graph `G` on `κ` records which terms overlap; the product
results assume that terms that do not overlap commute. For a set `A` of terms let
`E_A = clusterOp h A β` be the sum of the terms of the power series of `e^{-βH}` whose set of
letters is exactly `A`; by inclusion and exclusion,
`E_A = ∑_{D ⊆ A} (-1)^{|A \ D|} e^{-β H_D}`. Then

* `ρ(β, l) = ∑_A E_A`, the sum over the sets `A` of terms none of whose clusters is large;
* `E_{A ∪ B} = E_A E_B` when `A` and `B` are disjoint and the terms of `A` commute with those of
  `B`;
* hence `E_A` is the product, in any order, of `E_C` over the clusters `C` of `A`, and
  `ρ(β, l) = ∑_A ∏_{C cluster of A} E_C`;
* `E_C` acts on the sites of the terms of `C`.

## Main results

* `TNLean.Lattice.ClusterExpansion.clusterOp`: the operator `E_A`.
* `TNLean.Lattice.ClusterExpansion.hasSum_words_clusterOp`: `E_A` as the sum of the words whose
  set of letters is `A`, weighted by `(-β)^n / n!`.
* `TNLean.Lattice.ClusterExpansion.truncatedExp_eq_sum_clusterOp`: `ρ(β, l) = ∑_A E_A` over the
  sets of terms with no large cluster.
* `TNLean.Lattice.ClusterExpansion.clusterOp_union`: `E_{A ∪ B} = E_A E_B` for disjoint sets of
  mutually commuting terms.
* `TNLean.Lattice.ClusterExpansion.clusters`, `biUnion_clusters`: the clusters of a set of terms
  partition it.
* `TNLean.Lattice.ClusterExpansion.clusterOp_eq_noncommProd_clusters`: `E_A` as the product of the
  `E_C` over the clusters `C` of `A`.
* `TNLean.Lattice.ClusterExpansion.truncatedExp_eq_sum_noncommProd_clusters`:
  `ρ(β, l) = ∑_A ∏_{C} E_C`.
* `TNLean.Lattice.ClusterExpansion.clusterOp_mem_supportedOperators`: `E_C` acts on the union of
  the supports of the terms of `C`.

## References

* M. B. Hastings, *Solving gapped Hamiltonians locally*, Phys. Rev. B 73 (2006) 085115,
  arXiv:cond-mat/0508554v3, Section IV, lines 1090–1114 and 1256–1279.
-/

open Finset Matrix
open scoped Function

namespace TNLean.Lattice.ClusterExpansion

section Operator

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

/-- The operator `E_A`: the sum of the terms of the power series of `e^{-βH}`, `H = ∑_k h_k`,
whose set of letters is exactly `A`. By inclusion and exclusion over the letters it is
`∑_{D ⊆ A} (-1)^{|A \ D|} e^{-β H_D}` with `H_D = ∑_{k ∈ D} h_k`, the definition used here.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1268–1269. -/
noncomputable def clusterOp (h : κ → Matrix ι ι ℂ) (A : Finset κ) (β : ℝ) : Matrix ι ι ℂ :=
  ∑ D ∈ A.powerset, (-1 : ℂ) ^ #(A \ D) • NormedSpace.exp (-(β • ∑ k ∈ D, h k))

/-- `E_A` is the cluster part with the boundary `Aᶜ`: the words containing every term of `A` and
no other term. -/
theorem clusterOp_eq_clusterPart [Fintype κ] (h : κ → Matrix ι ι ℂ) (A : Finset κ) (β : ℝ) :
    clusterOp h A β = clusterPart (∑ k, h k) h Aᶜ A β := by
  rw [clusterPart_eq_sum_powerset, clusterOp]
  refine Finset.sum_congr rfl fun E hE ↦ ?_
  have h0 : ∑ k, h k - ∑ k ∈ Aᶜ, h k - ∑ k ∈ A, h k = 0 := by
    rw [← Finset.sum_add_sum_compl A h]
    abel
  rw [h0, smul_zero, zero_add, ← Finset.smul_sum, card_sdiff_of_subset (mem_powerset.1 hE)]

/-- **`E_A` as a word series.** The words of length `n` whose set of letters is exactly `A`,
weighted by `(-β)^n / n!`, sum to `E_A`. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1268–1269. -/
theorem hasSum_words_clusterOp [Fintype κ] (h : κ → Matrix ι ι ℂ) (A : Finset κ) (β : ℝ) :
    HasSum (fun n ↦ ((-β) ^ n / n.factorial : ℝ) •
        ∑ w : Fin n → κ with univ.image w = A, (List.ofFn fun i ↦ h (w i)).prod)
      (clusterOp h A β) := by
  rw [clusterOp_eq_clusterPart]
  convert hasSum_words_clusterPart rfl
    (disjoint_left.2 fun _ h h' ↦ mem_compl.1 h h') β using 4 with n
  refine Finset.filter_congr fun w _ ↦ ?_
  constructor
  · rintro rfl
    exact ⟨Subset.rfl, disjoint_left.2 fun _ h h' ↦ mem_compl.1 h' h⟩
  · rintro ⟨h1, h2⟩
    refine Subset.antisymm (fun x hx ↦ ?_) h1
    by_contra hxA
    exact disjoint_left.1 h2 hx (mem_compl.2 hxA)

/-- `E_∅ = 1`. -/
@[simp]
theorem clusterOp_empty (h : κ → Matrix ι ι ℂ) (β : ℝ) : clusterOp h ∅ β = 1 := by
  simp [clusterOp]

end Operator

section Truncation

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (G : SimpleGraph κ) [DecidableRel G.Adj] (large : Finset κ → Prop)

open Classical in
/-- **`ρ(β, l)` as a sum over sets of terms.** The power series of `ρ(β, l)` sums to `∑_A E_A`,
the sum over the sets `A` of terms none of whose clusters is large. The words are grouped by
their set of letters. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1103–1107. -/
theorem hasSum_truncatedExpTerm_clusterOp (h : κ → Matrix ι ι ℂ) (β : ℝ) :
    HasSum (truncatedExpTerm G large h β)
      (∑ A with NoLargeCluster G large A, clusterOp h A β) := by
  have key : ∀ n, truncatedExpTerm G large h β n =
      ∑ A with NoLargeCluster G large A, ((-β) ^ n / n.factorial : ℝ) •
        ∑ w : Fin n → κ with univ.image w = A, (List.ofFn fun i ↦ h (w i)).prod := by
    intro n
    rw [truncatedExpTerm, ← Finset.smul_sum]
    congr 1
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun w : Fin n → κ ↦ univ.image w)
      (t := {A | NoLargeCluster G large A}) (fun w hw ↦ by simpa using hw)]
    refine Finset.sum_congr rfl fun A hA ↦ ?_
    rw [Finset.filter_filter]
    refine Finset.sum_congr (Finset.filter_congr fun w _ ↦ ?_) fun _ _ ↦ rfl
    constructor
    · exact fun hw ↦ hw.2
    · intro hw
      refine ⟨?_, hw⟩
      rw [hw]
      simpa using hA
  rw [funext key]
  exact hasSum_sum fun A _ ↦ hasSum_words_clusterOp h A β

open Classical in
/-- **`ρ(β, l) = ∑_A E_A`**, the sum over the sets `A` of terms none of whose clusters is large.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1103–1107. -/
theorem truncatedExp_eq_sum_clusterOp (h : κ → Matrix ι ι ℂ) (β : ℝ) :
    truncatedExp G large h β = ∑ A with NoLargeCluster G large A, clusterOp h A β :=
  (hasSum_truncatedExpTerm_clusterOp G large h β).tsum_eq

end Truncation

section Factorization

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

/-- **`E_{A ∪ B} = E_A E_B`** for disjoint sets `A`, `B` of terms such that every term of `A`
commutes with every term of `B`. The subsets of `A ∪ B` are the unions `D₁ ∪ D₂` with `D₁ ⊆ A`,
`D₂ ⊆ B`, and `e^{-β (H_{D₁} + H_{D₂})} = e^{-β H_{D₁}} e^{-β H_{D₂}}`. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1108–1110. -/
theorem clusterOp_union (h : κ → Matrix ι ι ℂ) {A B : Finset κ} (hAB : Disjoint A B)
    (hc : ∀ j ∈ A, ∀ k ∈ B, Commute (h j) (h k)) (β : ℝ) :
    clusterOp h (A ∪ B) β = clusterOp h A β * clusterOp h B β := by
  rw [clusterOp, clusterOp, clusterOp, Finset.sum_mul_sum, ← Finset.sum_product']
  symm
  refine Finset.sum_nbij' (fun p ↦ p.1 ∪ p.2) (fun D ↦ (D ∩ A, D ∩ B)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [mem_product, mem_powerset] at hp ⊢
    exact union_subset_union hp.1 hp.2
  · intro D hD
    simp only [mem_product, mem_powerset] at hD ⊢
    exact ⟨inter_subset_right, inter_subset_right⟩
  · intro p hp
    simp only [mem_product, mem_powerset] at hp
    obtain ⟨D₁, D₂⟩ := p
    have h1 : D₂ ∩ A = ∅ :=
      disjoint_iff_inter_eq_empty.1 (hAB.symm.mono_left hp.2)
    have h2 : D₁ ∩ B = ∅ := disjoint_iff_inter_eq_empty.1 (hAB.mono_left hp.1)
    simp only [union_inter_distrib_right, h1, h2, union_empty, empty_union,
      inter_eq_left.2 hp.1, inter_eq_left.2 hp.2]
  · intro D hD
    simp only [mem_powerset] at hD
    simp only [← inter_union_distrib_left, inter_eq_left.2 hD]
  · rintro ⟨D₁, D₂⟩ hp
    simp only [mem_product, mem_powerset] at hp
    have hD : Disjoint D₁ D₂ := (hAB.mono_left hp.1).mono_right hp.2
    have hcD : Commute (-(β • ∑ k ∈ D₁, h k)) (-(β • ∑ k ∈ D₂, h k)) :=
      (((Commute.sum_left _ _ _ fun j hj ↦ Commute.sum_right _ _ _ fun k hk ↦
        hc j (hp.1 hj) k (hp.2 hk)).smul_left β).smul_right β).neg_left.neg_right
    have hcard : #((A ∪ B) \ (D₁ ∪ D₂)) = #(A \ D₁) + #(B \ D₂) := by
      rw [card_sdiff_of_subset (union_subset_union hp.1 hp.2), card_sdiff_of_subset hp.1,
        card_sdiff_of_subset hp.2, card_union_of_disjoint hAB, card_union_of_disjoint hD]
      have := card_le_card hp.1
      have := card_le_card hp.2
      omega
    simp only
    rw [smul_mul_smul_comm, ← pow_add, ← hcard, ← Matrix.exp_add_of_commute _ _ hcD,
      sum_union hD, smul_add, neg_add]

/-- Disjoint sets of mutually commuting terms give commuting operators `E_A`, `E_B`. -/
theorem commute_clusterOp (h : κ → Matrix ι ι ℂ) {A B : Finset κ} (hAB : Disjoint A B)
    (hc : ∀ j ∈ A, ∀ k ∈ B, Commute (h j) (h k)) (β : ℝ) :
    Commute (clusterOp h A β) (clusterOp h B β) := by
  change _ * _ = _ * _
  rw [← clusterOp_union h hAB hc, ← clusterOp_union h hAB.symm
    (fun k hk j hj ↦ (hc j hj k hk).symm), union_comm]

/-- **`E` of a union is the product over the parts.** For a family `S` of pairwise disjoint
sets of terms, with the terms of distinct members commuting, `E_{⋃S}` is the product, in any
order, of `E_C` over `C ∈ S`. -/
theorem clusterOp_biUnion (h : κ → Matrix ι ι ℂ) (S : Finset (Finset κ))
    (hS : (S : Set (Finset κ)).Pairwise fun C C' ↦
      Disjoint C C' ∧ ∀ j ∈ C, ∀ k ∈ C', Commute (h j) (h k)) (β : ℝ) :
    clusterOp h (S.biUnion id) β =
      S.noncommProd (fun C ↦ clusterOp h C β)
        (hS.mono' fun _ _ hCC' ↦ commute_clusterOp h hCC'.1 hCC'.2 β) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert C S hC ih =>
    have hS' : (S : Set (Finset κ)).Pairwise fun C C' ↦
        Disjoint C C' ∧ ∀ j ∈ C, ∀ k ∈ C', Commute (h j) (h k) :=
      hS.mono (coe_subset.2 (subset_insert C S))
    have hCS : ∀ C' ∈ S, Disjoint C C' ∧ ∀ j ∈ C, ∀ k ∈ C', Commute (h j) (h k) :=
      fun C' hC' ↦ hS (mem_insert_self C S) (mem_insert_of_mem hC')
        (fun hCC' ↦ hC (hCC' ▸ hC'))
    rw [noncommProd_insert_of_notMem _ _ _ _ hC, biUnion_insert, id,
      clusterOp_union h ((disjoint_biUnion_right C S id).2 fun C' hC' ↦ (hCS C' hC').1), ih hS']
    intro j hj k hk
    obtain ⟨C', hC', hkC'⟩ := mem_biUnion.1 hk
    exact (hCS C' hC').2 j hj k hkC'

end Factorization

section Clusters

variable {κ : Type*} [Fintype κ] [DecidableEq κ] (G : SimpleGraph κ) [DecidableRel G.Adj]

open Classical in
/-- The clusters of a set `A` of terms: the connected subsets of `A` to which no other term of `A`
is adjacent. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1096–1102. -/
noncomputable def clusters (A : Finset κ) : Finset (Finset κ) :=
  {C ∈ A.powerset | IsCluster G A C}

theorem mem_clusters {A C : Finset κ} : C ∈ clusters G A ↔ IsCluster G A C := by
  classical
  simp only [clusters, mem_filter, mem_powerset, and_iff_right_iff_imp]
  exact fun hC ↦ hC.1

/-- Every term of `A` lies in a cluster of `A`: a connected subset of `A` containing it with the
largest number of terms. -/
theorem exists_isCluster_mem {A : Finset κ} {k : κ} (hk : k ∈ A) :
    ∃ C, IsCluster G A C ∧ k ∈ C := by
  classical
  set T : Finset (Finset κ) := {C ∈ A.powerset | k ∈ C ∧ (G.induce (C : Set κ)).Connected}
  have hT : ({k} : Finset κ) ∈ T := by
    simp only [T, mem_filter, mem_powerset, singleton_subset_iff, mem_singleton, true_and]
    rw [coe_singleton]
    exact ⟨hk, (SimpleGraph.connected_iff _).2 ⟨.of_subsingleton, ⟨⟨k, rfl⟩⟩⟩⟩
  obtain ⟨C, hCT, hmax⟩ := Finset.exists_max_image T card ⟨_, hT⟩
  simp only [T, mem_filter, mem_powerset] at hCT
  refine ⟨C, ⟨hCT.1, hCT.2.2, Finset.disjoint_left.2 fun j hjA hjB ↦ ?_⟩, hCT.2.1⟩
  obtain ⟨hjC, i, hi, hji⟩ := (mem_boundary G).1 hjB
  have hconn : (G.induce ((insert j C : Finset κ) : Set κ)).Connected := by
    have := SimpleGraph.connected_induce_union (G := G) hCT.2.2.preconnected
      (t := {j}) (.of_subsingleton) hi rfl hji.symm
    rwa [coe_insert, Set.insert_eq, Set.union_comm]
  have hmem : insert j C ∈ T := by
    simp only [T, mem_filter, mem_powerset]
    exact ⟨insert_subset hjA hCT.1, mem_insert_of_mem hCT.2.1, hconn⟩
  have := hmax _ hmem
  rw [card_insert_of_notMem hjC] at this
  omega

/-- **The clusters of `A` partition `A`.** -/
theorem biUnion_clusters (A : Finset κ) : (clusters G A).biUnion id = A := by
  refine Finset.Subset.antisymm (biUnion_subset.2 fun C hC ↦ ((mem_clusters G).1 hC).1)
    fun k hk ↦ ?_
  obtain ⟨C, hC, hkC⟩ := exists_isCluster_mem G hk
  exact mem_biUnion.2 ⟨C, (mem_clusters G).2 hC, hkC⟩

/-- Distinct clusters of `A` are disjoint, and no term of one is adjacent to a term of the
other. -/
theorem pairwise_clusters (A : Finset κ) :
    (clusters G A : Set (Finset κ)).Pairwise fun C C' ↦
      Disjoint C C' ∧ ∀ j ∈ C, ∀ k ∈ C', ¬ G.Adj j k := by
  intro C hC C' hC' hne
  rw [mem_coe, mem_clusters] at hC hC'
  have hd : Disjoint C C' := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    by_contra hn
    exact hne (eq_of_isCluster_of_inter_nonempty G hC hC' (nonempty_iff_ne_empty.2 hn))
  refine ⟨hd, fun j hj k hk hjk ↦ ?_⟩
  have hb : k ∈ boundary G C :=
    (mem_boundary G).2 ⟨Finset.disjoint_right.1 hd hk, j, hj, hjk.symm⟩
  exact Finset.disjoint_left.1 hC.2.2 (hC'.1 hk) hb

end Clusters

section ClusterProduct

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (G : SimpleGraph κ) [DecidableRel G.Adj] (large : Finset κ → Prop)

/-- The operators `E_C` of the clusters of `A` commute when non-overlapping terms commute. -/
theorem pairwise_commute_clusterOp_clusters {h : κ → Matrix ι ι ℂ}
    (hcomm : ∀ j k, ¬ G.Adj j k → Commute (h j) (h k)) (A : Finset κ) (β : ℝ) :
    (clusters G A : Set (Finset κ)).Pairwise
      (Commute on fun C ↦ clusterOp h C β) :=
  (pairwise_clusters G A).mono' fun _ _ hCC' ↦
    commute_clusterOp h hCC'.1 (fun j hj k hk ↦ hcomm j k (hCC'.2 j hj k hk)) β

/-- **`E_A` as a product over the clusters of `A`.** If terms that do not overlap commute, then
`E_A` is the product, in any order, of `E_C` over the clusters `C` of `A`; `E_C` is built only
from the terms of `C`. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1108–1110 and
1258–1259. -/
theorem clusterOp_eq_noncommProd_clusters {h : κ → Matrix ι ι ℂ}
    (hcomm : ∀ j k, ¬ G.Adj j k → Commute (h j) (h k)) (A : Finset κ) (β : ℝ) :
    clusterOp h A β =
      (clusters G A).noncommProd (fun C ↦ clusterOp h C β)
        (pairwise_commute_clusterOp_clusters G hcomm A β) := by
  conv_lhs => rw [← biUnion_clusters G A]
  exact clusterOp_biUnion h _ ((pairwise_clusters G A).mono' fun _ _ hCC' ↦
    ⟨hCC'.1, fun j hj k hk ↦ hcomm j k (hCC'.2 j hj k hk)⟩) β

open Classical in
/-- **`ρ(β, l)` as a sum of products over clusters** (Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1108–1110). If terms that do not overlap commute, then
`ρ(β, l) = ∑_A ∏_{C} E_C`, the sum over the sets `A` of terms with no large cluster of the
product over the clusters `C` of `A`. -/
theorem truncatedExp_eq_sum_noncommProd_clusters {h : κ → Matrix ι ι ℂ}
    (hcomm : ∀ j k, ¬ G.Adj j k → Commute (h j) (h k)) (β : ℝ) :
    truncatedExp G large h β =
      ∑ A with NoLargeCluster G large A,
        (clusters G A).noncommProd (fun C ↦ clusterOp h C β)
          (pairwise_commute_clusterOp_clusters G hcomm A β) := by
  rw [truncatedExp_eq_sum_clusterOp]
  exact Finset.sum_congr rfl fun A _ ↦ clusterOp_eq_noncommProd_clusters G hcomm A β

end ClusterProduct

section Support

open QuantumCircuit

variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [DecidableEq κ] {d : ℕ}

/-- **`E_C` acts on the sites of the terms of `C`.** If each term `h k` acts on the sites
`acts k`, then `E_C` acts on `⋃_{k ∈ C} acts k`. Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1268–1269. -/
theorem clusterOp_mem_supportedOperators {h : κ → Matrix (σ → Fin d) (σ → Fin d) ℂ}
    {acts : κ → Finset σ} (hh : ∀ k, h k ∈ supportedOperators d (acts k : Set σ))
    (C : Finset κ) (β : ℝ) :
    clusterOp h C β ∈ supportedOperators d (C.biUnion acts : Set σ) := by
  refine Submodule.sum_mem _ fun D hD ↦ Submodule.smul_mem _ _ (exp_mem_supportedOperators ?_)
  refine Submodule.neg_mem _ (Submodule.smul_of_tower_mem _ β (Submodule.sum_mem _ fun k hk ↦ ?_))
  exact supportedOperators_mono (coe_subset.2 (subset_biUnion_of_mem acts
    (mem_powerset.1 hD hk))) (hh k)

end Support

end TNLean.Lattice.ClusterExpansion
