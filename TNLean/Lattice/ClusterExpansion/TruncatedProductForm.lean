/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ClusterExpansion.ClusterFactorization

/-!
# The truncated operator in matrix product form

Hastings, *Solving gapped Hamiltonians locally* (arXiv:cond-mat/0508554v3,
`References/cond-mat_0508554/proj3new.tex`, lines 1256–1279), shows that the truncated operator
`ρ(β, l_proj)` "can be exactly written in a matrix product form", the form of eq. `mpf`
(lines 1024–1039). Each term of `ρ(β, l_proj)` is a product of operators on clusters whose sites
are at most `l_proj` apart (lines 1103–1110); the index `α_i` at a site `i` of a cluster records
the cluster, and the terms of a decomposition of the cluster's operator into products of
single-site operators (lines 1259–1272).

This file carries out that construction for terms `h k` acting on the sites `acts k` of a finite
planar domain, the overlap graph of the supports, and clusters counted as large when their
supports contain two sites joined by no walk of length at most `l` (`IsLargeWalk`). By
`truncatedExp_eq_sum_clusterOp`, `ρ(β, l) = ∑_A E_A` over the sets `A` of terms with no large
cluster.

* Terms acting on no site are adjacent to nothing, so each forms a cluster by itself, which is
  not large. Their contribution splits off as a factor `∑_{A₀} E_{A₀}`, a multiple of the
  identity (`truncatedExp_eq_mul`); it has a product form with one coefficient at any site.
* The remaining sets `A` correspond to the families of valid clusters with disjoint supports,
  `A ↦ clusters A`, and the entries of `E_A` factor over the clusters
  (`noncommProd_apply_of_pairwiseDisjoint`, `sum_clusterOp_apply`).
* The index at a site is the cluster containing it, if any, together with a matrix-unit label.
  The coefficient function at a site checks that the recorded cluster is valid and recorded at
  every site of its supports, and at one anchor site of the cluster it carries the matrix element
  of `E_C`. It reads only the sites of the recorded cluster, which are within walk distance `l`
  (`clusterCoeff`, `isLocalCoefficient_clusterCoeff`). The index records the set of terms of the
  cluster rather than only its sites; the matrix-unit labels play the role of the terms of the
  decomposition into single-site operators.

## Main results

* `TNLean.Lattice.ClusterExpansion.IsLargeWalk`: largeness of a set of terms in walk distance.
* `TNLean.Lattice.ClusterExpansion.noncommProd_apply_of_pairwiseDisjoint`: entries of a product
  of operators on disjoint sets of sites.
* `TNLean.Lattice.ClusterExpansion.truncatedExp_eq_mul`: the terms acting on no site split off
  as a factor.
* `TNLean.Lattice.ClusterExpansion.hasProductForm_sum_clusterOp`: the product form of the sum
  over sets of terms acting on some site.
* `TNLean.Lattice.ClusterExpansion.hasProductForm_truncatedExp`: `ρ(β, l)` has a matrix product
  form of range `l`.

**Scope restriction (geometry):** the source uses an arbitrary lattice of `N` sites with a metric
(lines 184 and 1230); this file uses finite planar domains with walk distance, and
`hasProductForm_truncatedExp` assumes the domain is nonempty, as the source's lattice is. The
source's count of the values of each index (lines 1273–1275) is not established. Documented in
`docs/paper-gaps/hastings05_planar_domain_scope.tex`.

## References

* M. B. Hastings, *Solving gapped Hamiltonians locally*, Phys. Rev. B 73 (2006) 085115,
  arXiv:cond-mat/0508554v3, Section IV, eq. `mpf` (lines 1024–1039), lines 1096–1110 and
  1256–1279.
-/

open Finset Matrix QuantumCircuit
open scoped Function

namespace TNLean.Lattice.ClusterExpansion

section Entry

variable {σ ι : Type*} [Fintype σ] [DecidableEq σ] {d : ℕ}

/-- **Entries of a product of operators on disjoint sets of sites.** If the operators `O C`,
`C ∈ S`, act on pairwise disjoint sets `X C`, the `(u, v)` entry of their product is the diagonal
check `u = v` off `⋃_C X C` times the product over `C` of the entries of `O C` between `u` and the
configuration equal to `v` on `X C` and to `u` elsewhere. -/
theorem noncommProd_apply_of_pairwiseDisjoint (X : ι → Finset σ)
    (O : ι → Matrix (σ → Fin d) (σ → Fin d) ℂ) (S : Finset ι)
    (hO : ∀ C ∈ S, O C ∈ supportedOperators d (X C : Set σ))
    (hS : (S : Set ι).PairwiseDisjoint X) (hc : (S : Set ι).Pairwise (Commute on O))
    (u v : σ → Fin d) :
    S.noncommProd O hc u v =
      (∏ j ∈ (S.biUnion X)ᶜ, if u j = v j then 1 else 0) *
        ∏ C ∈ S, O C u (fun j ↦ if j ∈ X C then v j else u j) := by
  classical
  induction S using Finset.induction_on generalizing u with
  | empty => simp [one_apply, Finset.prod_boole, funext_iff]
  | insert C S hC ih =>
    have hS' : (S : Set ι).PairwiseDisjoint X := hS.subset (by simp)
    have hCS : ∀ C' ∈ S, Disjoint (X C) (X C') := fun C' hC' ↦
      hS (by simp) (by simp [hC']) fun h ↦ hC (h ▸ hC')
    have hXC : Disjoint (X C) (S.biUnion X) := (disjoint_biUnion_right _ _ _).2 hCS
    have hO' : ∀ C' ∈ S, O C' ∈ supportedOperators d (X C' : Set σ) :=
      fun C' hC' ↦ hO C' (mem_insert_of_mem hC')
    rw [noncommProd_insert_of_notMem _ _ _ _ hC, Matrix.mul_apply]
    set w : σ → Fin d := fun j ↦ if j ∈ X C then v j else u j with hw
    rw [Finset.sum_eq_single w]
    · rw [ih hO' hS' _ w, biUnion_insert, Finset.prod_insert hC]
      have h1 : (∏ j ∈ (S.biUnion X)ᶜ, if w j = v j then (1 : ℂ) else 0) =
          ∏ j ∈ (X C ∪ S.biUnion X)ᶜ, if u j = v j then 1 else 0 := by
        rw [← Finset.prod_subset (s₁ := (X C ∪ S.biUnion X)ᶜ)
          (compl_subset_compl.2 subset_union_right) fun j hj hj' ↦ ?_]
        · refine Finset.prod_congr rfl fun j hj ↦ ?_
          have : j ∉ X C := fun h ↦ (mem_compl.1 hj) (mem_union_left _ h)
          simp [hw, this]
        · have : j ∈ X C := by
            by_contra hjC
            exact hj' (mem_compl.2 fun h ↦ (mem_union.1 h).elim hjC (mem_compl.1 hj))
          simp [hw, this]
      have h2 : ∀ C' ∈ S, O C' w (fun j ↦ if j ∈ X C' then v j else w j) =
          O C' u (fun j ↦ if j ∈ X C' then v j else u j) := by
        intro C' hC'
        refine apply_eq_apply_of_mem_supportedOperators (hO' C' hC') (fun j hj ↦ ?_)
          (fun j hj ↦ ?_) (fun j hj ↦ ?_) (fun j hj ↦ ?_)
        · have : j ∉ X C := fun h ↦ disjoint_left.1 (hCS C' hC') h hj
          simp [hw, this]
        · simp [show j ∈ X C' from hj]
        · simp [show j ∉ X C' from hj]
        · simp [show j ∉ X C' from hj]
      rw [h1, Finset.prod_congr rfl h2]
      ring
    · intro w' _ hw'
      by_cases hoff : ∃ j ∉ (X C : Set σ), u j ≠ w' j
      · rw [apply_eq_zero_of_mem_supportedOperators (hO C (mem_insert_self C S)) hoff, zero_mul]
      · push Not at hoff
        obtain ⟨j, hj⟩ := Function.ne_iff.1 hw'
        have hjX : j ∈ X C := by
          by_contra hjX
          exact hj (by simp [hw, hjX, hoff j hjX])
        rw [ih hO' hS' _ w', Finset.prod_eq_zero (i := j)
          (mem_compl.2 fun h ↦ disjoint_left.1 hXC hjX h), zero_mul, mul_zero]
        simp only [hw, hjX, ite_true] at hj
        simp [hj]
    · simp

end Entry

section Split

variable {Λ : Finset (ℤ × ℤ)} {q : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- A set `C` of terms is *large in walk distance* when the union of the supports of its terms
contains two sites joined by no walk of length at most `l` in the domain.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1103–1107. -/
def IsLargeWalk (l : ℕ) (acts : κ → Finset (Site Λ)) (C : Finset κ) : Prop :=
  ∃ a ∈ C.biUnion acts, ∃ b ∈ C.biUnion acts, ¬ ∃ p : (domainGraph Λ).Walk a b, p.length ≤ l

/-- Terms acting on no site do not affect whether a set of terms has a large cluster: such a
term is adjacent to nothing, so it forms a cluster by itself, which is not large. -/
theorem noLargeCluster_iff_filter (acts : κ → Finset (Site Λ)) (l : ℕ) (A : Finset κ) :
    NoLargeCluster (overlapGraph acts) (IsLargeWalk l acts) A ↔
      NoLargeCluster (overlapGraph acts) (IsLargeWalk l acts) {k ∈ A | (acts k).Nonempty} := by
  constructor
  · intro hA C hC hlarge
    refine hA C ⟨hC.1.trans (filter_subset _ _), hC.2.1, disjoint_left.2 fun j hjA hjB ↦ ?_⟩
      hlarge
    obtain ⟨-, x, hx⟩ := (mem_boundary_overlapGraph acts).1 hjB
    exact disjoint_left.1 hC.2.2 (mem_filter.2 ⟨hjA, x, (mem_inter.1 hx).1⟩) hjB
  · intro hA C hC hlarge
    obtain ⟨a, ha, -⟩ := id hlarge
    obtain ⟨k, hkC, hak⟩ := mem_biUnion.1 ha
    have hsub : C ⊆ {k ∈ A | (acts k).Nonempty} := by
      intro j hj
      refine mem_filter.2 ⟨hC.1 hj, ?_⟩
      by_contra hj0
      have hne : (⟨j, hj⟩ : (C : Set κ)) ≠ ⟨k, hkC⟩ := fun h ↦
        hj0 ⟨a, by rw [show j = k from congrArg Subtype.val h]; exact hak⟩
      obtain ⟨w, hadj, -, -⟩ :=
        SimpleGraph.Walk.exists_eq_cons_of_ne hne (hC.2.1.preconnected _ _).some
      exact hj0 ((SimpleGraph.comap_adj.1 hadj).2.mono inter_subset_left)
    exact hA C ⟨hsub, hC.2.1, hC.2.2.mono_left (filter_subset _ _)⟩ hlarge

open Classical in
/-- `ρ(β, l)` is the product of the sum of `E_A` over the sets `A` of terms acting on no site
(a multiple of the identity) and the sum of `E_A` over the sets `A` of terms acting on some site
with no large cluster. -/
theorem truncatedExp_eq_mul (acts : κ → Finset (Site Λ))
    (h : κ → Matrix (Configuration Λ q) (Configuration Λ q) ℂ)
    (hh : ∀ k, h k ∈ supportedOperators q (acts k : Set (Site Λ))) (l : ℕ) (β : ℝ) :
    truncatedExp (overlapGraph acts) (IsLargeWalk l acts) h β =
      (∑ A with ∀ k ∈ A, ¬ (acts k).Nonempty, clusterOp h A β) *
        ∑ A with (∀ k ∈ A, (acts k).Nonempty) ∧
          NoLargeCluster (overlapGraph acts) (IsLargeWalk l acts) A, clusterOp h A β := by
  rw [truncatedExp_eq_sum_clusterOp, Finset.sum_mul_sum, ← Finset.sum_product']
  have hf0 : ∀ A₀ A₁ : Finset κ, (∀ k ∈ A₀, ¬ (acts k).Nonempty) →
      (∀ k ∈ A₁, (acts k).Nonempty) → {k ∈ A₀ ∪ A₁ | ¬ (acts k).Nonempty} = A₀ := by
    intro A₀ A₁ h₀ h₁
    rw [filter_union, filter_true_of_mem h₀, filter_false_of_mem fun k hk h ↦ h (h₁ k hk),
      union_empty]
  have hf1 : ∀ A₀ A₁ : Finset κ, (∀ k ∈ A₀, ¬ (acts k).Nonempty) →
      (∀ k ∈ A₁, (acts k).Nonempty) → {k ∈ A₀ ∪ A₁ | (acts k).Nonempty} = A₁ := by
    intro A₀ A₁ h₀ h₁
    rw [filter_union, filter_true_of_mem h₁, filter_false_of_mem h₀, empty_union]
  refine Finset.sum_nbij' (fun A ↦ ({k ∈ A | ¬ (acts k).Nonempty}, {k ∈ A | (acts k).Nonempty}))
    (fun p ↦ p.1 ∪ p.2) ?_ ?_ ?_ ?_ ?_
  · intro A hA
    simp only [mem_filter, mem_univ, true_and, mem_product] at hA ⊢
    exact ⟨fun k hk ↦ hk.2, fun k hk ↦ hk.2,
      (noLargeCluster_iff_filter acts l A).1 hA⟩
  · rintro ⟨A₀, A₁⟩ hp
    simp only [mem_filter, mem_univ, true_and, mem_product] at hp ⊢
    rw [noLargeCluster_iff_filter, hf1 A₀ A₁ hp.1 hp.2.1]
    exact hp.2.2
  · intro A _
    exact (union_comm _ _).trans (filter_union_filter_not_eq (fun k ↦ (acts k).Nonempty) A)
  · rintro ⟨A₀, A₁⟩ hp
    simp only [mem_filter, mem_univ, true_and, mem_product] at hp
    exact Prod.ext (hf0 A₀ A₁ hp.1 hp.2.1) (hf1 A₀ A₁ hp.1 hp.2.1)
  · intro A _
    rw [← clusterOp_union h (disjoint_filter_filter_not _ _ _).symm fun j hj k _ ↦ ?_,
      (union_comm _ _).trans (filter_union_filter_not_eq (fun k ↦ (acts k).Nonempty) A)]
    exact commute_of_not_adj_overlapGraph hh j k fun hadj ↦
      (mem_filter.1 hj).2 (hadj.2.mono inter_subset_left)

end Split

section Core

variable {Λ : Finset (ℤ × ℤ)} {q : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
  (acts : κ → Finset (Site Λ)) (l : ℕ)

/-- A *valid cluster*: a nonempty connected set of terms, each acting on some site, whose
supports do not contain two sites farther apart than `l` in walk distance. These are the clusters
recorded by the indices of the matrix product form.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1096–1107. -/
def IsValidCluster (C : Finset κ) : Prop :=
  (∀ k ∈ C, (acts k).Nonempty) ∧ ((overlapGraph acts).induce (C : Set κ)).Connected ∧
    ¬ IsLargeWalk l acts C

open Classical in
/-- The families of valid clusters with pairwise disjoint supports. -/
noncomputable def validFamilies : Finset (Finset (Finset κ)) :=
  {S | (∀ C ∈ S, IsValidCluster acts l C) ∧
    (S : Set (Finset κ)).PairwiseDisjoint (·.biUnion acts)}

variable {acts l}

theorem mem_validFamilies {S : Finset (Finset κ)} :
    S ∈ validFamilies acts l ↔ (∀ C ∈ S, IsValidCluster acts l C) ∧
      (S : Set (Finset κ)).PairwiseDisjoint (·.biUnion acts) := by
  classical
  simp [validFamilies]

omit [Fintype κ] [DecidableEq κ] in
/-- The supports of a valid cluster form a nonempty set of sites. -/
theorem IsValidCluster.nonempty_biUnion {C : Finset κ} (hC : IsValidCluster acts l C) :
    (C.biUnion acts).Nonempty := by
  obtain ⟨⟨k, hk⟩⟩ := hC.2.1.nonempty
  obtain ⟨x, hx⟩ := hC.1 k hk
  exact ⟨x, mem_biUnion.2 ⟨k, hk, hx⟩⟩

omit [Fintype κ] [DecidableEq κ] in
/-- Two sites in the supports of a valid cluster are joined by a walk of length at most `l`. -/
theorem IsValidCluster.exists_walk {C : Finset κ} (hC : IsValidCluster acts l C)
    {a b : Site Λ} (ha : a ∈ C.biUnion acts) (hb : b ∈ C.biUnion acts) :
    ∃ p : (domainGraph Λ).Walk a b, p.length ≤ l := by
  by_contra hw
  exact hC.2.2 ⟨a, ha, b, hb, hw⟩

/-- A member of a family of valid clusters with disjoint supports is a cluster of the union of
the family. -/
theorem isCluster_of_mem_validFamilies {S : Finset (Finset κ)} (hS : S ∈ validFamilies acts l)
    {C : Finset κ} (hC : C ∈ S) : IsCluster (overlapGraph acts) (S.biUnion id) C := by
  rw [mem_validFamilies] at hS
  refine ⟨subset_biUnion_of_mem id hC, (hS.1 C hC).2.1, disjoint_left.2 fun j hjA hjB ↦ ?_⟩
  obtain ⟨C', hC', hjC'⟩ := mem_biUnion.1 hjA
  obtain ⟨hjC, x, hx⟩ := (mem_boundary_overlapGraph acts).1 hjB
  by_cases hCC' : C' = C
  · exact hjC (hCC' ▸ hjC')
  exact disjoint_left.1 (hS.2 hC' hC hCC') (mem_biUnion.2 ⟨j, hjC', (mem_inter.1 hx).1⟩)
    (mem_inter.1 hx).2

/-- The clusters of the union of a family of valid clusters with disjoint supports are the
members of the family. -/
theorem clusters_biUnion_of_mem_validFamilies {S : Finset (Finset κ)}
    (hS : S ∈ validFamilies acts l) : clusters (overlapGraph acts) (S.biUnion id) = S := by
  ext D
  rw [mem_clusters]
  refine ⟨fun hD ↦ ?_, isCluster_of_mem_validFamilies hS⟩
  obtain ⟨⟨k, hk⟩⟩ := hD.2.1.nonempty
  obtain ⟨C, hC, hkC⟩ := mem_biUnion.1 (hD.1 hk)
  rwa [eq_of_isCluster_of_inter_nonempty _ hD (isCluster_of_mem_validFamilies hS hC)
    ⟨k, mem_inter.2 ⟨hk, hkC⟩⟩]

/-- The clusters of any set of terms have pairwise disjoint supports. -/
theorem pairwiseDisjoint_clusters (A : Finset κ) :
    (clusters (overlapGraph acts) A : Set (Finset κ)).PairwiseDisjoint (·.biUnion acts) := by
  intro C hC C' hC' hne
  obtain ⟨hdisj, hnadj⟩ := pairwise_clusters _ A hC hC' hne
  refine disjoint_left.2 fun x hx hx' ↦ ?_
  obtain ⟨j, hj, hxj⟩ := mem_biUnion.1 hx
  obtain ⟨k, hk, hxk⟩ := mem_biUnion.1 hx'
  exact hnadj j hj k hk ⟨fun h ↦ disjoint_left.1 hdisj hj (h ▸ hk), x, mem_inter.2 ⟨hxj, hxk⟩⟩

open Classical in
/-- **The sum over sets of terms as a sum over families of clusters.** The sets `A` of terms
acting on some site with no large cluster correspond to the families of valid clusters with
disjoint supports, `A ↦ clusters A`, and the entries of `E_A` factor over the clusters.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1108–1110 and 1268–1270. -/
theorem sum_clusterOp_apply {h : κ → Matrix (Configuration Λ q) (Configuration Λ q) ℂ}
    (hh : ∀ k, h k ∈ supportedOperators q (acts k : Set (Site Λ))) (β : ℝ)
    (u v : Configuration Λ q) :
    (∑ A with (∀ k ∈ A, (acts k).Nonempty) ∧
        NoLargeCluster (overlapGraph acts) (IsLargeWalk l acts) A, clusterOp h A β) u v =
      ∑ S ∈ validFamilies acts l,
        (∏ j ∈ (S.biUnion (·.biUnion acts))ᶜ, if u j = v j then 1 else 0) *
          ∏ C ∈ S, clusterOp h C β u (fun j ↦ if j ∈ C.biUnion acts then v j else u j) := by
  rw [Matrix.sum_apply]
  refine Finset.sum_nbij' (fun A ↦ clusters (overlapGraph acts) A) (fun S ↦ S.biUnion id)
    ?_ ?_ ?_ ?_ ?_
  · intro A hA
    simp only [mem_filter, mem_univ, true_and] at hA
    rw [mem_validFamilies]
    refine ⟨fun C hC ↦ ?_, pairwiseDisjoint_clusters A⟩
    rw [mem_clusters] at hC
    exact ⟨fun k hk ↦ hA.1 k (hC.1 hk), hC.2.1, hA.2 C hC⟩
  · intro S hS
    simp only [mem_filter, mem_univ, true_and]
    refine ⟨fun k hk ↦ ?_, fun D hD ↦ ?_⟩
    · obtain ⟨C, hC, hkC⟩ := mem_biUnion.1 hk
      exact ((mem_validFamilies.1 hS).1 C hC).1 k hkC
    · rw [← mem_clusters, clusters_biUnion_of_mem_validFamilies hS] at hD
      exact ((mem_validFamilies.1 hS).1 D hD).2.2
  · intro A _
    exact biUnion_clusters _ A
  · intro S hS
    exact clusters_biUnion_of_mem_validFamilies hS
  · intro A _
    rw [clusterOp_eq_noncommProd_clusters _ (commute_of_not_adj_overlapGraph hh) A β,
      noncommProd_apply_of_pairwiseDisjoint _ _ _
        (fun C _ ↦ clusterOp_mem_supportedOperators hh C β) (pairwiseDisjoint_clusters A)]

variable (acts l)

/-- The *anchor* of a set of terms: a chosen site of the union of their supports, at which the
coefficient carrying the matrix element of `E_C` is placed. When the supports are empty, which
does not happen for a valid cluster, it is the given site `i`, so no site of the domain need be
chosen in advance. -/
noncomputable def anchor (C : Finset κ) (i : Site Λ) : Site Λ :=
  if hC : (C.biUnion acts).Nonempty then hC.choose else i

open Classical in
/-- The coefficient function at site `i`. The index at a site records the cluster containing it,
if any, and a matrix-unit label. A site recording no cluster checks that its label is diagonal. A
site recording the cluster `C` checks that `C` is valid, that `i` lies in its supports and that
every site of its supports records `C`; at the anchor of `C` it carries the matrix element of
`E_C` read off the labels on the supports of `C`.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1259–1272. -/
noncomputable def clusterCoeff (h : κ → Matrix (Configuration Λ q) (Configuration Λ q) ℂ)
    (β : ℝ) (i : Site Λ) (α : Site Λ → Option (Finset κ) × (Fin q × Fin q)) : ℂ :=
  (α i).1.elim (if (α i).2.1 = (α i).2.2 then 1 else 0) fun C ↦
    if IsValidCluster acts l C ∧ i ∈ C.biUnion acts ∧ ∀ j ∈ C.biUnion acts, (α j).1 = some C then
      if i = anchor acts C i then
        clusterOp h C β (fun j ↦ if j ∈ C.biUnion acts then (α j).2.1 else (α i).2.1)
          (fun j ↦ if j ∈ C.biUnion acts then (α j).2.2 else (α i).2.1)
      else 1
    else 0

variable {acts l}

omit [Fintype κ] in
/-- The coefficient function at `i` reads only indices at sites within walk distance `l` of `i`:
the sites of the supports of the cluster recorded at `i`. -/
theorem isLocalCoefficient_clusterCoeff
    (h : κ → Matrix (Configuration Λ q) (Configuration Λ q) ℂ) (β : ℝ) (i : Site Λ) :
    IsLocalCoefficient l i (clusterCoeff acts l h β i) := by
  classical
  intro α α' hαα'
  have hi : α i = α' i := hαα' i ⟨.nil, Nat.zero_le _⟩
  unfold clusterCoeff
  rw [hi]
  rcases hc : (α' i).1 with _ | C
  · rfl
  simp only [Option.elim]
  by_cases hv : IsValidCluster acts l C ∧ i ∈ C.biUnion acts
  · have hnear : ∀ j ∈ C.biUnion acts, α j = α' j :=
      fun j hj ↦ hαα' j (hv.1.exists_walk hv.2 hj)
    have hrow : (fun j ↦ if j ∈ C.biUnion acts then (α j).2.1 else (α' i).2.1) =
        fun j ↦ if j ∈ C.biUnion acts then (α' j).2.1 else (α' i).2.1 := by
      funext j
      split_ifs with hj
      · rw [hnear j hj]
      · rfl
    have hcol : (fun j ↦ if j ∈ C.biUnion acts then (α j).2.2 else (α' i).2.1) =
        fun j ↦ if j ∈ C.biUnion acts then (α' j).2.2 else (α' i).2.1 := by
      funext j
      split_ifs with hj
      · rw [hnear j hj]
      · rfl
    have hall : (∀ j ∈ C.biUnion acts, (α j).1 = some C) ↔
        ∀ j ∈ C.biUnion acts, (α' j).1 = some C :=
      forall₂_congr fun j hj ↦ by rw [hnear j hj]
    simp only [hrow, hcol, hall]
  · have hn : ∀ γ : Site Λ → Option (Finset κ) × (Fin q × Fin q),
        ¬ (IsValidCluster acts l C ∧ i ∈ C.biUnion acts ∧
          ∀ j ∈ C.biUnion acts, (γ j).1 = some C) := fun _ h ↦ hv ⟨h.1, h.2.1⟩
    simp only [hn, ↓reduceIte]

/-- The entries of a sum `∑_α F(α) ⊗_j |a_j⟩⟨b_j|` over indices carrying a matrix-unit label:
the labels are forced to be the row and column configurations. -/
theorem sum_smul_rectKronecker_single_apply {I : Type*} [Fintype I]
    (F : (Site Λ → I × (Fin q × Fin q)) → ℂ) (u v : Configuration Λ q) :
    (∑ α, F α • rectKronecker fun j ↦ single (α j).2.1 (α j).2.2 (1 : ℂ)) u v =
      ∑ c : Site Λ → I, F fun j ↦ (c j, (u j, v j)) := by
  classical
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, rectKronecker_apply, smul_eq_mul]
  rw [← (Equiv.arrowProdEquivProdArrow _ _ _).symm.sum_comp, Fintype.sum_prod_type]
  refine Fintype.sum_congr _ _ fun c ↦ ?_
  rw [Finset.sum_eq_single (fun j ↦ (u j, v j))]
  · simp [Equiv.arrowProdEquivProdArrow]
  · intro ℓ _ hℓ
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hℓ
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ j) ?_)
    simp only [Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk]
    rw [single_apply]
    split_ifs with h
    · exact absurd (Prod.ext h.1 h.2) hj
    · rfl
  · simp

omit [Fintype κ] [DecidableEq κ] in
/-- The anchor of a valid cluster is a fixed site of its supports, independent of `i`. -/
theorem anchor_eq {C : Finset κ} (hC : IsValidCluster acts l C) (i : Site Λ) :
    anchor acts C i = hC.nonempty_biUnion.choose :=
  dite_eq_left hC.nonempty_biUnion

variable (acts l)

/-- An assignment of clusters to sites is *consistent* when every recorded cluster is valid,
contains the site in its supports, and is recorded at every site of its supports. -/
def IsClusterAssignment (c : Site Λ → Option (Finset κ)) : Prop :=
  ∀ i C, c i = some C →
    IsValidCluster acts l C ∧ i ∈ C.biUnion acts ∧ ∀ j ∈ C.biUnion acts, c j = some C

open Classical in
/-- The clusters recorded by an assignment of clusters to sites. -/
noncomputable def recordedClusters (c : Site Λ → Option (Finset κ)) : Finset (Finset κ) :=
  {C | ∃ i, c i = some C}

open Classical in
/-- The assignment recording at each site the member of `S` whose supports contain it. -/
noncomputable def clusterAssignment (S : Finset (Finset κ)) (i : Site Λ) : Option (Finset κ) :=
  if hS : ∃ C ∈ S, i ∈ C.biUnion acts then some hS.choose else none

variable {acts l}

theorem mem_recordedClusters {c : Site Λ → Option (Finset κ)} {C : Finset κ} :
    C ∈ recordedClusters c ↔ ∃ i, c i = some C := by
  classical
  simp [recordedClusters]

omit [Fintype κ] [DecidableEq κ] in
theorem clusterAssignment_eq_some_of_mem {S : Finset (Finset κ)}
    (hS : (S : Set (Finset κ)).PairwiseDisjoint (·.biUnion acts)) {C : Finset κ} (hC : C ∈ S)
    {i : Site Λ} (hi : i ∈ C.biUnion acts) : clusterAssignment acts S i = some C := by
  unfold clusterAssignment
  split_ifs with hex
  · obtain ⟨hC', hi'⟩ := hex.choose_spec
    by_contra hne
    exact disjoint_left.1 (hS hC' hC fun h ↦ hne (congrArg some h)) hi' hi
  · exact absurd ⟨C, hC, hi⟩ hex

omit [Fintype κ] [DecidableEq κ] in
theorem clusterAssignment_eq_some {S : Finset (Finset κ)} {C : Finset κ} {i : Site Λ}
    (h : clusterAssignment acts S i = some C) : C ∈ S ∧ i ∈ C.biUnion acts := by
  unfold clusterAssignment at h
  split_ifs at h with hex
  · obtain rfl := Option.some.inj h
    exact hex.choose_spec

omit [Fintype κ] [DecidableEq κ] in
theorem clusterAssignment_eq_none {S : Finset (Finset κ)} {i : Site Λ}
    (h : ∀ C ∈ S, i ∉ C.biUnion acts) : clusterAssignment acts S i = none := by
  unfold clusterAssignment
  split_ifs with hex
  · obtain ⟨C, hC, hi⟩ := hex
    exact absurd hi (h C hC)
  · rfl

theorem recordedClusters_mem_validFamilies {c : Site Λ → Option (Finset κ)}
    (hc : IsClusterAssignment acts l c) : recordedClusters c ∈ validFamilies acts l := by
  rw [mem_validFamilies]
  refine ⟨fun C hC ↦ ?_, fun C hC C' hC' hne ↦ ?_⟩
  · obtain ⟨i, hi⟩ := mem_recordedClusters.1 hC
    exact (hc i C hi).1
  · obtain ⟨i, hi⟩ := mem_recordedClusters.1 hC
    obtain ⟨i', hi'⟩ := mem_recordedClusters.1 hC'
    refine disjoint_left.2 fun x hx hx' ↦ hne ?_
    exact Option.some.inj (((hc i C hi).2.2 x hx).symm.trans ((hc i' C' hi').2.2 x hx'))

open Classical in
/-- **The sum over assignments.** For fixed labels, the products of the coefficient functions
vanish except at consistent assignments of clusters to sites, which correspond to the families
of valid clusters with disjoint supports; at such an assignment the product is the diagonal check
off the supports times the matrix elements of the `E_C`. -/
theorem sum_prod_clusterCoeff {h : κ → Matrix (Configuration Λ q) (Configuration Λ q) ℂ}
    (hh : ∀ k, h k ∈ supportedOperators q (acts k : Set (Site Λ))) (β : ℝ)
    (u v : Configuration Λ q) :
    ∑ c : Site Λ → Option (Finset κ), ∏ i, clusterCoeff acts l h β i (fun j ↦ (c j, (u j, v j))) =
      ∑ S ∈ validFamilies acts l,
        (∏ j ∈ (S.biUnion (·.biUnion acts))ᶜ, if u j = v j then 1 else 0) *
          ∏ C ∈ S, clusterOp h C β u (fun j ↦ if j ∈ C.biUnion acts then v j else u j) := by
  have hzero : ∀ c : Site Λ → Option (Finset κ),
      ∏ i, clusterCoeff acts l h β i (fun j ↦ (c j, (u j, v j))) ≠ 0 →
        IsClusterAssignment acts l c := by
    intro c hc i C hci
    by_contra hn
    exact hc (Finset.prod_eq_zero (mem_univ i)
      (by simp only [clusterCoeff, hci, Option.elim, hn, ↓reduceIte]))
  have hval : ∀ S ∈ validFamilies acts l,
      ∏ i, clusterCoeff acts l h β i (fun j ↦ (clusterAssignment acts S j, (u j, v j))) =
        (∏ j ∈ (S.biUnion (·.biUnion acts))ᶜ, if u j = v j then 1 else 0) *
          ∏ C ∈ S, clusterOp h C β u (fun j ↦ if j ∈ C.biUnion acts then v j else u j) := by
    intro S hS
    rw [mem_validFamilies] at hS
    rw [← Finset.prod_mul_prod_compl (S.biUnion (·.biUnion acts)), mul_comm]
    congr 1
    · refine Finset.prod_congr rfl fun i hi ↦ ?_
      have hn : clusterAssignment acts S i = none := clusterAssignment_eq_none
        fun C hC hiC ↦ mem_compl.1 hi (mem_biUnion.2 ⟨C, hC, hiC⟩)
      simp only [clusterCoeff, hn, Option.elim]
    · rw [Finset.prod_biUnion hS.2]
      refine Finset.prod_congr rfl fun C hC ↦ ?_
      have hc : ∀ i ∈ C.biUnion acts, clusterAssignment acts S i = some C :=
        fun i hi ↦ clusterAssignment_eq_some_of_mem hS.2 hC hi
      have hcoeff : ∀ i ∈ C.biUnion acts,
          clusterCoeff acts l h β i (fun j ↦ (clusterAssignment acts S j, (u j, v j))) =
            if i = (hS.1 C hC).nonempty_biUnion.choose then
              clusterOp h C β (fun j ↦ if j ∈ C.biUnion acts then u j else u i)
                (fun j ↦ if j ∈ C.biUnion acts then v j else u i)
            else 1 := by
        intro i hi
        have hcnd : IsValidCluster acts l C ∧ i ∈ C.biUnion acts ∧
            ∀ j ∈ C.biUnion acts, clusterAssignment acts S j = some C := ⟨hS.1 C hC, hi, hc⟩
        simp only [clusterCoeff, hc i hi, Option.elim, anchor_eq (hS.1 C hC)]
        split_ifs <;> rfl
      have hanc := (hS.1 C hC).nonempty_biUnion.choose_spec
      rw [Finset.prod_congr rfl hcoeff, Finset.prod_ite_eq']
      simp only [hanc, ↓reduceIte]
      refine apply_eq_apply_of_mem_supportedOperators (clusterOp_mem_supportedOperators hh C β)
        (fun j hj ↦ ?_) (fun j hj ↦ ?_) (fun j hj ↦ ?_) (fun j hj ↦ ?_)
      · simp [show j ∈ C.biUnion acts from hj]
      · simp [show j ∈ C.biUnion acts from hj]
      · simp [show j ∉ C.biUnion acts from hj]
      · simp [show j ∉ C.biUnion acts from hj]
  have hleft : ∀ c, IsClusterAssignment acts l c →
      clusterAssignment acts (recordedClusters c) = c := by
    intro c hc
    have hpd := (mem_validFamilies.1 (recordedClusters_mem_validFamilies hc)).2
    funext i
    rcases hci : c i with _ | C
    · refine clusterAssignment_eq_none fun C hC hiC ↦ ?_
      obtain ⟨i', hi'⟩ := mem_recordedClusters.1 hC
      have := (hc i' C hi').2.2 i hiC
      rw [hci] at this
      exact absurd this (by simp)
    · exact clusterAssignment_eq_some_of_mem hpd (mem_recordedClusters.2 ⟨i, hci⟩)
        (hc i C hci).2.1
  rw [← Finset.sum_filter_of_ne fun c _ hc ↦ hzero c hc]
  refine Finset.sum_nbij' recordedClusters (clusterAssignment acts) ?_ ?_ ?_ ?_ ?_
  · intro c hc
    exact recordedClusters_mem_validFamilies (mem_filter.1 hc).2
  · intro S hS
    rw [mem_validFamilies] at hS
    refine mem_filter.2 ⟨mem_univ _, fun i C he ↦ ?_⟩
    obtain ⟨hC, hi⟩ := clusterAssignment_eq_some he
    exact ⟨hS.1 C hC, hi, fun j hj ↦ clusterAssignment_eq_some_of_mem hS.2 hC hj⟩
  · intro c hc
    exact hleft c (mem_filter.1 hc).2
  · intro S hS
    rw [mem_validFamilies] at hS
    ext C
    rw [mem_recordedClusters]
    constructor
    · rintro ⟨i, hi⟩
      exact (clusterAssignment_eq_some hi).1
    · intro hC
      obtain ⟨x, hx⟩ := (hS.1 C hC).nonempty_biUnion
      exact ⟨x, clusterAssignment_eq_some_of_mem hS.2 hC hx⟩
  · intro c hc
    have hc' := (mem_filter.1 hc).2
    rw [← hval _ (recordedClusters_mem_validFamilies hc'), hleft c hc']

/-- **The product form of the clusters of terms acting on some site.** The sum of `E_A` over the
sets `A` of terms acting on some site with no cluster large in walk distance has a matrix product
form of range `l`. The index at a site records the cluster containing it, if any, and a
matrix-unit label. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1256–1279. -/
theorem hasProductForm_sum_clusterOp
    {h : κ → Matrix (Configuration Λ q) (Configuration Λ q) ℂ}
    (hh : ∀ k, h k ∈ supportedOperators q (acts k : Set (Site Λ))) (β : ℝ) :
    open Classical in HasProductForm Λ q l
      (∑ A with (∀ k ∈ A, (acts k).Nonempty) ∧
        NoLargeCluster (overlapGraph acts) (IsLargeWalk l acts) A, clusterOp h A β) := by
  classical
  let e := Fintype.equivFin (Finset κ)
  refine ⟨{ Index := Option (Fin (Fintype.card (Finset κ))) × (Fin q × Fin q)
            siteOp := fun _ a ↦ single a.2.1 a.2.2 1
            coeff := fun i α ↦ clusterCoeff acts l h β i fun j ↦ ((α j).1.map e.symm, (α j).2)
            coeff_local := fun i α α' hαα' ↦
              isLocalCoefficient_clusterCoeff h β i _ _ fun j hj ↦ by rw [hαα' j hj]
            eq_sum := ?_ }⟩
  ext u v
  rw [sum_clusterOp_apply hh β u v, ← sum_prod_clusterCoeff hh β u v,
    sum_smul_rectKronecker_single_apply]
  exact (Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl _) (Equiv.optionCongr e.symm)) _ _
    fun c ↦ rfl).symm

end Core

section Main

variable {Λ : Finset (ℤ × ℤ)} {q : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **The truncated operator in matrix product form** (Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1256–1279). For terms `h k` acting on the sites `acts k` of a nonempty
finite planar domain, terms adjacent when their supports meet, and clusters large when their
supports contain two sites farther apart than `l` in walk distance, the truncated operator
`ρ(β, l)` has a matrix product form of range `l`. No Hermiticity, no nonempty supports and no
connectivity of the domain are assumed. -/
theorem hasProductForm_truncatedExp [Nonempty (Site Λ)] (acts : κ → Finset (Site Λ))
    (h : κ → Matrix (Configuration Λ q) (Configuration Λ q) ℂ)
    (hh : ∀ k, h k ∈ supportedOperators q (acts k : Set (Site Λ))) (l : ℕ) (β : ℝ) :
    HasProductForm Λ q l (truncatedExp (overlapGraph acts) (IsLargeWalk l acts) h β) := by
  classical
  rw [truncatedExp_eq_mul acts h hh l β]
  refine HasProductForm.mul ?_ (hasProductForm_sum_clusterOp hh β)
  refine hasProductForm_of_mem_supportedOperators_radius (X := ∅) (Classical.arbitrary _)
    (by simp) ?_
  refine Submodule.sum_mem _ fun A hA ↦
    supportedOperators_mono ?_ (clusterOp_mem_supportedOperators hh A β)
  intro x hx
  obtain ⟨k, hk, hxk⟩ := mem_biUnion.1 hx
  exact absurd ⟨x, hxk⟩ ((mem_filter.1 hA).2 k hk)

end Main

end TNLean.Lattice.ClusterExpansion
