/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ProductForm
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import QICLean.Analysis.ClusterExpansion.Truncation
import QICLean.Algebra.OverlapGraph
import QICLean.Analysis.ClusterExpansion.ClusterPart
import QICLean.Analysis.ClusterExpansion.Factorization
import QICLean.Analysis.ClusterExpansion.Percolation
import QICLean.Analysis.ClusterExpansion.Temperature
import QICLean.Analysis.ClusterExpansion.Path

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
* `TNLean.Lattice.ClusterExpansion.commute_of_not_adj_overlapGraph`,
  `TNLean.Lattice.ClusterExpansion.truncatedExp_eq_sum_noncommProd_clusters_overlapGraph`: for
  terms acting on sites and the overlap graph, the commutation hypothesis holds, so `ρ(β, l)` is
  a sum of products over clusters with no further hypothesis.
* `TNLean.Lattice.ClusterExpansion.clusterOp_mem_supportedOperators`: `E_C` acts on the union of
  the supports of the terms of `C`.

## References

* M. B. Hastings, *Solving gapped Hamiltonians locally*, Phys. Rev. B 73 (2006) 085115,
  arXiv:cond-mat/0508554v3, Section IV, lines 1090–1114 and 1256–1279.
-/

open Finset Matrix
open scoped Function

open ClusterExpansion
open SimpleGraph (overlapGraph)

namespace TNLean.Lattice.ClusterExpansion

section Support

open QuantumCircuit

variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [DecidableEq κ] {d : ℕ}

/-- **`E_C` acts on the sites of the terms of `C`.** If each term `h k` acts on the sites
`acts k`, then `E_C` acts on `⋃_{k ∈ C} acts k`. Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1268–1269. -/
theorem clusterOp_mem_supportedOperators {h : κ → Matrix (σ → Fin d) (σ → Fin d) ℂ}
    {acts : κ → Finset σ}
    (hh : ∀ k, h k ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) (acts k : Finset σ))
    (C : Finset κ) (β : ℝ) :
    clusterOp h C β ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) (C.biUnion acts : Finset σ) := by
  refine sum_mem fun D hD ↦ SMulMemClass.smul_mem _ (ManyBody.exp_mem_supportedOperators ?_)
  refine neg_mem (Submodule.smul_of_tower_mem
    (Subalgebra.toSubmodule (ManyBody.supportedOperators _ _).toSubalgebra) β
    (sum_mem fun k hk ↦ ?_))
  exact ManyBody.supportedOperators_mono (coe_subset.2 (subset_biUnion_of_mem acts
    (mem_powerset.1 hD hk))) (hh k)

omit [DecidableEq κ] in
/-- **Terms that do not overlap commute.** If each term `h k` acts on the sites `acts k`, then two
terms that are not adjacent in the overlap graph are equal or act on disjoint sets of sites, so
they commute. This discharges the commutation hypothesis of the cluster products. -/
theorem commute_of_not_adj_overlapGraph {h : κ → Matrix (σ → Fin d) (σ → Fin d) ℂ}
    {acts : κ → Finset σ}
    (hh : ∀ k, h k ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) (acts k : Finset σ)) :
    ∀ j k, ¬ (SimpleGraph.overlapGraph acts).Adj j k → Commute (h j) (h k) := by
  intro j k hjk
  by_cases hjk' : j = k
  · subst hjk'
    exact Commute.refl _
  refine ManyBody.commute_of_mem_supportedOperators_of_disjoint (hh j) (hh k) ?_
  rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.not_nonempty_iff_eq_empty]
  exact fun hne ↦ hjk ⟨hjk', hne⟩

open Classical in
/-- **`ρ(β, l)` as a sum of products over clusters, for terms acting on sites** (Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1108–1110). If each term `h k` acts on the sites
`acts k` and the clusters are those of the overlap graph, then `ρ(β, l) = ∑_A ∏_{C} E_C`, the sum
over the sets `A` of terms with no large cluster of the product over the clusters `C` of `A`, and
each `E_C` acts on `⋃_{k ∈ C} acts k` (`clusterOp_mem_supportedOperators`). -/
theorem truncatedExp_eq_sum_noncommProd_clusters_overlapGraph [Fintype κ]
    (large : Finset κ → Prop) {h : κ → Matrix (σ → Fin d) (σ → Fin d) ℂ}
    {acts : κ → Finset σ}
    (hh : ∀ k, h k ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) (acts k : Finset σ)) (β : ℝ) :
    ClusterExpansion.truncatedExp (SimpleGraph.overlapGraph acts) large h β =
      ∑ A with ClusterExpansion.NoLargeCluster (SimpleGraph.overlapGraph acts) large A,
        (clusters (SimpleGraph.overlapGraph acts) A).noncommProd (fun C ↦ clusterOp h C β)
          (pairwise_commute_clusterOp_clusters _ (commute_of_not_adj_overlapGraph hh) A β) :=
  truncatedExp_eq_sum_noncommProd_clusters _ large (commute_of_not_adj_overlapGraph hh) β

end Support

end TNLean.Lattice.ClusterExpansion
