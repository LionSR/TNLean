/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ClusterExpansion.PathCrossingExpansion
import TNLean.Circuit.EntropySupport

/-!
# The label path of actual nearest-neighbour interactions

The designated support of bond `i` is the pair of its actual endpoint sites.
This supplies nonadjacent commutation in the physical cluster decomposition without requiring
positivity or exact minimal supports. Supporting ALVV, arXiv:1602.08828v2,
`eq:rho-expansion`, source lines 1971–2013.

**Local fix (interaction-label cutoff):** `truncatedExp_nearestNeighbor_eq_crossing_components`
uses components of the label path, rather than the minimal physical support of a word product.
A component of `s` labels is designated on `s + 1` sites. The printed physical-support estimate
is distinct; see `docs/paper-gaps/alvv16_cluster_approximation.tex`.
-/

open Finset SimpleGraph QuantumCircuit

namespace TNLean.Lattice.ClusterExpansion

/-- The overlap graph of the designated nearest-neighbour bond supports is exactly the label
path. Supporting ALVV, arXiv:1602.08828v2, `eq:rho-expansion`, source lines 1971–2013. -/
theorem overlapGraph_nearestNeighbor_eq_pathGraph (N : ℕ) :
    overlapGraph (fun i : Fin N ↦ ({i.castSucc, i.succ} : Finset (Fin (N + 1)))) = pathGraph N := by
  ext i j
  change (i ≠ j ∧ (({i.castSucc, i.succ} : Finset (Fin (N + 1))) ∩
    {j.castSucc, j.succ}).Nonempty) ↔ _
  rw [pathGraph_adj]
  simp only [Finset.Nonempty, mem_inter, mem_insert, mem_singleton]
  simp only [or_and_right, exists_or, exists_eq_left]
  simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
  omega

/-- Actual designated nearest-neighbour supports imply commutation at nonadjacent labels.
No positivity or exact minimal support is assumed. Supporting ALVV,
arXiv:1602.08828v2, `eq:rho-expansion`, source lines 1971–2013. -/
theorem commute_nearestNeighbor_of_not_adj {N q : ℕ}
    (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
      (h i) {i.castSucc, i.succ}) :
    ∀ j k, ¬ (pathGraph N).Adj j k → Commute (h j) (h k) := by
  have hc := commute_of_not_adj_overlapGraph
    (fun i ↦ QuantumCircuit.mem_supportedOperators_of_isSupportedOn (hs i))
  simpa only [overlapGraph_nearestNeighbor_eq_pathGraph] using hc

open Classical in
/-- The actual nearest-neighbour label truncation splits into one no-crossing product and the
sum over its possible crossing components. The side factors are constructed finite sums and
commutation is derived from the physical supports. Supporting the interaction-label version of
ALVV, arXiv:1602.08828v2, `eq:rho-expansion`, source lines 1971–2013. -/
theorem truncatedExp_nearestNeighbor_eq_crossing_components {N q r : ℕ}
    (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
      (h i) {i.castSucc, i.succ}) (p : Fin N) (β : ℝ) :
    let F := fun B : Finset (Fin N) ↦
      ∑ A ∈ B.powerset with NoLargeCluster (pathGraph N) (fun C ↦ r ≤ C.card) A,
        clusterOp h A β
    truncatedExp (pathGraph N) (fun C ↦ r ≤ C.card) h β =
      F {j ∈ univ | j.val < p.val} * F {j ∈ univ | p.val < j.val} +
        ∑ C ∈ (univ : Finset (Finset (Fin N))).filter (fun C : Finset (Fin N) ↦
            p ∈ C ∧ ((pathGraph N).induce (C : Set (Fin N))).Connected ∧ C.card < r),
          clusterOp h C β *
            (F {j ∈ univ | ∀ c ∈ C, j.val + 1 < c.val} *
              F {j ∈ univ | ∀ c ∈ C, c.val + 1 < j.val}) := by
  exact truncatedExp_pathGraph_eq_crossing_components h
    (commute_nearestNeighbor_of_not_adj h hs) p β

end TNLean.Lattice.ClusterExpansion
