/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ClusterExpansion.NearestNeighborPath
import TNLean.Lattice.ClusterExpansion.RetainedClusterSupport

/-!
# Physical interval support of the retained nearest-neighbour sums

The actual side sums in the crossing-component expansion are supported on their physical
intervals. Supporting the interaction-label expansion in ALVV, arXiv:1602.08828v2,
`eq:rho-expansion`, source lines 1971–2013.

**Local fix (interaction-label cutoff):** the retained sums in this module use the label-path
selector, not the minimal physical support of a product. The support conclusion is for the
unchanged actual operators with designated two-site interactions; see
`docs/paper-gaps/alvv16_cluster_approximation.tex`.
-/

open Finset SimpleGraph

namespace TNLean.Lattice.ClusterExpansion

open Classical in
/-- A retained sum over actual nearest-neighbour labels in a physical interval acts only on
that interval. The support is designated and need not be minimal. Supporting ALVV,
arXiv:1602.08828v2, `eq:rho-expansion`, source lines 1971–2013. -/
theorem isSupportedOn_retained_nearestNeighbor_interval {N q r : ℕ}
    (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
      (h i) {i.castSucc, i.succ})
    (B : Finset (Fin N)) (a b : ℕ) (hB : ∀ i ∈ B, a ≤ i.val ∧ i.val + 1 < b) (β : ℝ) :
    Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
      (∑ A ∈ B.powerset with NoLargeCluster (pathGraph N) (fun C ↦ r ≤ C.card) A,
        clusterOp h A β) {v ∈ (univ : Finset (Fin (N + 1))) | a ≤ v.val ∧ v.val < b} := by
  apply (isSupportedOn_sum_retained_clusterOp (pathGraph N) (fun C ↦ r ≤ C.card)
    h (fun i ↦ {i.castSucc, i.succ}) hs B β).mono
  intro v hv
  obtain ⟨i, hi, hvi⟩ := mem_biUnion.mp hv
  have hb := hB i hi
  refine mem_filter.mpr ⟨mem_univ _, ?_⟩
  simp only [mem_insert, mem_singleton] at hvi
  rcases hvi with rfl | rfl <;> simp only [Fin.val_castSucc, Fin.val_succ] <;> omega

open Classical in
/-- The actual retained sum of labels strictly left of a crossing bond acts on the left side
of that physical cut. Supporting ALVV, arXiv:1602.08828v2, `eq:rho-expansion`, lines 1971–2013. -/
theorem isSupportedOn_retained_nearestNeighbor_left {N q r : ℕ}
    (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
      (h i) {i.castSucc, i.succ})
    (p : Fin N) (B : Finset (Fin N)) (hB : ∀ i ∈ B, i.val < p.val) (β : ℝ) :
    Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
      (∑ A ∈ B.powerset with NoLargeCluster (pathGraph N) (fun C ↦ r ≤ C.card) A,
        clusterOp h A β) {v ∈ (univ : Finset (Fin (N + 1))) | v.val ≤ p.val} := by
  apply (isSupportedOn_retained_nearestNeighbor_interval h hs B 0 (p.val + 1)
    (fun i hi ↦ ⟨Nat.zero_le _, Nat.add_lt_add_right (hB i hi) 1⟩) β).mono
  exact fun v hv ↦ mem_filter.mpr ⟨mem_univ _, Nat.le_of_lt_succ (mem_filter.mp hv).2.2⟩

open Classical in
/-- The actual retained sum of labels strictly right of a crossing bond acts on the right side
of that physical cut. Supporting ALVV, arXiv:1602.08828v2, `eq:rho-expansion`, lines 1971–2013. -/
theorem isSupportedOn_retained_nearestNeighbor_right {N q r : ℕ}
    (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
      (h i) {i.castSucc, i.succ})
    (p : Fin N) (B : Finset (Fin N)) (hB : ∀ i ∈ B, p.val < i.val) (β : ℝ) :
    Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
      (∑ A ∈ B.powerset with NoLargeCluster (pathGraph N) (fun C ↦ r ≤ C.card) A,
        clusterOp h A β) {v ∈ (univ : Finset (Fin (N + 1))) | p.val < v.val} := by
  apply (isSupportedOn_retained_nearestNeighbor_interval h hs B (p.val + 1) (N + 1)
    (fun i hi ↦ ⟨Nat.succ_le_of_lt (hB i hi), Nat.add_lt_add_right i.isLt 1⟩) β).mono
  exact fun v hv ↦ mem_filter.mpr ⟨mem_univ _, Nat.lt_of_succ_le (mem_filter.mp hv).2.1⟩

end TNLean.Lattice.ClusterExpansion
