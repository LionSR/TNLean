/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ClusterExpansion.CrossingComponentSum
import TNLean.Lattice.ClusterExpansion.PathSeparation

/-!
# The actual path expansion grouped by the crossing component

The two side factors are constructed as retained finite sums on the actual allowed label sets.
Supporting the interaction-label version of ALVV, arXiv:1602.08828v2,
`eq:rho-expansion`, source lines 1971–2013. No operator rank or matrix product representation
is assumed here.

**Local fix (interaction-label cutoff):** this decomposition uses components of the actual
label path. It does not identify the resulting truncation with the source's minimal physical-site
support selector; see `docs/paper-gaps/alvv16_cluster_approximation.tex`.
-/

open Finset SimpleGraph

namespace TNLean.Lattice.ClusterExpansion

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N r : ℕ}

open Classical in
/-- Exact no-crossing and crossing-component decomposition on the actual label path.
All side factors are actual retained-support sums. The case `r = 1` has no crossing component.
Supporting the interaction-label expansion in ALVV, arXiv:1602.08828v2,
`eq:rho-expansion`, source lines 1971–2013. -/
theorem truncatedExp_pathGraph_eq_crossing_components
    (h : Fin N → Matrix ι ι ℂ)
    (hcomm : ∀ j k, ¬ (pathGraph N).Adj j k → Commute (h j) (h k))
    (p : Fin N) (β : ℝ) :
    truncatedExp (pathGraph N) (fun C ↦ r ≤ C.card) h β =
      (∑ A ∈ ({j ∈ (univ : Finset (Fin N)) | j.val < p.val}).powerset
          with NoLargeCluster (pathGraph N) (fun C ↦ r ≤ C.card) A, clusterOp h A β) *
        (∑ A ∈ ({j ∈ (univ : Finset (Fin N)) | p.val < j.val}).powerset
          with NoLargeCluster (pathGraph N) (fun C ↦ r ≤ C.card) A, clusterOp h A β) +
      ∑ C ∈ (univ : Finset (Finset (Fin N))).filter (fun C : Finset (Fin N) ↦
          p ∈ C ∧ ((pathGraph N).induce (C : Set (Fin N))).Connected ∧ C.card < r),
        clusterOp h C β *
          ((∑ A ∈ ({j ∈ (univ : Finset (Fin N)) |
                ∀ c ∈ C, j.val + 1 < c.val}).powerset
              with NoLargeCluster (pathGraph N) (fun D ↦ r ≤ D.card) A, clusterOp h A β) *
            ∑ A ∈ ({j ∈ (univ : Finset (Fin N)) |
                ∀ c ∈ C, c.val + 1 < j.val}).powerset
              with NoLargeCluster (pathGraph N) (fun D ↦ r ≤ D.card) A, clusterOp h A β) := by
  classical
  let good := NoLargeCluster (pathGraph N) (fun C : Finset (Fin N) ↦ r ≤ C.card)
  have hsplit : (∑ A : Finset (Fin N) with good A, clusterOp h A β) =
      (∑ A : Finset (Fin N) with good A ∧ p ∉ A, clusterOp h A β) +
        ∑ A : Finset (Fin N) with good A ∧ p ∈ A, clusterOp h A β := by
    have hs := Finset.sum_filter_add_sum_filter_not (s := univ.filter good)
      (p := fun A ↦ p ∉ A) (f := fun A ↦ clusterOp h A β)
    simpa only [Finset.filter_filter, not_not] using hs.symm
  have hnoCross : (∑ A : Finset (Fin N) with good A ∧ p ∉ A, clusterOp h A β) =
      ∑ A ∈ (({p} : Finset (Fin N))ᶜ).powerset with good A, clusterOp h A β := by
    refine Finset.sum_congr ?_ fun _ _ ↦ rfl
    ext A
    simp only [mem_filter, mem_univ, true_and, mem_powerset, Finset.subset_compl_singleton]
    exact and_comm
  rw [truncatedExp_eq_sum_clusterOp]
  change (∑ A : Finset (Fin N) with good A, clusterOp h A β) = _
  rw [hsplit, hnoCross, sum_retained_clusterOp_containing_eq (pathGraph N)
    (fun C ↦ r ≤ C.card) h hcomm p β]
  simp only [not_le]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [pathGraph_compl_singleton_eq_sides]
    exact sum_retained_clusterOp_union_eq_mul (pathGraph N) (fun C ↦ r ≤ C.card) h hcomm
      (pathGraph_point_sides_separated p).1 (pathGraph_point_sides_separated p).2 β
  · refine Finset.sum_congr rfl fun C hCmem ↦ ?_
    have hc := (mem_filter.mp hCmem).2
    apply congrArg (clusterOp h C β * ·)
    rw [pathGraph_exterior_eq_sides hc.2.1]
    exact sum_retained_clusterOp_union_eq_mul (pathGraph N) (fun D ↦ r ≤ D.card) h hcomm
      (pathGraph_sides_separated ⟨p, hc.1⟩).1 (pathGraph_sides_separated ⟨p, hc.1⟩).2 β

end TNLean.Lattice.ClusterExpansion
