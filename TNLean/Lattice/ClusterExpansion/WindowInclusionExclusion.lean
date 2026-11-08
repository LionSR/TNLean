/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ClusterExpansion.MandatoryLabels
import Mathlib.Combinatorics.Enumerative.InclusionExclusion

/-!
# Inclusion and exclusion for mandatory windows

A finite family of required windows specifies a set of discarded label supports.
Mathlib's finite inclusion--exclusion identity, followed by the existing mandatory-support
identity, expresses the discarded operator as an alternating sum of the existing cluster parts.
The identity is valid for arbitrary complex matrices and every real parameter.

These are finite identities auxiliary to the cluster expansion in ALVV,
arXiv:1602.08828v2, `thm:cluster-approx`, source lines 1935–1968. The second theorem explicitly
assumes an avoidance characterization of the selected supports. The actual path characterization
is proved separately in `PathIntervals`; no spatial estimate is assumed here.
-/

open Finset

namespace TNLean.Lattice.ClusterExpansion

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] in
private theorem badSupport_indicator (W : Finset (Finset κ)) (A : Finset κ)
    (f : Finset κ → Matrix ι ι ℂ) :
    (if ∃ I ∈ W, I ⊆ A then f A else 0) =
      ∑ F ∈ W.powerset with F.Nonempty,
        (-1 : ℤ) ^ (F.card + 1) • (if F.biUnion id ⊆ A then f A else 0) := by
  classical
  have hi := Finset.indicator_biUnion_eq_sum_powerset W
    (fun I : Finset κ ↦ {A : Finset κ | I ⊆ A}) f A
  simpa only [Set.indicator, Set.mem_iUnion, Set.mem_ofPred_eq,
    Set.mem_iInter, Finset.biUnion_subset, id_eq, exists_prop] using hi

/-- Inclusion and exclusion over a finite family of mandatory windows, expressed using the
existing cluster part. This finite identity is auxiliary to the corrected interaction-label
truncation in ALVV, arXiv:1602.08828v2, `thm:cluster-approx`. -/
theorem sum_clusterOp_bad_windows_eq (h : κ → Matrix ι ι ℂ)
    (W : Finset (Finset κ)) (β : ℝ) :
    (∑ A : Finset κ with ∃ I ∈ W, I ⊆ A, clusterOp h A β) =
      ∑ F ∈ W.powerset with F.Nonempty,
        (-1 : ℤ) ^ (F.card + 1) •
          clusterPart (∑ i, h i) h ∅ (F.biUnion id) β := by
  classical
  rw [Finset.sum_filter]
  simp_rw [badSupport_indicator W _ (fun A ↦ clusterOp h A β)]
  rw [Finset.sum_comm]
  simp_rw [← Finset.smul_sum, ← Finset.sum_filter,
    ← clusterPart_empty_boundary_eq_sum_clusterOp]

/-- A window characterization of discarded supports gives an exact inclusion--exclusion
formula for the existing truncated exponential. This is a finite identity; no spatial estimate
or matrix product representation is assumed. Auxiliary to ALVV, arXiv:1602.08828v2,
`thm:cluster-approx`. -/
theorem exp_sub_truncatedExp_eq_sum_clusterPart_windows
    (G : SimpleGraph κ) [DecidableRel G.Adj] (large : Finset κ → Prop)
    (W : Finset (Finset κ))
    (hW : ∀ A, NoLargeCluster G large A ↔ ¬ ∃ I ∈ W, I ⊆ A)
    (h : κ → Matrix ι ι ℂ) (β : ℝ) :
    NormedSpace.exp (-(β • ∑ i, h i)) - truncatedExp G large h β =
      ∑ F ∈ W.powerset with F.Nonempty,
        (-1 : ℤ) ^ (F.card + 1) •
          clusterPart (∑ i, h i) h ∅ (F.biUnion id) β := by
  classical
  have hfull : NormedSpace.exp (-(β • ∑ i, h i)) = ∑ A : Finset κ, clusterOp h A β := by
    simpa [clusterPart] using clusterPart_empty_boundary_eq_sum_clusterOp h ∅ β
  rw [hfull, truncatedExp_eq_sum_clusterOp]
  rw [← sum_clusterOp_bad_windows_eq]
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := (univ : Finset (Finset κ)))
    (p := NoLargeCluster G large) (f := fun A ↦ clusterOp h A β)
  rw [← hsplit, add_sub_cancel_left]
  simp_rw [hW, not_not]

end TNLean.Lattice.ClusterExpansion
