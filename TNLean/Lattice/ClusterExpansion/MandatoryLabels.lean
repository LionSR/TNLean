/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ClusterExpansion.ClusterFactorization
import QICLean.Analysis.MandatoryExponentialNorm

/-!
# Mandatory labels in the existing cluster expansion

The empty-boundary cluster part inherits the energy-normalized operator norm
bound. When the background is the full sum of the interactions, it is the sum
of the existing exact-support coefficients over supports containing the
required labels. The word-series identities are those
of Hastings, arXiv:cond-mat/0508554v3, source lines 1174–1177 and 1268–1269.

**Local fix (energy normalization and interaction labels):** these are
auxiliary results for a corrected interaction-label expansion related
to ALVV, arXiv:1602.08828v2, `thm:cluster-approx`, lines 1270–1291 and 1935–1968.
The false printed spatial approximation estimate remains distinct; see
`docs/paper-gaps/alvv16_cluster_approximation.tex`. No spatial cut or matrix
product operator construction is concluded here.
-/

open Finset
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.Lattice.ClusterExpansion

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq κ] in
/-- The existing empty-boundary cluster part satisfies the corrected
energy-normalized mandatory-label estimate. Auxiliary to ALVV,
arXiv:1602.08828v2, `thm:cluster-approx`, lines 1270–1291 and 1935–1968;
Hastings, arXiv:cond-mat/0508554v3, source lines 1174–1177. -/
theorem norm_clusterPart_empty_boundary_le_of_lower_bound
    (H : Matrix ι ι ℂ) (h : κ → Matrix ι ι ℂ) (U : Finset κ)
    (hH : H.IsHermitian) (hh : ∀ i ∈ U, (h i).IsHermitian)
    (hnorm : ∀ i ∈ U, ‖h i‖ ≤ 1) (lambda β : ℝ)
    (hlo : (lambda : ℂ) • 1 ≤ H) (hβ : 0 ≤ β) :
    Real.exp (β * lambda) * ‖clusterPart H h ∅ U β‖ ≤ (Real.exp β - 1) ^ U.card := by
  simpa only [clusterPart, Finset.sum_empty, sub_zero] using
    Matrix.norm_sum_powerset_exp_sub_le_of_lower_bound H h U hH hh hnorm lambda β hlo hβ

/-- Summing the existing exact-support coefficients over supports containing
all required labels gives the existing empty-boundary cluster part.
Hastings, arXiv:cond-mat/0508554v3, source lines 1174–1177 and 1268–1269. -/
theorem clusterPart_empty_boundary_eq_sum_clusterOp [Fintype κ]
    (h : κ → Matrix ι ι ℂ) (U : Finset κ) (β : ℝ) :
    clusterPart (∑ i, h i) h ∅ U β = ∑ A : Finset κ with U ⊆ A, clusterOp h A β := by
  classical
  have hp := hasSum_words_clusterPart (H := ∑ i, h i) (h := h) (B := ∅) (C := U)
    rfl (by simp) β
  simp only [Finset.disjoint_empty_right, and_true] at hp
  apply hp.unique
  convert (hasSum_sum (s := {A : Finset κ | U ⊆ A}) fun A _ ↦
    hasSum_words_clusterOp h A β) using 1
  funext n
  rw [← Finset.smul_sum]
  congr 1
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun w : Fin n → κ ↦ univ.image w)
    (t := {A : Finset κ | U ⊆ A}) (fun w hw ↦ by simpa using hw)]
  refine Finset.sum_congr rfl fun A hA ↦ ?_
  rw [Finset.filter_filter]
  exact Finset.sum_congr (Finset.filter_congr fun w _ ↦
    ⟨fun hw ↦ hw.2, fun hw ↦ ⟨hw.symm ▸ (Finset.mem_filter.mp hA).2, hw⟩⟩)
    (fun _ _ ↦ rfl)


end TNLean.Lattice.ClusterExpansion
