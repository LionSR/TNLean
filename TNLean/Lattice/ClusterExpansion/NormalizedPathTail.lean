/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ClusterExpansion.WindowInclusionExclusion
import TNLean.Lattice.ClusterExpansion.PathWindowWeights
import QICLean.Algebra.UnionCoefficientBound

/-!
# The energy-normalized interaction-label cluster tail on a path

For `H = ∑ i, h i` with Hermitian terms of operator norm at most one and `H ≥ lambda I`, the
existing label-path truncation has energy-normalized error at most
`exp (N² (2 (exp β - 1))^r) - 1`, provided `r > 0`, `β ≥ 0`, and `2 (exp β - 1) ≤ 1`.
The proof groups exact inclusion--exclusion coefficients by their mandatory label union, applies
the normalized mandatory-label norm bound, and sums weights of actual interval components.
No commutation assumption on the terms is needed for this norm estimate.

**Local fix (cutoff and energy normalization):** this is a corrected auxiliary estimate related
to ALVV, arXiv:1602.08828v2, `thm:cluster-approx`, source lines 1270–1291 and 1935–1968.
The cutoff counts interaction labels, the norm is normalized by a supplied lower energy, and the
factor `2` accounts for the grouped inclusion--exclusion coefficients. The printed
physical-support approximation remains false; see
`docs/paper-gaps/alvv16_cluster_approximation.tex`. The spatial cut and matrix product operator
conclusions are separate and are not asserted here.
-/

open Finset SimpleGraph
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.Lattice.ClusterExpansion

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

private theorem sum_bad_clusterOp_grouped (h : κ → Matrix ι ι ℂ)
    (W : Finset (Finset κ)) (β : ℝ) :
    (∑ A : Finset κ with ∃ I ∈ W, I ⊆ A, clusterOp h A β) =
      ∑ U ∈ (W.powerset.filter Finset.Nonempty).image (fun F ↦ F.biUnion id),
        (∑ F ∈ W.powerset with F.Nonempty ∧ F.biUnion id = U,
          (-1 : ℤ) ^ (F.card + 1)) • clusterPart (∑ i, h i) h ∅ U β := by
  classical
  rw [sum_clusterOp_bad_windows_eq]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun F : Finset (Finset κ) ↦ F.biUnion id)
    (t := (W.powerset.filter Finset.Nonempty).image (fun F ↦ F.biUnion id))
    (fun F hF ↦ Finset.mem_image.mpr ⟨F, hF, rfl⟩)]
  refine Finset.sum_congr rfl fun U _ ↦ ?_
  rw [Finset.filter_filter, Finset.sum_smul]
  refine Finset.sum_congr rfl fun F hF ↦ ?_
  rw [(Finset.mem_filter.mp hF).2.2]

private theorem norm_sum_bad_clusterOp_le (h : κ → Matrix ι ι ℂ)
    (hh : ∀ i, (h i).IsHermitian) (hnorm : ∀ i, ‖h i‖ ≤ 1)
    (W : Finset (Finset κ)) (marker : W → κ)
    (hmarker : ∀ I : W, marker I ∈ (I : Finset κ)) (hinj : Function.Injective marker)
    (lambda β : ℝ) (hlo : (lambda : ℂ) • 1 ≤ ∑ i, h i) (hβ : 0 ≤ β) :
    Real.exp (β * lambda) * ‖∑ A : Finset κ with ∃ I ∈ W, I ⊆ A, clusterOp h A β‖ ≤
      ∑ U ∈ (W.powerset.filter Finset.Nonempty).image (fun F ↦ F.biUnion id),
        (2 * (Real.exp β - 1)) ^ U.card := by
  classical
  rw [sum_bad_clusterOp_grouped]
  let S := (W.powerset.filter Finset.Nonempty).image (fun F ↦ F.biUnion id)
  let c := fun U ↦ ∑ F ∈ W.powerset with F.Nonempty ∧ F.biUnion id = U,
    (-1 : ℤ) ^ (F.card + 1)
  have hH : (∑ i, h i).IsHermitian := Matrix.isHermitian_sum _ fun i _ ↦ hh i
  change Real.exp (β * lambda) * ‖∑ U ∈ S, c U • clusterPart (∑ i, h i) h ∅ U β‖ ≤ _
  calc
    _ ≤ Real.exp (β * lambda) * ∑ U ∈ S, ‖c U • clusterPart (∑ i, h i) h ∅ U β‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (Real.exp_pos _).le
    _ = ∑ U ∈ S, ‖c U‖ * (Real.exp (β * lambda) * ‖clusterPart (∑ i, h i) h ∅ U β‖) := by
      simp_rw [norm_zsmul ℝ, Int.norm_cast_real]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun U _ ↦ by ring
    _ ≤ ∑ U ∈ S, (2 : ℝ) ^ U.card * (Real.exp β - 1) ^ U.card := by
      apply Finset.sum_le_sum
      intro U _
      exact mul_le_mul (Finset.norm_sum_powerset_biUnion_sign_le_two_pow W marker hmarker hinj U)
        (norm_clusterPart_empty_boundary_le_of_lower_bound (∑ i, h i) h U hH
          (fun i _ ↦ hh i) (fun i _ ↦ hnorm i) lambda β hlo hβ)
        (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) (by positivity)
    _ = _ := by
      simp only [mul_pow]
      rfl

open Classical in
/-- The corrected energy-normalized interaction-label cluster tail on the actual path graph.
For Hermitian norm-one terms and a supplied lower energy `lambda`, the discarded operator has
normalized norm at most `exp (N² (2 (exp β - 1))^r) - 1`. The cutoff counts interaction labels.
This auxiliary correction to ALVV, arXiv:1602.08828v2, `thm:cluster-approx`, source lines
1270–1291 and 1935–1968, does not assert the false printed physical-support estimate or a matrix
product operator representation; see `docs/paper-gaps/alvv16_cluster_approximation.tex`. -/
theorem norm_exp_sub_truncatedExp_pathGraph_le {N r : ℕ} (hr : 0 < r)
    (h : Fin N → Matrix ι ι ℂ) (hh : ∀ i, (h i).IsHermitian) (hnorm : ∀ i, ‖h i‖ ≤ 1)
    (lambda β : ℝ) (hlo : (lambda : ℂ) • 1 ≤ ∑ i, h i) (hβ : 0 ≤ β)
    (hsmall : 2 * (Real.exp β - 1) ≤ 1) :
    Real.exp (β * lambda) *
      ‖NormedSpace.exp (-(β • ∑ i, h i)) -
        truncatedExp (pathGraph N) (fun C ↦ r ≤ C.card) h β‖ ≤
      Real.exp ((N : ℝ) ^ 2 * (2 * (Real.exp β - 1)) ^ r) - 1 := by
  classical
  rw [exp_sub_truncatedExp_eq_sum_clusterPart_windows (pathGraph N)
    (fun C ↦ r ≤ C.card) (pathWindows N r) (fun A ↦ noLargeCluster_pathGraph_iff hr A) h β,
    ← sum_clusterOp_bad_windows_eq]
  obtain ⟨marker, hmarker, hinj⟩ := pathWindows_exists_marker (N := N) hr
  exact (norm_sum_bad_clusterOp_le h hh hnorm (pathWindows N r) marker hmarker hinj
    lambda β hlo hβ).trans (sum_pow_card_unions_pathWindows_le hr
      (mul_nonneg (by norm_num) (sub_nonneg.mpr (Real.one_le_exp hβ))) hsmall)

end TNLean.Lattice.ClusterExpansion
