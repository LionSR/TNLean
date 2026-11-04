/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ClusterExpansion.PathIntervals
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Weights of unions of interaction-label windows

A union of nonempty families of length-`r` windows is determined by its actual graph components.
Every component is an interval of at least `r` labels. The component map injects these unions into
nonempty families of such intervals, and the total interval weight is bounded using the finite
product expansion and the endpoint count.

This is auxiliary to a corrected interaction-label estimate related to ALVV,
arXiv:1602.08828v2, `thm:cluster-approx`, source lines 1935–1968. No operator factorization or
matrix product representation is needed for this scalar count.
-/

open Finset SimpleGraph

namespace TNLean.Lattice.ClusterExpansion

variable {N r : ℕ}

open Classical in
private theorem prod_pow_card_clusters (U : Finset (Fin N)) (b : ℝ) :
    (∏ C ∈ clusters (pathGraph N) U, b ^ C.card) = b ^ U.card := by
  classical
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [← Finset.card_biUnion ((pairwise_clusters (pathGraph N) U).mono'
    (fun _ _ h ↦ h.1))]
  exact congrArg Finset.card (biUnion_clusters (pathGraph N) U)

open Classical in
/-- The total weight of unions of nonempty families of length-`r` windows has an exponential
bound. This counts actual components of the label path. Auxiliary to the corrected
interaction-label tail in ALVV, arXiv:1602.08828v2, `thm:cluster-approx`. -/
theorem sum_pow_card_unions_pathWindows_le {r : ℕ} (hr : 0 < r)
    {b : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    (∑ U ∈ ((pathWindows N r).powerset.filter Finset.Nonempty).image
        (fun F ↦ F.biUnion id), b ^ U.card) ≤
      Real.exp ((N : ℝ) ^ 2 * b ^ r) - 1 := by
  classical
  let S := ((pathWindows N r).powerset.filter Finset.Nonempty).image (fun F ↦ F.biUnion id)
  have hcomponents : ∀ U ∈ S, (clusters (pathGraph N) U).Nonempty ∧
      clusters (pathGraph N) U ⊆ pathIntervals N r := by
    intro U hU
    obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hU
    have hFsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hF).1
    obtain ⟨I, hIF⟩ := (Finset.mem_filter.mp hF).2
    have hI := mem_pathWindows.mp (hFsub hIF)
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (hI.2.symm ▸ hr)
    obtain ⟨C, hC, _⟩ := exists_isCluster_mem (pathGraph N)
      (show x ∈ F.biUnion id from Finset.mem_biUnion.mpr ⟨I, hIF, hx⟩)
    exact ⟨⟨C, (mem_clusters (pathGraph N)).mpr hC⟩,
      clusters_biUnion_pathWindows_subset hFsub⟩
  have hinj : Function.Injective (clusters (pathGraph N)) := by
    intro U V heq
    exact (biUnion_clusters (pathGraph N) U).symm.trans
      ((congrArg (fun F ↦ F.biUnion id) heq).trans (biUnion_clusters (pathGraph N) V))
  have hsum : (∑ U ∈ S, b ^ U.card) ≤
      ∑ F ∈ (pathIntervals N r).powerset with F.Nonempty, ∏ C ∈ F, b ^ C.card := by
    apply Finset.sum_le_sum_of_injOn (clusters (pathGraph N)) hinj.injOn
    · intro F hF
      obtain ⟨U, hU, rfl⟩ := mem_image.mp hF
      exact mem_filter.mpr ⟨mem_powerset.mpr (hcomponents U hU).2, (hcomponents U hU).1⟩
    · intro U _
      exact (prod_pow_card_clusters U b).symm.le
    · intro F _ _
      exact Finset.prod_nonneg fun C _ ↦ pow_nonneg hb C.card
  have hprod : (∑ F ∈ (pathIntervals N r).powerset with F.Nonempty,
      ∏ C ∈ F, b ^ C.card) + 1 = ∏ C ∈ pathIntervals N r, (1 + b ^ C.card) := by
    rw [Finset.prod_one_add]
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (s := (pathIntervals N r).powerset) (p := Finset.Nonempty)
      (f := fun F ↦ ∏ C ∈ F, b ^ C.card)
    simpa [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq'] using hsplit
  have hweights : (∑ C ∈ pathIntervals N r, b ^ C.card) ≤ (N : ℝ) ^ 2 * b ^ r := by
    calc
      (∑ C ∈ pathIntervals N r, b ^ C.card) ≤ ∑ _C ∈ pathIntervals N r, b ^ r :=
        Finset.sum_le_sum fun C hC ↦ pow_le_pow_of_le_one hb hb1
          (mem_pathIntervals.mp hC).2.2
      _ = (pathIntervals N r).card * b ^ r := by simp
      _ ≤ (N : ℝ) ^ 2 * b ^ r := mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_pathIntervals_le N r) (pow_nonneg hb r)
  have hprodle : (∏ C ∈ pathIntervals N r, (1 + b ^ C.card)) ≤
      Real.exp (∑ C ∈ pathIntervals N r, b ^ C.card) := by
    rw [Real.exp_sum]
    exact Finset.prod_le_prod₀ (fun C _ ↦ add_nonneg zero_le_one (pow_nonneg hb C.card))
      (fun C _ ↦ by simpa only [add_comm] using Real.add_one_le_exp (b ^ C.card))
  change (∑ U ∈ S, b ^ U.card) ≤ _
  linarith [hprodle.trans (Real.exp_le_exp.mpr hweights)]

end TNLean.Lattice.ClusterExpansion
