/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ClusterExpansion.SeparatedClusterSupports

/-!
# Retained cluster sums over separated label supports

The factors in the separated expansion are actual finite sums of the existing exact-label
coefficients. Supporting ALVV, arXiv:1602.08828v2, `eq:rho-expansion`, source lines 1971–2013.
-/

open Finset

namespace TNLean.Lattice.ClusterExpansion

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (G : SimpleGraph κ) [DecidableRel G.Adj]

open Classical in
/-- Exact factorization of the retained finite sum on two separated allowed label sets.
The factors are constructed by summing the existing coefficients over their respective supports.
Supporting ALVV, arXiv:1602.08828v2, `eq:rho-expansion`, source lines 1971–2013. -/
theorem sum_retained_clusterOp_union_eq_mul (large : Finset κ → Prop)
    (h : κ → Matrix ι ι ℂ)
    (hcomm : ∀ j k, ¬ G.Adj j k → Commute (h j) (h k))
    {B C : Finset κ} (hBC : Disjoint B C)
    (hsep : ∀ b ∈ B, ∀ c ∈ C, ¬ G.Adj b c) (β : ℝ) :
    (∑ A ∈ (B ∪ C).powerset with NoLargeCluster G large A, clusterOp h A β) =
      (∑ A ∈ B.powerset with NoLargeCluster G large A, clusterOp h A β) *
        ∑ A ∈ C.powerset with NoLargeCluster G large A, clusterOp h A β := by
  classical
  have hsplit (A : Finset κ) (hA : A ⊆ B ∪ C) : (A ∩ B) ∪ (A ∩ C) = A := by
    rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hA]
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_nbij' (fun A ↦ (A ∩ B, A ∩ C)) (fun p ↦ p.1 ∪ p.2)
    ?_ ?_ ?_ ?_ ?_
  · intro A hA
    obtain ⟨hAsub, hgood⟩ := mem_filter.mp hA
    have hg := (noLargeCluster_union_iff_of_no_adj G large
      (A := A ∩ B) (B := A ∩ C)
      (fun b hb c hc ↦ hsep b (mem_inter.mp hb).2 c (mem_inter.mp hc).2)).mp
        (by rwa [hsplit A (mem_powerset.mp hAsub)])
    exact mem_product.mpr ⟨mem_filter.mpr ⟨mem_powerset.mpr inter_subset_right, hg.1⟩,
      mem_filter.mpr ⟨mem_powerset.mpr inter_subset_right, hg.2⟩⟩
  · rintro ⟨A, D⟩ hAD
    simp only [mem_product, mem_filter, mem_powerset] at hAD ⊢
    exact ⟨union_subset_union hAD.1.1 hAD.2.1,
      (noLargeCluster_union_iff_of_no_adj G large
        (fun a ha d hd ↦ hsep a (hAD.1.1 ha) d (hAD.2.1 hd))).mpr ⟨hAD.1.2, hAD.2.2⟩⟩
  · exact fun A hA ↦ hsplit A (mem_powerset.mp (mem_filter.mp hA).1)
  · rintro ⟨A, D⟩ hAD
    simp only [mem_product, mem_filter, mem_powerset] at hAD
    have hDB : D ∩ B = ∅ := disjoint_iff_inter_eq_empty.mp (hBC.symm.mono_left hAD.2.1)
    have hAC : A ∩ C = ∅ := disjoint_iff_inter_eq_empty.mp (hBC.mono_left hAD.1.1)
    simp only [union_inter_distrib_right, hDB, hAC, inter_eq_left.mpr hAD.1.1,
      inter_eq_left.mpr hAD.2.1, union_empty, empty_union]
  · intro A hA
    rw [← clusterOp_union h ((hBC.mono_left inter_subset_right).mono_right inter_subset_right)
      (fun j hj k hk ↦ hcomm j k (hsep j (mem_inter.mp hj).2 k (mem_inter.mp hk).2)) β,
      hsplit A (mem_powerset.mp (mem_filter.mp hA).1)]

end TNLean.Lattice.ClusterExpansion
