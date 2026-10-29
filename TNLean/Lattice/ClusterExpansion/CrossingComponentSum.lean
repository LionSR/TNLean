/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ClusterExpansion.SeparatedClusterSums
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# The retained expansion grouped by the component containing a given label

The component and its remaining allowed labels are constructed from actual graph clusters.
This is the finite structural step in ALVV, arXiv:1602.08828v2,
`eq:rho-expansion`, source lines 1971–2013.
-/

open Finset

namespace TNLean.Lattice.ClusterExpansion

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (G : SimpleGraph κ) [DecidableRel G.Adj]

private theorem no_adj_of_subset_exterior {C B : Finset κ}
    (hB : B ⊆ (C ∪ boundary G C)ᶜ) : ∀ c ∈ C, ∀ b ∈ B, ¬ G.Adj c b := by
  intro c hc b hb hcb
  have hbnot := Finset.mem_compl.mp (hB hb)
  have hbC : b ∉ C := fun h ↦ hbnot (mem_union_left _ h)
  exact hbnot (mem_union_right _ ((mem_boundary G).mpr ⟨hbC, c, hc, hcb.symm⟩))

private theorem sdiff_subset_exterior_of_isCluster {A C : Finset κ}
    (hC : IsCluster G A C) : A \ C ⊆ (C ∪ boundary G C)ᶜ := by
  intro x hx
  refine Finset.mem_compl.mpr fun h ↦ ?_
  exact (Finset.mem_union.mp h).elim (Finset.mem_sdiff.mp hx).2
    (fun hxB ↦ Finset.disjoint_left.mp hC.2.2 (Finset.mem_sdiff.mp hx).1 hxB)

open Classical in
/-- The retained supports containing a label are grouped by their unique component containing
that label. The remaining factor is the actual retained finite sum on the complement of the
component and its boundary. Supporting ALVV, arXiv:1602.08828v2, `eq:rho-expansion`,
source lines 1971–2013. -/
theorem sum_retained_clusterOp_containing_eq (large : Finset κ → Prop)
    (h : κ → Matrix ι ι ℂ)
    (hcomm : ∀ j k, ¬ G.Adj j k → Commute (h j) (h k)) (p : κ) (β : ℝ) :
    (∑ A : Finset κ with NoLargeCluster G large A ∧ p ∈ A, clusterOp h A β) =
      ∑ C ∈ (univ : Finset (Finset κ)).filter (fun C : Finset κ ↦
          p ∈ C ∧ (G.induce (C : Set κ)).Connected ∧ ¬ large C),
        clusterOp h C β *
          ∑ B ∈ ((C ∪ boundary G C)ᶜ).powerset with NoLargeCluster G large B,
            clusterOp h B β := by
  classical
  let comp := fun A : Finset κ ↦ if hp : p ∈ A then
    (exists_isCluster_mem G hp).choose else ∅
  have hcomp {A : Finset κ} (hp : p ∈ A) : IsCluster G A (comp A) ∧ p ∈ comp A := by
    simpa only [comp, dite_eq_left hp] using (exists_isCluster_mem G hp).choose_spec
  have hcover {A : Finset κ} (hp : p ∈ A) : comp A ∪ (A \ comp A) = A :=
    Finset.union_sdiff_of_subset (hcomp hp).1.1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij' (fun A ↦ Sigma.mk (comp A) (A \ comp A))
    (fun t ↦ t.1 ∪ t.2) ?_ ?_ ?_ ?_ ?_
  · intro A hA
    have hg := (mem_filter.mp hA).2
    have hc := hcomp hg.2
    have hext := sdiff_subset_exterior_of_isCluster G hc.1
    have hgoodB : NoLargeCluster G large (A \ comp A) :=
      ((noLargeCluster_union_iff_of_no_adj G large (no_adj_of_subset_exterior G hext)).mp
        (by rw [hcover hg.2]; exact hg.1)).2
    exact mem_sigma.mpr ⟨mem_filter.mpr ⟨mem_univ _, hc.2, hc.1.2.1, hg.1 _ hc.1⟩,
      mem_filter.mpr ⟨mem_powerset.mpr hext, hgoodB⟩⟩
  · rintro ⟨C, B⟩ hCB
    obtain ⟨hCmem, hBmem⟩ := mem_sigma.mp hCB
    have hc := (mem_filter.mp hCmem).2
    have hb := mem_filter.mp hBmem
    exact mem_filter.mpr ⟨mem_univ _,
      (noLargeCluster_union_iff_of_no_adj G large
        (no_adj_of_subset_exterior G (mem_powerset.mp hb.1))).mpr
          ⟨(noLargeCluster_iff_not_large_of_connected G large hc.2.1).mpr hc.2.2, hb.2⟩,
      mem_union_left _ hc.1⟩
  · exact fun A hA ↦ hcover (mem_filter.mp hA).2.2
  · rintro ⟨C, B⟩ hCB
    obtain ⟨hCmem, hBmem⟩ := mem_sigma.mp hCB
    have hc := (mem_filter.mp hCmem).2
    have hb := mem_powerset.mp (mem_filter.mp hBmem).1
    have hpc : p ∈ C ∪ B := mem_union_left _ hc.1
    have hcluster : IsCluster G (C ∪ B) C :=
      (isCluster_union_iff_of_no_adj G (no_adj_of_subset_exterior G hb)).mpr
        (.inl (isCluster_self_of_connected G hc.2.1))
    have heq : comp (C ∪ B) = C := eq_of_isCluster_of_inter_nonempty G (hcomp hpc).1
      hcluster ⟨p, mem_inter.mpr ⟨(hcomp hpc).2, hc.1⟩⟩
    have hd : Disjoint C B := Finset.disjoint_left.mpr fun x hxC hxB ↦
      Finset.mem_compl.mp (hb hxB) (mem_union_left _ hxC)
    simp only [heq, Finset.union_sdiff_cancel_left hd]
  · intro A hA
    have hp := (mem_filter.mp hA).2.2
    have hext := sdiff_subset_exterior_of_isCluster G (hcomp hp).1
    rw [← clusterOp_union h Finset.disjoint_sdiff
      (fun j hj k hk ↦ hcomm j k (no_adj_of_subset_exterior G hext j hj k hk)) β, hcover hp]

end TNLean.Lattice.ClusterExpansion
