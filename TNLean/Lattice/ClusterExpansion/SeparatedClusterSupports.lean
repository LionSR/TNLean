/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ClusterExpansion.ClusterFactorization

/-!
# Clusters in separated label supports

Separated finite supports have no graph edges between them. Their actual connected components
and retained cluster selectors split without joining components. This is auxiliary to the
component factorization in ALVV, arXiv:1602.08828v2, `eq:rho-expansion`, source lines 1971–2013.
-/

open Finset

namespace TNLean.Lattice.ClusterExpansion

variable {κ : Type*} [Fintype κ] [DecidableEq κ]
    (G : SimpleGraph κ) [DecidableRel G.Adj]

private theorem disjoint_boundary_of_subset_union {A B C : Finset κ}
    (hC : C ⊆ A ∪ B) (hsep : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) :
    Disjoint C (boundary G A) := by
  refine Finset.disjoint_left.mpr fun x hxC hxB ↦ ?_
  obtain ⟨hxA, a, ha, hxa⟩ := (mem_boundary G).mp hxB
  exact hsep a ha x ((Finset.mem_union.mp (hC hxC)).resolve_left hxA) hxa.symm

/-- A cluster of a union of separated supports is exactly a cluster of one of the supports.
Supporting the component factorization in ALVV, arXiv:1602.08828v2, `eq:rho-expansion`,
source lines 1971–2013. -/
theorem isCluster_union_iff_of_no_adj {A B C : Finset κ}
    (hsep : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) :
    IsCluster G (A ∪ B) C ↔ IsCluster G A C ∨ IsCluster G B C := by
  constructor
  · intro hC
    obtain ⟨x⟩ := hC.2.1.nonempty
    rcases Finset.mem_union.mp (hC.1 x.property) with hxA | hxB
    · left
      exact ⟨subset_of_connected_of_disjoint_boundary G hC.2.1
        ⟨x, mem_inter.mpr ⟨x.property, hxA⟩⟩
        (disjoint_boundary_of_subset_union G hC.1 hsep), hC.2.1,
        hC.2.2.mono_left Finset.subset_union_left⟩
    · right
      exact ⟨subset_of_connected_of_disjoint_boundary G hC.2.1
        ⟨x, mem_inter.mpr ⟨x.property, hxB⟩⟩
        (disjoint_boundary_of_subset_union G (by simpa only [union_comm] using hC.1)
          (fun b hb a ha hba ↦ hsep a ha b hb hba.symm)), hC.2.1,
        hC.2.2.mono_left Finset.subset_union_right⟩
  · rintro (hC | hC)
    · refine ⟨hC.1.trans Finset.subset_union_left, hC.2.1,
        Finset.disjoint_union_left.mpr ⟨hC.2.2, ?_⟩⟩
      refine Finset.disjoint_left.mpr fun b hb hbC ↦ ?_
      obtain ⟨_, a, ha, hba⟩ := (mem_boundary G).mp hbC
      exact hsep a (hC.1 ha) b hb hba.symm
    · refine ⟨hC.1.trans Finset.subset_union_right, hC.2.1,
        Finset.disjoint_union_left.mpr ⟨?_, hC.2.2⟩⟩
      refine Finset.disjoint_left.mpr fun a ha haC ↦ ?_
      obtain ⟨_, b, hb, hab⟩ := (mem_boundary G).mp haC
      exact hsep a ha b (hC.1 hb) hab

/-- Retaining all clusters below any fixed largeness condition splits over separated supports.
Supporting ALVV, arXiv:1602.08828v2, `eq:rho-expansion`, source lines 1971–2013. -/
theorem noLargeCluster_union_iff_of_no_adj (large : Finset κ → Prop) {A B : Finset κ}
    (hsep : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) :
    NoLargeCluster G large (A ∪ B) ↔ NoLargeCluster G large A ∧ NoLargeCluster G large B := by
  exact ⟨fun h ↦ ⟨fun C hC ↦ h C ((isCluster_union_iff_of_no_adj G hsep).mpr (.inl hC)),
    fun C hC ↦ h C ((isCluster_union_iff_of_no_adj G hsep).mpr (.inr hC))⟩,
    fun h C hC ↦ ((isCluster_union_iff_of_no_adj G hsep).mp hC).elim (h.1 C) (h.2 C)⟩

/-- A connected label support is its own cluster. Supporting ALVV,
arXiv:1602.08828v2, `eq:rho-expansion`, source lines 1971–2013. -/
theorem isCluster_self_of_connected {C : Finset κ}
    (hC : (G.induce (C : Set κ)).Connected) : IsCluster G C C := by
  exact ⟨Finset.Subset.rfl, hC, Finset.disjoint_left.mpr
    (fun x hx hxB ↦ (mem_boundary G).mp hxB |>.1 hx)⟩

/-- For a connected support, retaining every cluster means retaining that support itself.
Supporting ALVV, arXiv:1602.08828v2, `eq:rho-expansion`, source lines 1971–2013. -/
theorem noLargeCluster_iff_not_large_of_connected (large : Finset κ → Prop) {C : Finset κ}
    (hC : (G.induce (C : Set κ)).Connected) : NoLargeCluster G large C ↔ ¬ large C := by
  constructor
  · exact fun h ↦ h C (isCluster_self_of_connected G hC)
  · intro hsmall D hD
    obtain ⟨x⟩ := hD.2.1.nonempty
    have heq : D = C := eq_of_isCluster_of_inter_nonempty G hD
      (isCluster_self_of_connected G hC) ⟨x, mem_inter.mpr ⟨x.property, hD.1 x.property⟩⟩
    exact heq.symm ▸ hsmall

end TNLean.Lattice.ClusterExpansion
