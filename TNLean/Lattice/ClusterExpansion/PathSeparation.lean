/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ClusterExpansion.PathIntervals

/-!
# Separation around an actual interval in the label path

The complement of an interval and its graph boundary is the union of the allowed label sets to
its left and right. Supporting ALVV, arXiv:1602.08828v2, `eq:rho-expansion`, lines 1971–2013.
-/

open Finset SimpleGraph

namespace TNLean.Lattice.ClusterExpansion

variable {N : ℕ}

open Classical in
/-- The actual exterior of a connected interval is its two separated sides, excluding the
boundary labels. Supporting ALVV, arXiv:1602.08828v2, `eq:rho-expansion`, lines 1971–2013. -/
theorem pathGraph_exterior_eq_sides {C : Finset (Fin N)}
    (hC : ((pathGraph N).induce (C : Set (Fin N))).Connected) :
    (C ∪ boundary (pathGraph N) C)ᶜ =
      {j ∈ (univ : Finset (Fin N)) | ∀ c ∈ C, j.val + 1 < c.val} ∪
        {j ∈ (univ : Finset (Fin N)) | ∀ c ∈ C, c.val + 1 < j.val} := by
  classical
  have hord := ordConnected_of_pathGraph_connected hC
  obtain ⟨p⟩ := hC.nonempty
  ext j
  constructor
  · intro hj
    have hjnot : j ∉ C ∧ j ∉ boundary (pathGraph N) C := by
      simpa only [mem_compl, mem_union, not_or] using hj
    have hnadj : ∀ c ∈ C, ¬ (pathGraph N).Adj j c := fun c hc hjc ↦
      hjnot.2 ((mem_boundary (pathGraph N)).mpr ⟨hjnot.1, c, hc, hjc⟩)
    have hne : j ≠ (p : Fin N) := fun heq ↦ hjnot.1 (heq.symm ▸ p.property)
    rcases lt_or_gt_of_ne hne with hjp | hpj
    · apply mem_union_left
      refine mem_filter.mpr ⟨mem_univ _, fun c hc ↦ ?_⟩
      have hlt : j.val < c.val := by
        by_contra hlt
        exact hjnot.1 (hord.out' hc p.property ⟨show c ≤ j by omega, hjp.le⟩)
      have hneq : j.val + 1 ≠ c.val := fun heq ↦ hnadj c hc (pathGraph_adj.mpr (.inl heq))
      omega
    · apply mem_union_right
      refine mem_filter.mpr ⟨mem_univ _, fun c hc ↦ ?_⟩
      have hlt : c.val < j.val := by
        by_contra hlt
        exact hjnot.1 (hord.out' p.property hc ⟨hpj.le, show j ≤ c by omega⟩)
      have hneq : c.val + 1 ≠ j.val := fun heq ↦ hnadj c hc (pathGraph_adj.mpr (.inr heq))
      omega
  · intro hj
    have hside : (∀ c ∈ C, j.val + 1 < c.val) ∨ (∀ c ∈ C, c.val + 1 < j.val) := by
      simpa only [mem_union, mem_filter, mem_univ, true_and] using hj
    have hjC : j ∉ C := by
      intro hjC
      rcases hside with hs | hs <;> have := hs j hjC <;> omega
    refine mem_compl.mpr fun hjbad ↦ (mem_union.mp hjbad).elim hjC ?_
    intro hjB
    obtain ⟨_, c, hc, hjc⟩ := (mem_boundary (pathGraph N)).mp hjB
    have hadj := pathGraph_adj.mp hjc
    rcases hside with hs | hs <;> have := hs c hc <;> omega

/-- The two exterior sides of a nonempty support are disjoint and have no path edge between
them. Supporting ALVV, arXiv:1602.08828v2, `eq:rho-expansion`, lines 1971–2013. -/
theorem pathGraph_sides_separated {C : Finset (Fin N)} (hne : C.Nonempty) :
    Disjoint {j ∈ (univ : Finset (Fin N)) | ∀ c ∈ C, j.val + 1 < c.val}
      {j ∈ (univ : Finset (Fin N)) | ∀ c ∈ C, c.val + 1 < j.val} ∧
      ∀ a ∈ {j ∈ (univ : Finset (Fin N)) | ∀ c ∈ C, j.val + 1 < c.val},
        ∀ b ∈ {j ∈ (univ : Finset (Fin N)) | ∀ c ∈ C, c.val + 1 < j.val},
          ¬ (pathGraph N).Adj a b := by
  obtain ⟨p, hp⟩ := hne
  constructor
  · refine Finset.disjoint_left.mpr fun j hjL hjR ↦ ?_
    have hL := (mem_filter.mp hjL).2 p hp
    have hR := (mem_filter.mp hjR).2 p hp
    omega
  · intro a ha b hb hab
    have hL := (mem_filter.mp ha).2 p hp
    have hR := (mem_filter.mp hb).2 p hp
    have hadj := pathGraph_adj.mp hab
    omega

/-- Removing a single label leaves its two strict order sides. Supporting the no-crossing
case in ALVV, arXiv:1602.08828v2, `eq:rho-expansion`, lines 1971–2013. -/
theorem pathGraph_compl_singleton_eq_sides (p : Fin N) :
    ({p} : Finset (Fin N))ᶜ = {j ∈ (univ : Finset (Fin N)) | j.val < p.val} ∪
      {j ∈ (univ : Finset (Fin N)) | p.val < j.val} := by
  ext j
  simp only [mem_compl, mem_singleton, mem_union, mem_filter, mem_univ, true_and,
    Fin.ext_iff]
  omega

/-- The two strict sides of a deleted label are separated in the actual path graph.
Supporting ALVV, arXiv:1602.08828v2, `eq:rho-expansion`, lines 1971–2013. -/
theorem pathGraph_point_sides_separated (p : Fin N) :
    Disjoint {j ∈ (univ : Finset (Fin N)) | j.val < p.val}
      {j ∈ (univ : Finset (Fin N)) | p.val < j.val} ∧
      ∀ a ∈ {j ∈ (univ : Finset (Fin N)) | j.val < p.val},
        ∀ b ∈ {j ∈ (univ : Finset (Fin N)) | p.val < j.val}, ¬ (pathGraph N).Adj a b := by
  constructor
  · refine Finset.disjoint_left.mpr fun j hjL hjR ↦ ?_
    have hL := (mem_filter.mp hjL).2
    have hR := (mem_filter.mp hjR).2
    omega
  · intro a ha b hb hab
    have hL := (mem_filter.mp ha).2
    have hR := (mem_filter.mp hb).2
    have hadj := pathGraph_adj.mp hab
    omega

end TNLean.Lattice.ClusterExpansion
