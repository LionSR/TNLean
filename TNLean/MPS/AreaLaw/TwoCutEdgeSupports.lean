/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Basic

/-!
# Nearest-neighbour edges at two cuts of a finite chain

The cuts are immediately after sites u and v, with u < v. The three regions are
[0,u+1), [u+1,v+1), and the complement of their union. A valid edge r acts on
[r,r+2), and the condition r+1 < L makes both sites actual chain sites.

This is the elementary support classification needed for ALVV,
arXiv:1602.08828v2, `eq:H-mid-cut` and `item:small-sr` (local source lines 806–831),
and the algebraic step in `prop:Cheby-AGSP-eff` (lines 1324–1332). The convention
here agrees with the explicitly named cuts (i1,i1+1) and (i2,i2+1).
Adjacent cuts are allowed; their crossing supports share the middle site.
-/

namespace TNLean.MPS.AreaLaw

/-- Nearest-neighbour supports at cuts immediately following u and v.
The edge indexed by r has interval support [r,r+2).
ALVV, arXiv:1602.08828v2, `eq:H-mid-cut` and `item:small-sr`, lines 806–831. -/
theorem interval_edge_classification_of_lt
    {L u v : ℕ} (huv : u < v) (hv : v + 1 < L) :
    interval L u (u + 2) ⊆
        interval L 0 (u + 1) ∪ interval L (u + 1) (v + 1) ∧
      interval L u (u + 2) ∩ interval L 0 (u + 1) =
        {⟨u, by omega⟩} ∧
      Disjoint (interval L v (v + 2)) (interval L 0 (u + 1)) ∧
      interval L v (v + 2) ∩ interval L (u + 1) (v + 1) =
        {⟨v, by omega⟩} ∧
      ∀ r : ℕ, r + 1 < L → r ≠ u → r ≠ v →
        interval L r (r + 2) ⊆ interval L 0 (u + 1) ∨
        interval L r (r + 2) ⊆ interval L (u + 1) (v + 1) ∨
        interval L r (r + 2) ⊆
          (interval L 0 (u + 1) ∪ interval L (u + 1) (v + 1))ᶜ := by
  classical
  have hUnion (x : Fin L) :
      x ∈ interval L 0 (u + 1) ∪ interval L (u + 1) (v + 1) ↔
        x.val < v + 1 := by
    simp only [Finset.mem_union, mem_interval]
    omega
  have hOutside (x : Fin L) :
      x ∈ (interval L 0 (u + 1) ∪ interval L (u + 1) (v + 1))ᶜ ↔
        v + 1 ≤ x.val := by
    rw [Finset.mem_compl, hUnion]
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    apply (hUnion x).mpr
    have hx' := mem_interval.mp hx
    omega
  · ext x
    simp only [Finset.mem_inter, mem_interval, Finset.mem_singleton, Fin.ext_iff]
    omega
  · rw [Finset.disjoint_left]
    intro x hx hx'
    have hxr := mem_interval.mp hx
    have hxl := mem_interval.mp hx'
    omega
  · ext x
    simp only [Finset.mem_inter, mem_interval, Finset.mem_singleton, Fin.ext_iff]
    omega
  · intro r _hr hru hrv
    by_cases hleft : r < u
    · left
      exact interval_mono (Nat.zero_le r) (by omega)
    · by_cases hmiddle : r < v
      · right
        left
        exact interval_mono (by omega) (by omega)
      · right
        right
        intro x hx
        apply (hOutside x).mpr
        have hx' := mem_interval.mp hx
        omega

end TNLean.MPS.AreaLaw
