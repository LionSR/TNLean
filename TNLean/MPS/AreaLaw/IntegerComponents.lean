/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.Int.SuccPred
import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Components of an induced integer graph

In the graph induced on a set of integers from the ambient integer Hasse graph,
two vertices are reachable exactly when every integer between them is in the set.
No finiteness or nonemptiness assumption on the set is required.

## Main results

* `SimpleGraph.hasse_int_induce_reachable_iff` characterizes reachability by interval
  containment.
* `SimpleGraph.ConnectedComponent.ordConnected_image_hasse_int_induce` shows that
  the coordinates of each component are order-connected.

This is the geometric ingredient of the one-dimensional component reduction in
`docs/notes/one_dimensional_note/part1_arealaw.tex`, lines 71–80; the induced
nearest-neighbor graph is specified in `part0_preamble.tex:191–199`.
Hamiltonian decomposition and the disconnected-domain area law are separate results.
-/

namespace SimpleGraph

/-- An edge of the induced integer graph cannot cross a missing integer.
TNLean one-dimensional note, standing graph at `part0_preamble.tex:191–199`
and component reduction at `part1_arealaw.tex:71–80`. -/
private theorem lt_iff_lt_of_hasse_int_induce_adj {S : Set ℤ} {x y : S} {z : ℤ}
    (hz : z ∉ S) (hxy : ((hasse ℤ).induce S).Adj x y) :
    (x : ℤ) < z ↔ (y : ℤ) < z := by
  have hxne : (x : ℤ) ≠ z := fun h ↦ hz (h ▸ x.property)
  have hyne : (y : ℤ) ≠ z := fun h ↦ hz (h ▸ y.property)
  have hstep : (x : ℤ) + 1 = (y : ℤ) ∨ (y : ℤ) + 1 = (x : ℤ) := by
    simpa only [induce_adj, hasse_adj, Order.covBy_iff_add_one_eq] using hxy
  omega

private theorem lt_iff_lt_of_hasse_int_induce_reachable {S : Set ℤ} {x y : S}
    {z : ℤ} (hz : z ∉ S) (hxy : ((hasse ℤ).induce S).Reachable x y) :
    (x : ℤ) < z ↔ (y : ℤ) < z := by
  obtain ⟨w⟩ := hxy
  induction w with
  | nil => exact Iff.rfl
  | cons h _ ih => exact (lt_iff_lt_of_hasse_int_induce_adj hz h).trans ih

private theorem mem_of_hasse_int_induce_reachable {S : Set ℤ} {x y : S}
    (hxy : ((hasse ℤ).induce S).Reachable x y) {z : ℤ}
    (hzmin : min (x : ℤ) (y : ℤ) ≤ z) (hzmax : z ≤ max (x : ℤ) (y : ℤ)) :
    z ∈ S := by
  by_contra hz
  have hcut := lt_iff_lt_of_hasse_int_induce_reachable hz hxy
  have hxne : (x : ℤ) ≠ z := fun h ↦ hz (h ▸ x.property)
  have hyne : (y : ℤ) ≠ z := fun h ↦ hz (h ▸ y.property)
  rcases le_total (x : ℤ) (y : ℤ) with h | h
  · rw [min_eq_left h] at hzmin
    rw [max_eq_right h] at hzmax
    omega
  · rw [min_eq_right h] at hzmin
    rw [max_eq_left h] at hzmax
    omega

private theorem hasse_int_induce_reachable_of_le {S : Set ℤ} (x y : S)
    (hxy : (x : ℤ) ≤ (y : ℤ))
    (hS : ∀ z : ℤ, (x : ℤ) ≤ z → z ≤ (y : ℤ) → z ∈ S) :
    ((hasse ℤ).induce S).Reachable x y := by
  have hreach : ∀ (n : ℤ), (x : ℤ) ≤ n → n ≤ (y : ℤ) →
      ∀ hn : n ∈ S, ((hasse ℤ).induce S).Reachable x ⟨n, hn⟩ := by
    apply Int.leInduction
    · intro _ hn
      exact Reachable.refl x
    · intro n hxn ih hny hn
      have hny' : n ≤ (y : ℤ) := by omega
      have hn' : n ∈ S := hS n hxn hny'
      have hadj : ((hasse ℤ).induce S).Adj ⟨n, hn'⟩ ⟨n + 1, hn⟩ := by
        exact Or.inl (Order.covBy_iff_add_one_eq.mpr rfl)
      exact (ih hny' hn').trans hadj.reachable
  exact hreach (y : ℤ) hxy le_rfl y.property

/-- In the induced ambient integer Hasse graph, two vertices are reachable if and only if
all integers between them belong to the domain. No finiteness assumption on the domain
is required. This is the interval geometry used in the component reduction in the TNLean
one-dimensional note, `part1_arealaw.tex:71–80`, for the standing graph specified in
`part0_preamble.tex:191–199`. -/
theorem hasse_int_induce_reachable_iff (S : Set ℤ) (x y : S) :
    ((hasse ℤ).induce S).Reachable x y ↔
      ∀ z : ℤ, min (x : ℤ) (y : ℤ) ≤ z →
        z ≤ max (x : ℤ) (y : ℤ) → z ∈ S := by
  constructor
  · intro hxy z hzmin hzmax
    exact mem_of_hasse_int_induce_reachable hxy hzmin hzmax
  · intro hS
    rcases le_total (x : ℤ) (y : ℤ) with hxy | hyx
    · exact hasse_int_induce_reachable_of_le x y hxy fun z hxz hzy ↦
        hS z (by simpa only [min_eq_left hxy] using hxz)
          (by simpa only [max_eq_right hxy] using hzy)
    · exact (hasse_int_induce_reachable_of_le y x hyx fun z hyz hzx ↦
        hS z (by simpa only [min_eq_right hyx] using hyz)
          (by simpa only [max_eq_left hyx] using hzx)).symm

/-- The coordinates of each connected component of an induced integer graph form an
order-connected set. This interval property is used in the component reduction in the
TNLean one-dimensional note, `part1_arealaw.tex:71–80`. -/
theorem ConnectedComponent.ordConnected_image_hasse_int_induce (S : Set ℤ)
    (C : ((hasse ℤ).induce S).ConnectedComponent) :
    Set.OrdConnected (Subtype.val '' C.supp) := by
  refine ⟨?_⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ z ⟨hxz, hzy⟩
  have hxy := C.reachable_of_mem_supp hx hy
  have hinterval := (hasse_int_induce_reachable_iff S x y).mp hxy
  have hz : z ∈ S := hinterval z ((min_le_left _ _).trans hxz)
    (hzy.trans (le_max_right _ _))
  have hxz' : ((hasse ℤ).induce S).Reachable x ⟨z, hz⟩ :=
    hasse_int_induce_reachable_of_le x ⟨z, hz⟩ hxz fun w hxw hwz ↦
      hinterval w ((min_le_left _ _).trans hxw)
        ((hwz.trans hzy).trans (le_max_right _ _))
  refine ⟨⟨z, hz⟩, ?_, rfl⟩
  rw [ConnectedComponent.mem_supp_iff] at hx ⊢
  exact (ConnectedComponent.sound hxz').symm.trans hx

end SimpleGraph
