/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.IntegerCellExteriorCollar

/-!
# Connectivity of occupied integer cells through their contacts

A preconnected finite union of closed integer-centered unit squares has a
connected contact graph. Contacts include shared corners: four-neighbor
connectivity of the occupied centers is not assumed.

This is an auxiliary geometric consequence for the block decomposition in
SCP10, arXiv:1001.3807, proof of Theorem 6.9, lines 1935–1990.
-/

open Set

namespace TNLean.PEPS

/-- The occupied-square contact graph, including diagonal contacts.
Source: SCP10, proof of Theorem 6.9, lines 1935–1990; auxiliary geometry. -/
def integerCellContactGraph (A : Finset (ℤ × ℤ)) :
    SimpleGraph {a : ℤ × ℤ // a ∈ A} where
  Adj a b := a ≠ b ∧ IsIntegerCellNear a.1 b.1
  symm := ⟨by
    rintro a b ⟨hne, hx, hy⟩
    exact ⟨hne.symm, by simpa only [abs_sub_comm] using hx,
      by simpa only [abs_sub_comm] using hy⟩⟩
  loopless := ⟨by intro a h; exact h.1 rfl⟩

/-- Intersecting occupied cells have centers at coordinate distance at most one.
Source: SCP10, proof of Theorem 6.9, lines 1935–1990; auxiliary geometry. -/
theorem isIntegerCellNear_of_integerClosedCell_inter_nonempty (a b : ℤ × ℤ)
    (h : (integerClosedCell a ∩ integerClosedCell b).Nonempty) : IsIntegerCellNear a b := by
  obtain ⟨x, ha, hb⟩ := h
  obtain ⟨ha₁, ha₂⟩ := (mem_integerClosedCell_iff a x).mp ha
  obtain ⟨hb₁, hb₂⟩ := (mem_integerClosedCell_iff b x).mp hb
  have h₁ : |(a.1 : ℝ) - (b.1 : ℝ)| ≤ 1 := by
    have hax := abs_le.mp ha₁
    have hbx := abs_le.mp hb₁
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have h₂ : |(a.2 : ℝ) - (b.2 : ℝ)| ≤ 1 := by
    have hay := abs_le.mp ha₂
    have hby := abs_le.mp hb₂
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  exact ⟨by exact_mod_cast h₁, by exact_mod_cast h₂⟩

private theorem isClosed_integerClosedCell (a : ℤ × ℤ) : IsClosed (integerClosedCell a) := by
  exact ((isCompact_Icc.prod isCompact_Icc).image
    (continuous_const.add continuous_id)).isClosed

/-- Preconnectedness of the actual occupied square union gives reachability
through all square contacts, including shared corners.
Source: SCP10, proof of Theorem 6.9, lines 1935–1990; auxiliary geometry. -/
theorem integerCellContactGraph_preconnected_of_isPreconnected (A : Finset (ℤ × ℤ))
    (hP : IsPreconnected (integerClosedCellUnion A)) :
    (integerCellContactGraph A).Preconnected := by
  classical
  intro u v
  by_contra huv
  let S : Set {a : ℤ × ℤ // a ∈ A} := {a | (integerCellContactGraph A).Reachable u a}
  let U : Set (ℝ × ℝ) := ⋃ a ∈ S, integerClosedCell a.1
  let V : Set (ℝ × ℝ) := ⋃ a ∈ Sᶜ, integerClosedCell a.1
  have hU : IsClosed U := S.toFinite.isClosed_biUnion fun a _ => isClosed_integerClosedCell a.1
  have hV : IsClosed V := Sᶜ.toFinite.isClosed_biUnion fun a _ => isClosed_integerClosedCell a.1
  have hcover : integerClosedCellUnion A ⊆ U ∪ V := by
    intro x hx
    change x ∈ ⋃ a ∈ A, integerClosedCell a at hx
    simp only [mem_iUnion, exists_prop] at hx
    obtain ⟨a, ha, hx⟩ := hx
    by_cases hr : (integerCellContactGraph A).Reachable u ⟨a, ha⟩
    · exact Or.inl (mem_iUnion₂_of_mem hr hx)
    · exact Or.inr (mem_iUnion₂_of_mem hr hx)
  have hcenter (a : ℤ × ℤ) : integerCellCenter a ∈ integerClosedCell a := by
    rw [mem_integerClosedCell_iff]
    simp [integerCellCenter]
  have hUne : (integerClosedCellUnion A ∩ U).Nonempty :=
    ⟨integerCellCenter u.1, (integerCellCenter_mem_closedCellUnion_iff A u.1).mpr u.2,
      mem_iUnion₂_of_mem (SimpleGraph.Reachable.refl u) (hcenter u.1)⟩
  have hVne : (integerClosedCellUnion A ∩ V).Nonempty :=
    ⟨integerCellCenter v.1, (integerCellCenter_mem_closedCellUnion_iff A v.1).mpr v.2,
      mem_iUnion₂_of_mem huv (hcenter v.1)⟩
  obtain ⟨x, _, hxU, hxV⟩ :=
    isPreconnected_closed_iff.mp hP U V hU hV hcover hUne hVne
  simp only [U, V, mem_iUnion, exists_prop, mem_compl_iff] at hxU hxV
  obtain ⟨a, ha, hxa⟩ := hxU
  obtain ⟨b, hb, hxb⟩ := hxV
  change (integerCellContactGraph A).Reachable u a at ha
  change ¬(integerCellContactGraph A).Reachable u b at hb
  have hab : a ≠ b := by
    intro he
    exact hb (he ▸ ha)
  have hadj : (integerCellContactGraph A).Adj a b :=
    ⟨hab, isIntegerCellNear_of_integerClosedCell_inter_nonempty a.1 b.1 ⟨x, hxa, hxb⟩⟩
  exact hb (ha.trans hadj.reachable)

/-- A genuinely simply connected occupied square union has a connected contact
graph. Diagonal contacts are retained. Source: SCP10, proof of Theorem 6.9,
lines 1935–1990; auxiliary geometry. -/
theorem integerCellContactGraph_connected_of_isSimplyConnected (A : Finset (ℤ × ℤ))
    (hSC : IsSimplyConnected (integerClosedCellUnion A)) :
    (integerCellContactGraph A).Connected := by
  obtain ⟨x, hx⟩ := hSC.nonempty
  simp only [integerClosedCellUnion, mem_iUnion, exists_prop] at hx
  obtain ⟨a, ha, _⟩ := hx
  let : Nonempty {a : ℤ × ℤ // a ∈ A} := ⟨⟨a, ha⟩⟩
  exact ⟨integerCellContactGraph_preconnected_of_isPreconnected A
    hSC.isPathConnected.isConnected.isPreconnected⟩

end TNLean.PEPS
