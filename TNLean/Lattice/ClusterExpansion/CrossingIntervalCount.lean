/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ClusterExpansion.PathIntervals

/-!
# Counting the actual crossing intervals of the label path

The left and right distances from the crossing label determine an interval. This gives the
finite count used for the bond estimate in the interaction-label version of ALVV,
arXiv:1602.08828v2, `thm:cluster` and `eq:rho-expansion`, lines 1298–1303 and 1971–2013.
-/

open Finset SimpleGraph

namespace TNLean.Lattice.ClusterExpansion

open Classical in
/-- The actual connected label intervals containing `p` and shorter than `r` number at most
`(r - 1)²`. For `r ≤ 1` this family is empty. Supporting the interaction-label version of ALVV,
arXiv:1602.08828v2, `thm:cluster`, lines 1298–1303 and 1971–2013. -/
theorem card_crossing_intervals_le {N : ℕ} (p : Fin N) (r : ℕ) :
    ((univ : Finset (Finset (Fin N))).filter (fun C : Finset (Fin N) ↦
      p ∈ C ∧ ((pathGraph N).induce (C : Set (Fin N))).Connected ∧ C.card < r)).card ≤
        (r - 1) ^ 2 := by
  classical
  let T := (univ : Finset (Finset (Fin N))).filter (fun C : Finset (Fin N) ↦
    p ∈ C ∧ ((pathGraph N).induce (C : Set (Fin N))).Connected ∧ C.card < r)
  change T.card ≤ _
  by_cases hlow : r ≤ 1
  · have hempty : T = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro C hC
      have hc := (mem_filter.mp hC).2
      have hpos := Finset.card_pos.mpr ⟨p, hc.1⟩
      omega
    rw [hempty]
    exact Nat.zero_le _
  · have hr : 2 ≤ r := by omega
    have hne (C : T) : C.val.Nonempty := ⟨p, (mem_filter.mp C.property).2.1⟩
    have hb (C : T) : p.val - (C.val.min' (hne C)).val < r - 1 ∧
        (C.val.max' (hne C)).val - p.val < r - 1 := by
      have hc := (mem_filter.mp C.property).2
      have hmin : (C.val.min' (hne C)).val ≤ p.val := C.val.min'_le p hc.1
      have hmax : p.val ≤ (C.val.max' (hne C)).val := C.val.le_max' p hc.1
      have hlen : C.val.card = (C.val.max' (hne C)).val + 1 - (C.val.min' (hne C)).val :=
        (congrArg Finset.card (eq_Icc_of_ordConnected
          (ordConnected_of_pathGraph_connected hc.2.1) (hne C))).trans (Fin.card_Icc _ _)
      omega
    let f : T → Fin (r - 1) × Fin (r - 1) := fun C ↦
      (⟨p.val - (C.val.min' (hne C)).val, (hb C).1⟩,
        ⟨(C.val.max' (hne C)).val - p.val, (hb C).2⟩)
    have hinj : Function.Injective f := by
      intro C D hCD
      have hc := (mem_filter.mp C.property).2
      have hd := (mem_filter.mp D.property).2
      have hmin : C.val.min' (hne C) = D.val.min' (hne D) := by
        apply Fin.ext
        have hCmin : (C.val.min' (hne C)).val ≤ p.val := C.val.min'_le p hc.1
        have hDmin : (D.val.min' (hne D)).val ≤ p.val := D.val.min'_le p hd.1
        have hfst : p.val - (C.val.min' (hne C)).val = p.val - (D.val.min' (hne D)).val :=
          congrArg (fun t : Fin (r - 1) × Fin (r - 1) ↦ t.1.val) hCD
        omega
      have hmax : C.val.max' (hne C) = D.val.max' (hne D) := by
        apply Fin.ext
        have hCmax : p.val ≤ (C.val.max' (hne C)).val := C.val.le_max' p hc.1
        have hDmax : p.val ≤ (D.val.max' (hne D)).val := D.val.le_max' p hd.1
        have hsnd : (C.val.max' (hne C)).val - p.val = (D.val.max' (hne D)).val - p.val :=
          congrArg (fun t : Fin (r - 1) × Fin (r - 1) ↦ t.2.val) hCD
        omega
      apply Subtype.ext
      exact (eq_Icc_of_ordConnected (ordConnected_of_pathGraph_connected hc.2.1) (hne C)).trans
        ((congrArg₂ Icc hmin hmax).trans
          (eq_Icc_of_ordConnected (ordConnected_of_pathGraph_connected hd.2.1) (hne D)).symm)
    simpa [pow_two] using Fintype.card_le_of_injective f hinj

end TNLean.Lattice.ClusterExpansion
