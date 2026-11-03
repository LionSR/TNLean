/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ClusterExpansion.ClusterFactorization
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.SuccPred.Archimedean

/-!
# Intervals in the path of interaction labels

The connected supports in the path graph are exactly its nonempty order intervals.
Every interval with at least `r > 0` labels contains an actual length-`r` window.
Their left endpoints give distinct labels, and every nonempty interval is determined by its
two endpoints. The resulting families characterize the existing cluster cutoff and contain the
actual components of unions of windows.

These are auxiliary geometric results for the interaction-label expansion related to ALVV,
arXiv:1602.08828v2, `thm:cluster-approx`, source lines 1935–1968. The cutoff here counts interaction
labels, rather than the induced physical-site support in the printed statement.
-/

open Finset SimpleGraph

namespace TNLean.Lattice.ClusterExpansion

variable {N : ℕ}

/-- A connected support in the path of interaction labels contains every label between two
of its labels. This is the one-dimensional geometry used in the corrected interaction-label
version of ALVV, arXiv:1602.08828v2, `thm:cluster-approx`. -/
theorem ordConnected_of_pathGraph_connected {C : Finset (Fin N)}
    (hC : ((pathGraph N).induce (C : Set (Fin N))).Connected) :
    (C : Set (Fin N)).OrdConnected := by
  refine ⟨fun a ha b hb k hk ↦ ?_⟩
  by_contra hkC
  have key : ∀ (u v : (C : Set (Fin N))), ((pathGraph N).induce (C : Set (Fin N))).Walk u v →
      (u : Fin N).val < k.val → (v : Fin N).val < k.val := by
    intro u v p
    induction p with
    | nil => exact id
    | @cons u w v hadj p ih =>
      intro hu
      apply ih
      have hw : (w : Fin N).val ≠ k.val := fun heq ↦ hkC (Fin.ext heq ▸ w.property)
      have hadj' : (u : Fin N).val + 1 = (w : Fin N).val ∨
          (w : Fin N).val + 1 = (u : Fin N).val := pathGraph_adj.mp hadj
      omega
  have ha_ne : a.val ≠ k.val := fun heq ↦ hkC (Fin.ext heq ▸ ha)
  obtain ⟨p⟩ := hC.preconnected ⟨a, ha⟩ ⟨b, hb⟩
  exact (not_lt_of_ge hk.2) (key _ _ p (lt_of_le_of_ne hk.1 ha_ne))

/-- Every nonempty interval of interaction labels is connected in the label path.
Auxiliary to ALVV, arXiv:1602.08828v2, `thm:cluster-approx`. -/
theorem pathGraph_connected_of_ordConnected {C : Finset (Fin N)}
    (hC : (C : Set (Fin N)).OrdConnected) (hne : C.Nonempty) :
    ((pathGraph N).induce (C : Set (Fin N))).Connected := by
  let := hC
  have hcov : (Set.range (OrderEmbedding.subtype (· ∈ (C : Set (Fin N))))).OrdConnected := by
    simpa using hC
  have heq : (pathGraph N).induce (C : Set (Fin N)) = hasse (C : Set (Fin N)) := by
    ext u v
    change ((u : Fin N) ⋖ (v : Fin N) ∨ (v : Fin N) ⋖ (u : Fin N)) ↔ (u ⋖ v ∨ v ⋖ u)
    exact or_congr
      (Set.OrdConnected.apply_covBy_apply_iff
        (OrderEmbedding.subtype (· ∈ (C : Set (Fin N)))) hcov)
      (Set.OrdConnected.apply_covBy_apply_iff
        (OrderEmbedding.subtype (· ∈ (C : Set (Fin N)))) hcov)
  rw [heq]
  have : Nonempty (C : Set (Fin N)) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  exact ⟨hasse_preconnected_of_succ _⟩

/-- A nonempty interval is determined by its endpoints. Auxiliary to the interaction-label
geometry in ALVV, arXiv:1602.08828v2, `thm:cluster-approx`. -/
theorem eq_Icc_of_ordConnected {C : Finset (Fin N)}
    (hC : (C : Set (Fin N)).OrdConnected) (hne : C.Nonempty) :
    C = Icc (C.min' hne) (C.max' hne) := by
  ext k
  exact ⟨fun hk ↦ mem_Icc.mpr ⟨C.min'_le k hk, C.le_max' k hk⟩,
    fun hk ↦ hC.out' (C.min'_mem hne) (C.max'_mem hne) (mem_Icc.mp hk)⟩

/-- An interval with at least `r > 0` labels contains an interval with exactly `r` labels.
Auxiliary to the interaction-label cutoff in ALVV, arXiv:1602.08828v2,
`thm:cluster-approx`. -/
theorem exists_interval_subset_card {C : Finset (Fin N)}
    (hC : (C : Set (Fin N)).OrdConnected) {r : ℕ} (hr : 0 < r) (hcard : r ≤ C.card) :
    ∃ I : Finset (Fin N), I ⊆ C ∧ (I : Set (Fin N)).OrdConnected ∧ I.card = r := by
  have hne : C.Nonempty := Finset.card_pos.mp (hr.trans_le hcard)
  have heq := eq_Icc_of_ordConnected hC hne
  have hlen : r ≤ (C.max' hne).val + 1 - (C.min' hne).val := by
    rw [← Fin.card_Icc, ← heq]
    exact hcard
  let c : Fin N := ⟨(C.min' hne).val + r - 1, by
    have hmax := (C.max' hne).isLt
    omega⟩
  refine ⟨Icc (C.min' hne) c, ?_, ?_, ?_⟩
  · intro k hk
    exact hC.out' (C.min'_mem hne) (C.max'_mem hne)
      ⟨(mem_Icc.mp hk).1, (mem_Icc.mp hk).2.trans (show c ≤ C.max' hne by
        change (C.min' hne).val + r - 1 ≤ (C.max' hne).val
        omega)⟩
  · rw [coe_Icc]
    infer_instance
  · rw [Fin.card_Icc]
    dsimp [c]
    omega

open Classical in
/-- The actual intervals containing exactly `r` interaction labels. Auxiliary to the corrected
interaction-label cutoff in ALVV, arXiv:1602.08828v2, `thm:cluster-approx`. -/
noncomputable def pathWindows (N r : ℕ) : Finset (Finset (Fin N)) :=
  {I | (I : Set (Fin N)).OrdConnected ∧ I.card = r}

/-- Membership in the family of length-`r` interaction-label windows. -/
theorem mem_pathWindows {r : ℕ} {I : Finset (Fin N)} :
    I ∈ pathWindows N r ↔ (I : Set (Fin N)).OrdConnected ∧ I.card = r := by
  classical
  simp [pathWindows]

open Classical in
/-- Discarded path supports are precisely those containing a length-`r` window. The graph
components and the windows are constructed from the actual label path. Auxiliary to the corrected
interaction-label cutoff in ALVV, arXiv:1602.08828v2, `thm:cluster-approx`. -/
theorem noLargeCluster_pathGraph_iff {r : ℕ} (hr : 0 < r) (A : Finset (Fin N)) :
    NoLargeCluster (pathGraph N) (fun C ↦ r ≤ C.card) A ↔
      ¬ ∃ I ∈ pathWindows N r, I ⊆ A := by
  classical
  constructor
  · intro hno ⟨I, hIW, hIA⟩
    have hI := mem_pathWindows.mp hIW
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (hI.2.symm ▸ hr)
    obtain ⟨C, hC, hxC⟩ := exists_isCluster_mem (pathGraph N) (hIA hx)
    have hIC : I ⊆ C := subset_of_connected_of_disjoint_boundary (pathGraph N)
      (pathGraph_connected_of_ordConnected hI.1 ⟨x, hx⟩)
      ⟨x, mem_inter.mpr ⟨hx, hxC⟩⟩ (hC.2.2.mono_left hIA)
    exact hno C hC (hI.2 ▸ Finset.card_le_card hIC)
  · intro hno C hC hsize
    obtain ⟨I, hIC, hIord, hIcard⟩ := exists_interval_subset_card
      (ordConnected_of_pathGraph_connected hC.2.1) hr hsize
    exact hno ⟨I, mem_pathWindows.mpr ⟨hIord, hIcard⟩, hIC.trans hC.1⟩

private theorem eq_of_interval_min_card {I J : Finset (Fin N)}
    (hI : (I : Set (Fin N)).OrdConnected) (hJ : (J : Set (Fin N)).OrdConnected)
    (hneI : I.Nonempty) (hneJ : J.Nonempty) (hmin : I.min' hneI = J.min' hneJ)
    (hcard : I.card = J.card) : I = J := by
  have hIeq := eq_Icc_of_ordConnected hI hneI
  have hJeq := eq_Icc_of_ordConnected hJ hneJ
  have hlenI : I.card = (I.max' hneI).val + 1 - (I.min' hneI).val :=
    (congrArg Finset.card hIeq).trans (Fin.card_Icc _ _)
  have hlenJ : J.card = (J.max' hneJ).val + 1 - (J.min' hneJ).val :=
    (congrArg Finset.card hJeq).trans (Fin.card_Icc _ _)
  have hleI : (I.min' hneI).val ≤ (I.max' hneI).val := I.min'_le _ (I.max'_mem hneI)
  have hleJ : (J.min' hneJ).val ≤ (J.max' hneJ).val := J.min'_le _ (J.max'_mem hneJ)
  have hmax : I.max' hneI = J.max' hneJ := by
    apply Fin.ext
    have hm := congrArg Fin.val hmin
    omega
  exact hIeq.trans ((congrArg₂ Icc hmin hmax).trans hJeq.symm)

/-- The length-`r` windows have distinct chosen labels belonging to them: their left endpoints.
The choice is over the actual family, so an empty chain requires no chosen label. Auxiliary to the
corrected coefficient estimate in ALVV, arXiv:1602.08828v2, `thm:cluster-approx`. -/
theorem pathWindows_exists_marker {r : ℕ} (hr : 0 < r) :
    ∃ marker : pathWindows N r → Fin N,
      (∀ I : pathWindows N r, marker I ∈ (I : Finset (Fin N))) ∧ Function.Injective marker := by
  classical
  have hne : ∀ I : pathWindows N r, (I : Finset (Fin N)).Nonempty := fun I ↦
    Finset.card_pos.mp ((mem_pathWindows.mp I.property).2.symm ▸ hr)
  refine ⟨fun I ↦ I.val.min' (hne I), fun I ↦ I.val.min'_mem (hne I), ?_⟩
  intro I J hij
  apply Subtype.ext
  exact eq_of_interval_min_card (mem_pathWindows.mp I.property).1
    (mem_pathWindows.mp J.property).1 (hne I) (hne J) hij
    ((mem_pathWindows.mp I.property).2.trans (mem_pathWindows.mp J.property).2.symm)

open Classical in
/-- The nonempty intervals containing at least `r` interaction labels. Auxiliary to the corrected
interaction-label estimate in ALVV, arXiv:1602.08828v2, `thm:cluster-approx`. -/
noncomputable def pathIntervals (N r : ℕ) : Finset (Finset (Fin N)) :=
  {I | I.Nonempty ∧ (I : Set (Fin N)).OrdConnected ∧ r ≤ I.card}

/-- Membership in the family of intervals above the interaction-label cutoff. -/
theorem mem_pathIntervals {r : ℕ} {I : Finset (Fin N)} :
    I ∈ pathIntervals N r ↔ I.Nonempty ∧ (I : Set (Fin N)).OrdConnected ∧ r ≤ I.card := by
  classical
  simp [pathIntervals]

/-- Every interval is determined by its two endpoints, so there are at most `N²` intervals
above any cutoff. Auxiliary to ALVV, arXiv:1602.08828v2, `thm:cluster-approx`. -/
theorem card_pathIntervals_le (N r : ℕ) : (pathIntervals N r).card ≤ N ^ 2 := by
  classical
  let f : pathIntervals N r → Fin N × Fin N := fun I ↦
    (I.val.min' (mem_pathIntervals.mp I.property).1,
      I.val.max' (mem_pathIntervals.mp I.property).1)
  have hinj : Function.Injective f := by
    intro I J hij
    apply Subtype.ext
    have hi := mem_pathIntervals.mp I.property
    have hj := mem_pathIntervals.mp J.property
    exact (eq_Icc_of_ordConnected hi.2.1 hi.1).trans
      ((congrArg₂ Icc (congrArg Prod.fst hij) (congrArg Prod.snd hij)).trans
        (eq_Icc_of_ordConnected hj.2.1 hj.1).symm)
  simpa [pow_two] using Fintype.card_le_of_injective f hinj

open Classical in
/-- Every component of a union of length-`r` windows is an interval of at least `r` labels.
The components are the existing graph clusters, not an additional supplied decomposition.
Auxiliary to ALVV, arXiv:1602.08828v2, `thm:cluster-approx`. -/
theorem clusters_biUnion_pathWindows_subset {r : ℕ}
    {F : Finset (Finset (Fin N))} (hF : F ⊆ pathWindows N r) :
    clusters (pathGraph N) (F.biUnion id) ⊆ pathIntervals N r := by
  classical
  intro C hCmem
  have hC := (mem_clusters (pathGraph N)).mp hCmem
  obtain ⟨x⟩ := hC.2.1.nonempty
  obtain ⟨I, hIF, hxI⟩ := mem_biUnion.mp (hC.1 x.property)
  have hI := mem_pathWindows.mp (hF hIF)
  have hIU : I ⊆ F.biUnion id := fun k hk ↦ mem_biUnion.mpr ⟨I, hIF, hk⟩
  have hIC : I ⊆ C := subset_of_connected_of_disjoint_boundary (pathGraph N)
    (pathGraph_connected_of_ordConnected hI.1 ⟨x, hxI⟩)
    ⟨x, mem_inter.mpr ⟨hxI, x.property⟩⟩ (hC.2.2.mono_left hIU)
  exact mem_pathIntervals.mpr ⟨⟨x, x.property⟩,
    ordConnected_of_pathGraph_connected hC.2.1, hI.2 ▸ card_le_card hIC⟩

end TNLean.Lattice.ClusterExpansion
