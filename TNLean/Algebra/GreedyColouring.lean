/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Greedy colouring of a graph of bounded degree

A finite graph in which every vertex has at most `d` neighbours has a proper colouring with
`d + 1` colours: colour the vertices one at a time, each with a colour not used by its
neighbours. The frustration-free area-law note colours the overlap graph of the supports this
way, so that one sweep is a product of at most `d + 1` layers of terms with disjoint supports.

## Main statements

* `SimpleGraph.colorable_succ_of_forall_degree_le`.

## References

* Reading note *Entanglement across a cut in two-dimensional frustration-free ground states*,
  November 18, 2026, `docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`,
  paragraph "Contraction in one sweep": "Color it in `χ ≤ d + 1` colors".
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableEq V]

/-- Greedy colouring along a list: some colouring with `d + 1` colours separates every pair of
adjacent vertices of the list. -/
theorem exists_colouring_list_of_forall_degree_le {d : ℕ} (hd : ∀ v, G.degree v ≤ d)
    (l : List V) : ∃ c : V → Fin (d + 1), ∀ u ∈ l, ∀ w ∈ l, G.Adj u w → c u ≠ c w := by
  induction l with
  | nil => exact ⟨fun _ ↦ 0, by simp⟩
  | cons v l ih =>
    obtain ⟨c, hc⟩ := ih
    have hcard : ((G.neighborFinset v).image c).card < (Finset.univ : Finset (Fin (d + 1))).card :=
      calc ((G.neighborFinset v).image c).card ≤ (G.neighborFinset v).card := Finset.card_image_le
        _ = G.degree v := G.card_neighborFinset_eq_degree v
        _ < d + 1 := Nat.lt_succ_of_le (hd v)
        _ = _ := by simp
    obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    have hfree : ∀ w, G.Adj v w → a ≠ c w := fun w hw h ↦
      ha (Finset.mem_image.mpr ⟨w, (G.mem_neighborFinset v w).mpr hw, h.symm⟩)
    refine ⟨Function.update c v a, fun u hu w hw huw ↦ ?_⟩
    by_cases huv : u = v
    · subst huv
      rw [Function.update_self, Function.update_of_ne huw.ne']
      exact hfree w huw
    by_cases hwv : w = v
    · subst hwv
      rw [Function.update_self, Function.update_of_ne huv]
      exact (hfree u huw.symm).symm
    rw [Function.update_of_ne huv, Function.update_of_ne hwv]
    exact hc u ((List.mem_cons.mp hu).resolve_left huv) w
      ((List.mem_cons.mp hw).resolve_left hwv) huw

/-- **Greedy colouring.** A finite graph of maximum degree at most `d` is `d + 1` colourable.
Source: `docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`, paragraph
"Contraction in one sweep". -/
theorem colorable_succ_of_forall_degree_le {d : ℕ} (hd : ∀ v, G.degree v ≤ d) :
    G.Colorable (d + 1) := by
  obtain ⟨c, hc⟩ := G.exists_colouring_list_of_forall_degree_le hd Finset.univ.toList
  exact ⟨Coloring.mk c fun {u w} huw ↦ hc u (by simp) w (by simp) huw⟩

end SimpleGraph
