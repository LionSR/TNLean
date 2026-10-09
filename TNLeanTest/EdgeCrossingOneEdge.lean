/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.EdgeCrossingBudget

/-! A nonempty one-edge lattice regression for the exact budget. -/

open TNLean.PEPS TNLean.PEPS.AreaLaw
open scoped BigOperators

private def sample : Finset (ℤ × ℤ) := {(0, 0), (1, 0)}
private def left : Site sample := ⟨(0, 0), by simp [sample]⟩
private def right : Site sample := ⟨(1, 0), by simp [sample]⟩

private theorem site_cases (v : Site sample) : v = left ∨ v = right := by
  have hv := v.property
  simp only [sample, Finset.mem_insert, Finset.mem_singleton] at hv
  exact hv.elim (fun h ↦ Or.inl (Subtype.ext h)) (fun h ↦ Or.inr (Subtype.ext h))

private theorem boundary_one : edgeBoundary sample {left} = {s(left, right)} := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨_, x, hx, y, hy, hxy⟩ := Finset.mem_filter.mp he
    have hx' : x = left := Finset.mem_singleton.mp hx
    have hy' : y = right := (site_cases y).resolve_left
      (fun h ↦ hy (Finset.mem_singleton.mpr h))
    exact Finset.mem_singleton.mpr
      (hxy.trans (congrArg₂ (fun x y ↦ s(x, y)) hx' hy'))
  · intro he
    have he' := Finset.mem_singleton.mp he
    rw [he']
    apply Finset.mem_filter.mpr
    refine ⟨SimpleGraph.mem_edgeFinset.mpr ?_, left, Finset.mem_singleton_self _,
      right, ?_, rfl⟩
    · change (domainGraph sample).Adj left right
      simp [domainGraph, left, right]
    · simp only [Finset.mem_singleton]
      intro h
      have h' := congrArg Subtype.val h
      norm_num [left, right] at h'

example [LinearOrder (Site sample)] :
    (Entropy.crossingTerms nearestNeighborSupport {left}).card = 1 := by
  rw [card_crossingTerms_nearestNeighbor, boundary_one, Finset.card_singleton]

example [LinearOrder (Site sample)] (q : ℕ) (J : ℝ) :
    (∑ _j : Fin 1, (1 : ℝ) ^ 2 *
      ∑ i ∈ Entropy.crossingTerms nearestNeighborSupport {left},
        (Fintype.card (↥(nearestNeighborSupport i ∩ {left}) → Fin q) : ℝ) ^ 2 * J) =
      (q : ℝ) ^ 2 * J := by
  rw [nearestNeighbor_crossing_budget q J (fun _ : Fin 1 ↦ {left}) (fun _ ↦ 1)]
  simp [boundary_one]
