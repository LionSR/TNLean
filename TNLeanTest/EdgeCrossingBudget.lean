/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.EdgeCrossingBudget

/-! Crossing dimensions and degenerate boundary regressions. -/

open TNLean.PEPS TNLean.PEPS.AreaLaw
open scoped BigOperators

section
variable {V : Type*} [LinearOrder V]
variable {x y : V} {A : Finset V}
variable (h : (∃ v ∈ ({x, y} : Finset V), v ∈ A) ∧
  ∃ v ∈ ({x, y} : Finset V), v ∉ A)

-- A qubit crossing has coefficient four, not sixteen.
example : (Fintype.card (↥(({x, y} : Finset V) ∩ A) → Fin 2) : ℝ) ^ 2 = 4 := by
  rw [card_pair_insideConfig_of_crossing 2 h]
  norm_num

example : (Fintype.card (↥(({x, y} : Finset V) ∩ A) → Fin 2) : ℝ) ^ 2 ≠ 16 := by
  rw [card_pair_insideConfig_of_crossing 2 h]
  norm_num

example : Fintype.card (↥(({x, y} : Finset V) ∩ A) → Fin 0) = 0 :=
  card_pair_insideConfig_of_crossing 0 h

example : Fintype.card (↥(({x, y} : Finset V) ∩ A) → Fin 1) = 1 :=
  card_pair_insideConfig_of_crossing 1 h
end

example (Λ : Finset (ℤ × ℤ)) [LinearOrder (Site Λ)] :
    (Entropy.crossingTerms (nearestNeighborSupport (Λ := Λ)) ∅).card = 0 := by
  rw [card_crossingTerms_nearestNeighbor, edgeBoundary_empty, Finset.card_empty]

example (Λ : Finset (ℤ × ℤ)) [LinearOrder (Site Λ)] :
    (Entropy.crossingTerms (nearestNeighborSupport (Λ := Λ)) Finset.univ).card = 0 := by
  rw [card_crossingTerms_nearestNeighbor, edgeBoundary_univ, Finset.card_empty]

example [LinearOrder (Site (∅ : Finset (ℤ × ℤ)))]
    (A : Finset (Site (∅ : Finset (ℤ × ℤ)))) :
    (Entropy.crossingTerms nearestNeighborSupport A).card = 0 := by
  have hA : A = ∅ := Finset.eq_empty_of_isEmpty A
  rw [hA, card_crossingTerms_nearestNeighbor, edgeBoundary_empty, Finset.card_empty]

example (Λ : Finset (ℤ × ℤ)) [LinearOrder (Site Λ)] (q : ℕ) (J : ℝ)
    (regions : Fin 0 → Finset (Site Λ)) (a : Fin 0 → ℝ) :
    (∑ j : Fin 0, a j ^ 2 * ∑ i ∈ Entropy.crossingTerms nearestNeighborSupport (regions j),
      (Fintype.card (↥(nearestNeighborSupport i ∩ regions j) → Fin q) : ℝ) ^ 2 * J) = 0 := by
  simp

example (Λ : Finset (ℤ × ℤ)) [LinearOrder (Site Λ)] (q : ℕ) {m : ℕ}
    (regions : Fin m → Finset (Site Λ)) (a : Fin m → ℝ) :
    (∑ j : Fin m, a j ^ 2 * ∑ i ∈ Entropy.crossingTerms nearestNeighborSupport (regions j),
      (Fintype.card (↥(nearestNeighborSupport i ∩ regions j) → Fin q) : ℝ) ^ 2 * (0 : ℝ)) = 0 := by
  simp

-- Both endpoint orientations use the same one-site inside dimension.
example : Fintype.card (↥(({0, 1} : Finset (Fin 2)) ∩ {0}) → Fin 2) = 2 := by
  apply card_pair_insideConfig_of_crossing
  decide

example : Fintype.card (↥(({1, 0} : Finset (Fin 2)) ∩ {0}) → Fin 2) = 2 := by
  apply card_pair_insideConfig_of_crossing
  decide

example : (0 : Fin 2) ∉ Entropy.crossingTerms (fun v : Fin 2 ↦ {v}) {0} :=
  not_mem_crossingTerms_singleton _ _
