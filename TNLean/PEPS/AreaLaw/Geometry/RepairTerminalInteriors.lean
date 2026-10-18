/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairTermination

/-!
# Terminal interiors before an empty generation

Once a generation has no repair marks, every later generation is also empty.
Thus the union of terminal-square interiors over all generations is already
the union over the finitely many preceding generations. These are open
interiors; no assertion about the closed terminal squares or unassigned
boundary points is made here.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
Section 11, termination, lines 538–541, final regions, lines 558–561, and the
finite partition argument, lines 694–707. Source revision:
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Geometry

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
  (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ)

local notation "𝔇" => repairStage o Λ A C k₀ hC h₀ Sstar

/-- The accumulated terminal interiors are the union of the contributions
strictly before an empty generation.
Source: area-law Section 11, lines 538–541, 558–561 and 694–707. -/
theorem repairTerminalInteriors_eq_iUnion_lt_of_isEmpty (N : ℕ)
    [IsEmpty (𝔇 N).markIndex] :
    repairTerminalInteriors o Λ A C k₀ hC h₀ Sstar =
      ⋃ j < N, repairTerminalInteriorSet (𝔇 j).location (𝔇 j).scale Sstar := by
  refine Set.iUnion_congr fun j ↦ ?_
  by_cases hj : j < N
  · simp only [hj, Set.iUnion_true]
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hj)
    have : IsEmpty (𝔇 (N + n)).markIndex :=
      isEmpty_repairStage_markIndex_add o Λ A C k₀ hC h₀ Sstar N n inferInstance
    simp only [repairTerminalInteriorSet, Set.iUnion_of_empty, Set.iUnion_empty]

end TNLean.PEPS.AreaLaw.Geometry
