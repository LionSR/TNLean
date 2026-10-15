/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.CellTwoFamilyPartition

/-!
# Regression checks for the two-family partition of a cell

The unit cell at the origin has exactly one lattice site, and the partition of
the unit cell has a number of pieces and remainder sites bounded uniformly in
the exterior colours. The main theorem depends only on the standard axioms.
-/

set_option linter.hashCommand false

open TNLean.PEPS.AreaLaw.Geometry TNLean.PEPS.Approximation.CellPartition

example : cellSample (0, 0) 1 (0, 0) = {(0, 0)} := by
  ext p
  simp [cellSample, latticeBox, cellCorner, Prod.ext_iff]

example : ∃ C : ℝ, ∀ c : ℤ × ℤ → Fin 2,
    ∃ (P : OrderedTwoFamilyPartition (cellSample (0, 0) 1 (0, 0)))
      (scale : Fin P.pieceCount → ℝ),
      (∀ i, ∀ x ∈ P.piece i, ∀ y : ℤ × ℤ, cellIndex (0, 0) 1 (integerPoint y) ≠ (0, 0) →
        c (cellIndex (0, 0) 1 (integerPoint y)) = P.family i →
          scale i ^ (1 / 2 : ℝ) < dist (integerPoint x) (integerPoint y)) ∧
      (P.pieceCount : ℝ) + P.residual.card ≤ C := by
  obtain ⟨_ustar, -, -, C, K, -, h⟩ :=
    exists_cell_twoFamily_partition (γ := 1 / 2) (by norm_num) 0
  refine ⟨C, fun c ↦ ?_⟩
  obtain ⟨P, scale, -, -, -, hext, -, hcount⟩ := h 1 le_rfl (0, 0) (0, 0) c
  exact ⟨P, scale, hext, by simpa using hcount⟩

/--
info: 'TNLean.PEPS.Approximation.CellPartition.exists_cell_twoFamily_partition' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.Approximation.CellPartition.exists_cell_twoFamily_partition
