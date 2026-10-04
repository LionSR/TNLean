/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegionEntanglementBound
import TNLean.PEPS.TorusRectangleBoundaryCard

/-!
# The rectangular PEPS area law on a native torus

A bounded coordinate rectangle has at most `2w + 2h` crossing edges,
including empty rectangles and rectangles spanning a full period. If the crossing
virtual bonds all have dimension `D`, its normalized entanglement entropy
is at most `(2w + 2h) log D`. For a square this is `4L log D`.
The tensors may be site dependent and need not be injective.

**Scope restriction (finite simple torus):** Both periods are at least
three. The result is the finite periodic realization of the boundary-count argument,
not an assertion about arbitrary winding regions. See
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

Source: CPGSV21, arXiv:2011.12127, Section II.A.3, PEPS area law,
`Papers/2011.12127/TN-Review-main.tex`, line 445.

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
-/

namespace TNLean.PEPS

variable {width height d : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]

local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

/-- The rectangular boundary-count entropy bound for arbitrary tensors.
Source: CPGSV21, Section II.A.3, PEPS area law at line 445. -/
theorem entropy_torusRectangle_le_perimeter
    (A : Tensor (torusGraph width height) d) (hA : stateCoeff A ≠ 0)
    (xStart yStart xLen yLen : ℕ)
    (hxBound : xStart + xLen ≤ width) (hyBound : yStart + yLen ≤ height)
    (D : ℕ) (hD : ∀ e, IsRegionBoundaryEdge
      (torusContiguousRectangle xStart yStart xLen yLen) e → A.bondDim e = D) :
    let ρ := normalizedRegionReducedDensity A
      (torusContiguousRectangle xStart yStart xLen yLen)
    ∃ hρ : ρ.IsHermitian,
      0 ≤ vonNeumannEntropy ρ hρ ∧
      vonNeumannEntropy ρ hρ ≤ (2 * xLen + 2 * yLen : ℕ) * Real.log (D : ℝ) := by
  obtain ⟨hρ, hnonneg, hbound⟩ :=
    entropy_normalizedRegionReducedDensity_le_uniform_boundary A
      (torusContiguousRectangle xStart yStart xLen yLen) hA D hD
  refine ⟨hρ, hnonneg, hbound.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (Real.log_natCast_nonneg D)
  exact_mod_cast card_regionBoundaryEdge_torusRectangle_le
    xStart yStart xLen yLen hxBound hyBound

/-- A square of side length `L` has entanglement entropy at most
`4L log D`. Source: CPGSV21, Section II.A.3, the printed PEPS area-law
bound at line 445. -/
theorem entropy_torusSquare_le_four_mul
    (A : Tensor (torusGraph width height) d) (hA : stateCoeff A ≠ 0)
    (xStart yStart L : ℕ)
    (hxBound : xStart + L ≤ width) (hyBound : yStart + L ≤ height)
    (D : ℕ) (hD : ∀ e, IsRegionBoundaryEdge
      (torusContiguousRectangle xStart yStart L L) e → A.bondDim e = D) :
    let ρ := normalizedRegionReducedDensity A
      (torusContiguousRectangle xStart yStart L L)
    ∃ hρ : ρ.IsHermitian,
      0 ≤ vonNeumannEntropy ρ hρ ∧
      vonNeumannEntropy ρ hρ ≤ (4 * L : ℕ) * Real.log (D : ℝ) := by
  have h := entropy_torusRectangle_le_perimeter A hA
    xStart yStart L L hxBound hyBound D hD
  have hperimeter : 2 * L + 2 * L = 4 * L := by omega
  simpa only [hperimeter] using h

end TNLean.PEPS
