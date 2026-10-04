/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.TorusRegularRegionSupport
import TNLean.PEPS.TorusRectangleBoundaryCard

/-!
# The symmetry correction to a regular rectangular entropy bound

A positive bounded rectangle of side lengths `w,h`, both shorter than the
torus periods, has `2w + 2h` crossing bonds. For arbitrary regular G-injective
site tensors, its physical reduced density has rank `|G|^(2w + 2h - 1)`.
The normalized von Neumann entropy is at most `(2w + 2h - 1) log |G|`, and
the zero-order Rényi entropy is exactly that value. Isometry is not assumed.

**Scope restriction (regular native rectangles):** Both torus periods are at
least three, the virtual representation is regular, and the rectangle is
positive and bounded with both side lengths strictly smaller than the
periods. The statement concerns the ordinary untwisted closed vector; see
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, rectangular
boundary construction and Corollary 6.10, local source lines 1935–1957
and 2074–2090. The von Neumann inequality follows from Wolf Section 8.2.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]

local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height

/-- Numbering the actual rectangular crossing bonds after removing one
reference label from the exponent. Source: SCP10, the regular boundary
coordinates in Corollary 6.10, lines 2074–2090. -/
noncomputable def torusRectangleBoundaryEquiv
    (xStart yStart xLen yLen : ℕ) (hxPos : 0 < xLen) (hyPos : 0 < yLen)
    (hxBound : xStart + xLen ≤ width) (hyBound : yStart + yLen ≤ height)
    (hxLen : xLen < width) (hyLen : yLen < height) :
    {f : Edge Γₜ // IsRegionBoundaryEdge
      (torusContiguousRectangle xStart yStart xLen yLen) f} ≃
        Fin (2 * xLen + 2 * yLen - 1 + 1) := by
  apply Fintype.equivFinOfCardEq
  rw [card_regionBoundaryEdge_torusRectangle
    xStart yStart xLen yLen hxPos hyPos hxBound hyBound hxLen hyLen]
  omega

variable {G : Type*} [Group G] [Fintype G] {d : ℕ}

/-- The exact rectangular physical Schmidt rank for regular G-injective
site tensors, without isometry. Source: SCP10, Corollary 6.10,
lines 2074–2090, specialized to the untwisted rectangular cut. -/
theorem rank_regionReducedDensity_regular_torusRectangle
    (a : (v : X) → (IncidentEdge Γₜ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γₜ v))
      (regularSiteMap (a v)))
    (xStart yStart xLen yLen : ℕ) (hxPos : 0 < xLen) (hyPos : 0 < yLen)
    (hxBound : xStart + xLen ≤ width) (hyBound : yStart + yLen ≤ height)
    (hxLen : xLen < width) (hyLen : yLen < height) :
    (regionReducedDensity (groupBondTensor a)
      (torusContiguousRectangle xStart yStart xLen yLen)).rank =
        Fintype.card G ^ (2 * xLen + 2 * yLen - 1) :=
  rank_regionReducedDensity_of_regular_connected_cut a ha _
    (torusGraph_rectangle_connected xStart yStart xLen yLen hxPos hyPos hxBound hyBound)
    (torusGraph_compl_rectangle_connected xStart yStart xLen yLen hxLen hyLen) _
    (torusRectangleBoundaryEquiv
      xStart yStart xLen yLen hxPos hyPos hxBound hyBound hxLen hyLen)

/-- The symmetry-improved entropy bound and exact zero-order Rényi entropy
of a regular G-injective rectangular cut. Source: SCP10, Corollary 6.10,
lines 2074–2090, and Wolf Section 8.2 for the entropy-rank bound. -/
theorem entropy_normalizedRegionReducedDensity_regular_torusRectangle
    (a : (v : X) → (IncidentEdge Γₜ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γₜ v))
      (regularSiteMap (a v)))
    (xStart yStart xLen yLen : ℕ) (hxPos : 0 < xLen) (hyPos : 0 < yLen)
    (hxBound : xStart + xLen ≤ width) (hyBound : yStart + yLen ≤ height)
    (hxLen : xLen < width) (hyLen : yLen < height) :
    let ρ := normalizedRegionReducedDensity (groupBondTensor a)
      (torusContiguousRectangle xStart yStart xLen yLen)
    ∃ hρ : ρ.IsHermitian,
      0 ≤ vonNeumannEntropy ρ hρ ∧
      vonNeumannEntropy ρ hρ ≤
        (2 * xLen + 2 * yLen - 1 : ℕ) * Real.log (Fintype.card G : ℝ) ∧
      renyiEntropy ρ hρ 0 =
        (2 * xLen + 2 * yLen - 1 : ℕ) * Real.log (Fintype.card G : ℝ) := by
  classical
  exact entropy_normalizedRegionReducedDensity_of_regular_connected_cut a ha _
    (torusGraph_rectangle_connected xStart yStart xLen yLen hxPos hyPos hxBound hyBound)
    (torusGraph_compl_rectangle_connected xStart yStart xLen yLen hxLen hyLen) _
    (torusRectangleBoundaryEquiv
      xStart yStart xLen yLen hxPos hyPos hxBound hyBound hxLen hyLen)

end TNLean.PEPS
