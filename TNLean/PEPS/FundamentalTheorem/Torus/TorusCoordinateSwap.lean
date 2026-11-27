/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.FundamentalTheorem.Torus.Window.WindowComplement
import TNLean.PEPS.Tensor.Torus.TorusTranslationInvariant
import TNLean.PEPS.Tensor.Region.RegionTransport

/-!
# Exchange of torus coordinates

The graph isomorphism `(x, y) ↦ (y, x)` (`torusCoordinateSwap`, in
`TNLean/PEPS/Graph/Torus/TorusTranslation.lean`) exchanges the two edge directions and the
side lengths of arc rectangles. Regional injectivity and translation invariance
are preserved under this change of coordinates.

These identities implement the exchange of directions in the two-dimensional
argument of arXiv:1804.04964, lines 2368--2444 of
`Papers/1804.04964/paper_normal.tex`.
-/

namespace TNLean.PEPS
variable {width height d : ℕ} [NeZero width] [NeZero height]
variable [Fact (1 < width)] [Fact (1 < height)]

/-- Coordinate exchange sends an `L × K` arc rectangle to a `K × L` arc rectangle. -/
theorem Region_map_torusCoordinateSwap_arcRectangle
    (s : TorusVertex width height) (L K : ℕ) :
    Region.map torusCoordinateSwap (torusArcRectangle s L K) =
      torusArcRectangle (s.2, s.1) K L := by
  ext v
  simp only [mem_Region_map, torusCoordinateSwap_symm,
    torusCoordinateSwap_apply, mem_torusArcRectangle]
  exact and_comm

/-- Arc-window injectivity is preserved by coordinate exchange, with side lengths exchanged. -/
theorem NormalTorusArcWindowInjectivityHypotheses.transportCoordinateSwap
    (A : Tensor (torusGraph width height) d) {L K : ℕ}
    (h : NormalTorusArcWindowInjectivityHypotheses L K (regionInjectivityDataOf A)) :
    NormalTorusArcWindowInjectivityHypotheses K L
      (regionInjectivityDataOf (A.transport torusCoordinateSwap)) where
  arcWindow_injective := by
    intro s
    change RegionBlockedTensorInjective (A.transport torusCoordinateSwap)
      (torusArcRectangle s K L)
    rw [← Region_map_torusCoordinateSwap_arcRectangle (s.2, s.1) L K]
    exact (regionBlockedTensorInjective_transport A torusCoordinateSwap
      (torusArcRectangle (s.2, s.1) L K)).mpr (h.arcWindow_injective (s.2, s.1))

/-- Coordinate exchange sends a right edge to the corresponding up edge. -/
theorem _root_.ManyBody.Edge.map_torusCoordinateSwap_rightEdge (p : TorusVertex width height) :
    ManyBody.Edge.map torusCoordinateSwap (torusRightEdge p) = torusUpEdge (p.2, p.1) := by
  unfold torusRightEdge
  apply ManyBody.Edge.ofAdj_eq_ofAdj
  rcases ManyBody.Edge.ofAdj_endpoints (torusGraph_adj_right p.1 p.2) with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · exact Or.inl ⟨by rw [h₁]; rfl, by rw [h₂]; rfl⟩
  · exact Or.inr ⟨by rw [h₁]; rfl, by rw [h₂]; rfl⟩

/-- Translation invariance is preserved by coordinate exchange. -/
theorem IsTorusTranslationInvariant.transportCoordinateSwap
    (A : Tensor (torusGraph width height) d) (h : IsTorusTranslationInvariant A) :
    IsTorusTranslationInvariant (A.transport torusCoordinateSwap) := by
  intro a b
  rw [Tensor.transport_trans, ← torusCoordinateSwap_translate b a,
    ← Tensor.transport_trans, h b a]

end TNLean.PEPS
