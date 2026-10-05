/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusCoordinateSwap
import TNLean.PEPS.TorusWindowCrossTensorGauge

/-!
# Equality of all torus bond dimensions from normal arc windows

The staircase algebra isomorphism determines one horizontal bond dimension.
Exchanging coordinates gives a vertical comparison. Translation invariance then
identifies the dimensions at every edge. The argument uses the same arc-window
hypotheses in both directions and does not assume equality of the products of
non-boundary bond dimensions.

The bond-dimension theorem accepts all positive window lengths at the source's minimal
torus sizes. The complete derivation is recorded in
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`.

Source: arXiv:1804.04964, lines 582--586 and 2368--2444 of
`Papers/1804.04964/paper_normal.tex`.
-/

namespace TNLean.PEPS
variable {width height d L K : ℕ} [NeZero width] [NeZero height]
variable [Fact (1 < width)] [Fact (1 < height)]

private theorem bondDim_eq_of_orientation_references
    (A B : Tensor (torusGraph width height) d)
    (hATI : IsTorusTranslationInvariant A) (hBTI : IsTorusTranslationInvariant B)
    (hH : A.bondDim (torusRightEdge 0) = B.bondDim (torusRightEdge 0))
    (hV : A.bondDim (torusUpEdge 0) = B.bondDim (torusUpEdge 0)) :
    A.bondDim = B.bondDim := by
  funext e
  rcases torusEdge_horizontal_or_vertical e with he | he
  · exact (torusUniformBondDim_of_translationInvariant hATI).1 e he |>.trans
      (hH.trans ((torusUniformBondDim_of_translationInvariant hBTI).1 e he).symm)
  · exact (torusUniformBondDim_of_translationInvariant hATI).2 e he |>.trans
      (hV.trans ((torusUniformBondDim_of_translationInvariant hBTI).2 e he).symm)

end TNLean.PEPS

namespace TNLean.PEPS
variable {width height d L K : ℕ} [NeZero width] [NeZero height]
variable [Fact (1 < width)] [Fact (1 < height)]
private theorem horizontalBondDim_eq_at_origin
    (A B : Tensor (torusGraph width height) d)
    (hA : NormalTorusArcWindowInjectivityHypotheses L K (regionInjectivityDataOf A))
    (hB : NormalTorusArcWindowInjectivityHypotheses L K (regionInjectivityDataOf B))
    (hATI : IsTorusTranslationInvariant A) (hBTI : IsTorusTranslationInvariant B)
    (hAB : SameState A B)
    (hposA : ∀ e : Edge (torusGraph width height), 0 < A.bondDim e)
    (hposB : ∀ e : Edge (torusGraph width height), 0 < B.bondDim e)
    (hL : 0 < L) (hK : 0 < K)
    (hxw : 2 * L + 1 ≤ width) (hyh : 2 * K + 1 ≤ height) :
    A.bondDim (torusRightEdge 0) = B.bondDim (torusRightEdge 0) := by
  have hD := staircaseCrossTensor_bondDim_eq (a := 1) (b := 0)
    A B hA hB hATI hBTI hAB hposA hposB hL hK (by omega)
    (by omega) (by omega) hxw hyh
  simp only [horizontalStaircaseReferenceEdge, Nat.cast_zero, zero_add, Nat.cast_one] at hD
  exact (bondDim_torusRightEdge_const hATI
    ((1 : ZMod width) + ((L - 1 : ℕ) : ZMod width), ((K - 1 : ℕ) : ZMod height)) 0).trans
    (hD.trans (bondDim_torusRightEdge_const hBTI
      ((1 : ZMod width) + ((L - 1 : ℕ) : ZMod width), ((K - 1 : ℕ) : ZMod height)) 0).symm)
end TNLean.PEPS

namespace TNLean.PEPS
variable {width height d L K : ℕ} [NeZero width] [NeZero height]
variable [Fact (1 < width)] [Fact (1 < height)]

/-- Equality of PEPS states determines every bond dimension under normal arc-window
injectivity. The torus has at least `2 * L + 1` columns and `2 * K + 1` rows,
with positive `L` and `K`. The proof compares a horizontal staircase bond, exchanges the
coordinates for the vertical comparison, and uses translation invariance.

Source: arXiv:1804.04964, lines 582--586 and 2368--2444 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem bondDim_eq_of_normalArcWindows_sameState
    (A B : Tensor (torusGraph width height) d)
    (hA : NormalTorusArcWindowInjectivityHypotheses L K (regionInjectivityDataOf A))
    (hB : NormalTorusArcWindowInjectivityHypotheses L K (regionInjectivityDataOf B))
    (hATI : IsTorusTranslationInvariant A) (hBTI : IsTorusTranslationInvariant B)
    (hAB : SameState A B)
    (hposA : ∀ e : Edge (torusGraph width height), 0 < A.bondDim e)
    (hposB : ∀ e : Edge (torusGraph width height), 0 < B.bondDim e)
    (hL : 0 < L) (hK : 0 < K)
    (hxw : 2 * L + 1 ≤ width) (hyh : 2 * K + 1 ≤ height) :
    A.bondDim = B.bondDim := by
  have hH := horizontalBondDim_eq_at_origin A B hA hB hATI hBTI hAB
    hposA hposB hL hK hxw hyh
  have hV' := horizontalBondDim_eq_at_origin
    (A.transport torusCoordinateSwap) (B.transport torusCoordinateSwap)
    (hA.transportCoordinateSwap A) (hB.transportCoordinateSwap B)
    (hATI.transportCoordinateSwap A) (hBTI.transportCoordinateSwap B)
    (hAB.transport torusCoordinateSwap)
    (fun e ↦ hposA (Edge.map torusCoordinateSwap.symm e))
    (fun e ↦ hposB (Edge.map torusCoordinateSwap.symm e)) hK hL hyh hxw
  have hzero : (0 : TorusVertex width height) = (0, 0) := rfl
  have hV : A.bondDim (torusUpEdge 0) = B.bondDim (torusUpEdge 0) := by
    rw [hzero]
    simpa [Tensor.transport_bondDim, torusCoordinateSwap_symm,
      Edge.map_torusCoordinateSwap_rightEdge] using hV'
  exact bondDim_eq_of_orientation_references A B hATI hBTI hH hV

end TNLean.PEPS
