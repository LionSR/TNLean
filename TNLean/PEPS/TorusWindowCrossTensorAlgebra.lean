/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusWindowCrossTensorRealization

/-!
# The staircase cross-tensor algebra isomorphism

Two normal translation-invariant torus tensors generating the same state induce inverse
algebra isomorphisms on the highlighted horizontal bond. The identity physical operation fixes
the common blocked image. Equality of realized physical actions on that image proves that
exchanging the two tensors gives the inverse virtual assignment.

**Scope restriction (displayed horizontal staircase, `L, K ≥ 2`):** These results concern the
non-wrapping horizontal coordinates supported by the staircase comparison. Smaller windows
and the translation/rotation assembly for the full two-dimensional theorem remain recorded in
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`.

Source: arXiv:1804.04964, the algebra-isomorphism argument at lines 563--582 and its
two-dimensional reduction at lines 2320--2444 of `Papers/1804.04964/paper_normal.tex`.
-/

namespace TNLean.PEPS

section StaircaseAlgebra
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (1 < width)] [Fact (1 < height)]
variable {d L K a b : ℕ}
variable (A B : Tensor (torusGraph width height) d)
variable (hA : NormalTorusArcWindowInjectivityHypotheses L K
  (regionInjectivityDataOf (G := torusGraph width height) A))
variable (hB : NormalTorusArcWindowInjectivityHypotheses L K
  (regionInjectivityDataOf (G := torusGraph width height) B))
variable (hATI : IsTorusTranslationInvariant A) (hBTI : IsTorusTranslationInvariant B)
variable (hAB : SameState A B)
variable (hposA : ∀ e : Edge (torusGraph width height), 0 < A.bondDim e)
variable (hposB : ∀ e : Edge (torusGraph width height), 0 < B.bondDim e)
variable (hL : 2 ≤ L) (hK : 2 ≤ K) (ha0 : 1 ≤ a)
variable (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
variable (hxw : 2 * L + 1 ≤ width) (hyh : 2 * K + 1 ≤ height)

include hB hposB hxw hyh in
private theorem leftInsert_injective :
    Function.Injective (bondInsertedRegionInsert B
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
      (⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge
        B (by omega) (by omega) ha0 haw hbh⟩)) := by
  have hRB : RegionBlockedTensorInjective B
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K) := by
    have hi := hB.horizontalStaircaseLeftWindow_injective
      ((a : ZMod width), (b : ZMod height))
    rwa [regionInjectivityDataOf_isInjective] at hi
  exact bondInsertedRegionInsert_injective B
    (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K) hRB
    (hB.regionBlockedTensorInjective_windowComplement
      (regionInjectivityUnionClosure_of_overlap B hposB) hL hK hxw hyh _) hposB
    ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge
        B (by omega) (by omega) ha0 haw hbh⟩

/-- The canonical cross-tensor virtual assignment preserves addition.

Source: arXiv:1804.04964, the algebra assignment at lines 563--582. -/
theorem staircaseCrossTensorVirtualOperation_add (X Y) :
    (staircaseCrossTensorVirtualOperation A B hA hB hATI hBTI hAB
      hposA hposB hL hK ha0 haw hbh hxw hyh) (X + Y) =
      (staircaseCrossTensorVirtualOperation A B hA hB hATI hBTI hAB
      hposA hposB hL hK ha0 haw hbh hxw hyh) X +
      (staircaseCrossTensorVirtualOperation A B hA hB hATI hBTI hAB
      hposA hposB hL hK ha0 haw hbh hxw hyh) Y := by
  apply leftInsert_injective B hB hposB hL hK ha0 haw hbh hxw hyh
  rw [← staircaseCrossTensorVirtualOperation_realizes A B hA hB hATI hBTI hAB
    hposA hposB hL hK ha0 haw hbh hxw hyh,
    bondInsertedRegionInsert_add,
    ← staircaseCrossTensorVirtualOperation_realizes A B hA hB hATI hBTI hAB
      hposA hposB hL hK ha0 haw hbh hxw hyh,
    ← staircaseCrossTensorVirtualOperation_realizes A B hA hB hATI hBTI hAB
      hposA hposB hL hK ha0 haw hbh hxw hyh,
    staircaseO1PhysicalOp_add]
  rfl

/-- The canonical cross-tensor virtual assignment is complex linear.

Source: arXiv:1804.04964, the algebra assignment at lines 563--582. -/
theorem staircaseCrossTensorVirtualOperation_smul (c : ℂ) (X) :
    (staircaseCrossTensorVirtualOperation A B hA hB hATI hBTI hAB
      hposA hposB hL hK ha0 haw hbh hxw hyh) (c • X) =
      c • (staircaseCrossTensorVirtualOperation A B hA hB hATI hBTI hAB
      hposA hposB hL hK ha0 haw hbh hxw hyh) X := by
  apply leftInsert_injective B hB hposB hL hK ha0 haw hbh hxw hyh
  rw [← staircaseCrossTensorVirtualOperation_realizes A B hA hB hATI hBTI hAB
    hposA hposB hL hK ha0 haw hbh hxw hyh,
    bondInsertedRegionInsert_smul,
    ← staircaseCrossTensorVirtualOperation_realizes A B hA hB hATI hBTI hAB
      hposA hposB hL hK ha0 haw hbh hxw hyh,
    staircaseO1PhysicalOp_smul]
  rfl

/-- The canonical cross-tensor virtual assignment preserves the identity matrix. The
physical operation attached to the identity fixes the common blocked image.

Source: arXiv:1804.04964, the algebra assignment at lines 563--582. -/
theorem staircaseCrossTensorVirtualOperation_one :
    staircaseCrossTensorVirtualOperation A B hA hB hATI hBTI hAB
      hposA hposB hL hK ha0 haw hbh hxw hyh 1 = 1 := by
  apply leftInsert_injective B hB hposB hL hK ha0 haw hbh hxw hyh
  rw [← staircaseCrossTensorVirtualOperation_realizes A B hA hB hATI hBTI hAB
    hposA hposB hL hK ha0 haw hbh hxw hyh]
  funext μ
  rw [bondInsertedRegionInsert_one]
  exact physicalOps_eq_on_blocks_of_sameState A B _ hAB
    (hA.regionBlockedTensorInjective_windowComplement
      (regionInjectivityUnionClosure_of_overlap A hposA) hL hK hxw hyh _)
    (hB.regionBlockedTensorInjective_windowComplement
      (regionInjectivityUnionClosure_of_overlap B hposB) hL hK hxw hyh _)
    hposA hposB _ 1
    (fun ν ↦ by
      change regionInsertOfPhysicalOp A
        (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K) _ ν =
        regionBlockedWeight A
          (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K) ν
      rw [staircaseO1PhysicalOp_realizes_insert A hA (by omega) (by omega)
        ha0 haw hbh (by omega)]
      exact bondInsertedRegionInsert_one A _ _ ν) μ

/-- Exchanging the two tensors gives the inverse of the canonical virtual assignment.

Source: arXiv:1804.04964, the symmetry argument at lines 563--582. -/
theorem staircaseCrossTensorVirtualOperation_reverse (X) :
    staircaseCrossTensorVirtualOperation B A hB hA hBTI hATI hAB.symm
      hposB hposA hL hK ha0 haw hbh hxw hyh
      (staircaseCrossTensorVirtualOperation A B hA hB hATI hBTI hAB
        hposA hposB hL hK ha0 haw hbh hxw hyh X) = X := by
  let Y := staircaseCrossTensorVirtualOperation A B hA hB hATI hBTI hAB
    hposA hposB hL hK ha0 haw hbh hxw hyh X
  have hO : ∀ μ, staircaseO1PhysicalOp B hB (by omega) (by omega) haw (by omega) Y
      (regionBlockedWeight B
        (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K) μ) =
      staircaseO1PhysicalOp A hA (by omega) (by omega) haw (by omega) X
      (regionBlockedWeight B
        (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K) μ) := by
    intro μ
    change regionInsertOfPhysicalOp B _ _ μ = regionInsertOfPhysicalOp B _ _ μ
    rw [staircaseO1PhysicalOp_realizes_insert B hB (by omega) (by omega)
      ha0 haw hbh (by omega),
      staircaseCrossTensorVirtualOperation_realizes A B hA hB hATI hBTI hAB
        hposA hposB hL hK ha0 haw hbh hxw hyh]
  apply leftInsert_injective A hA hposA hL hK ha0 haw hbh hxw hyh
  rw [← staircaseCrossTensorVirtualOperation_realizes B A hB hA hBTI hATI hAB.symm
      hposB hposA hL hK ha0 haw hbh hxw hyh,
    ← staircaseO1PhysicalOp_realizes_insert A hA (by omega) (by omega)
      ha0 haw hbh (by omega)]
  funext μ
  exact physicalOps_eq_on_blocks_of_sameState B A _ hAB.symm
    (hB.regionBlockedTensorInjective_windowComplement
      (regionInjectivityUnionClosure_of_overlap B hposB) hL hK hxw hyh _)
    (hA.regionBlockedTensorInjective_windowComplement
      (regionInjectivityUnionClosure_of_overlap A hposA) hL hK hxw hyh _)
    hposB hposA _ _ hO μ

include hA hB hATI hBTI hAB hposA hposB hL hK ha0 haw hbh hxw hyh in
/-- The canonical staircase virtual assignment is an algebra isomorphism, with inverse
given by the canonical assignment in the opposite direction.

Source: arXiv:1804.04964, the algebra-isomorphism argument at lines 563--582. -/
noncomputable def staircaseCrossTensorAlgEquiv :
    Matrix (Fin (A.bondDim (horizontalStaircaseReferenceEdge
      ((a : ZMod width), (b : ZMod height)) L K)))
      (Fin (A.bondDim (horizontalStaircaseReferenceEdge
      ((a : ZMod width), (b : ZMod height)) L K))) ℂ ≃ₐ[ℂ]
    Matrix (Fin (B.bondDim (horizontalStaircaseReferenceEdge
      ((a : ZMod width), (b : ZMod height)) L K)))
      (Fin (B.bondDim (horizontalStaircaseReferenceEdge
      ((a : ZMod width), (b : ZMod height)) L K))) ℂ :=
  AlgEquiv.ofLinearEquiv
    { toFun := staircaseCrossTensorVirtualOperation A B hA hB hATI hBTI hAB
        hposA hposB hL hK ha0 haw hbh hxw hyh
      invFun := staircaseCrossTensorVirtualOperation B A hB hA hBTI hATI hAB.symm
        hposB hposA hL hK ha0 haw hbh hxw hyh
      left_inv := staircaseCrossTensorVirtualOperation_reverse A B hA hB
        hATI hBTI hAB hposA hposB hL hK ha0 haw hbh hxw hyh
      right_inv := staircaseCrossTensorVirtualOperation_reverse B A hB hA
        hBTI hATI hAB.symm hposB hposA hL hK ha0 haw hbh hxw hyh
      map_add' := staircaseCrossTensorVirtualOperation_add A B hA hB
        hATI hBTI hAB hposA hposB hL hK ha0 haw hbh hxw hyh
      map_smul' := staircaseCrossTensorVirtualOperation_smul A B hA hB
        hATI hBTI hAB hposA hposB hL hK ha0 haw hbh hxw hyh }
    (staircaseCrossTensorVirtualOperation_one A B hA hB hATI hBTI hAB
      hposA hposB hL hK ha0 haw hbh hxw hyh)
    (staircaseCrossTensorVirtualOperation_mul A B hA hB hATI hBTI hAB
      hposA hposB hL hK ha0 haw hbh hxw hyh)

end StaircaseAlgebra
end TNLean.PEPS
