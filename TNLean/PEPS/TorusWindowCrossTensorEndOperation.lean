/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.NormalSquareInjectivity
import TNLean.PEPS.TorusWindowChain6
import TNLean.PEPS.TorusWindowPeeling.EndPhysicalOperation
import TNLean.PEPS.TorusWindowVirtualOperationFamily

/-!
# The cross-tensor end operation on a staircase edge

Fix a virtual matrix `X` for a tensor `A`, and realize it by the physical operations on the
staircase windows.  If a tensor `B` generates the same closed state, those same physical
operations give one common family on the genuine `B` window tensors.  The paper next compares the
two end windows with open boundaries and uses their injectivity to extract one unique virtual
matrix on the highlighted bond of `B`.

This file formalizes exactly that extraction.  It does not compare the two virtual matrices, prove
a multiplication law for their assignment, identify the bond dimensions of `A` and `B`, or
construct a gauge.

**Scope restriction (displayed horizontal staircase):** The result is stated for the
non-wrapping horizontal staircase coordinates supported by the present boundary-geometry API.
The rotation/translation assembly needed for the full two-dimensional corollary is recorded in
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Lemma 5 at lines 2045--2252 and the
  two-dimensional open-boundary and end-window comparison at lines 2368--2444 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964).
-/

namespace TNLean
namespace PEPS

section Torus

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (1 < width)] [Fact (1 < height)]
variable {d L K : ℕ}

private noncomputable def regionPhysicalOperationCongr
    {R S : Finset (TorusVertex width height)} (h : R = S)
    (O : Module.End ℂ
      (RegionPhysicalConfig (V := TorusVertex width height) (d := d) R → ℂ)) :
    Module.End ℂ
      (RegionPhysicalConfig (V := TorusVertex width height) (d := d) S → ℂ) := by
  subst S
  exact O

private noncomputable def regionInsertCongr
    (B : Tensor (torusGraph width height) d)
    {R S : Finset (TorusVertex width height)} (h : R = S)
    (C : RegionInsert (G := torusGraph width height) (d := d) B R) :
    RegionInsert (G := torusGraph width height) (d := d) B S := by
  subst S
  exact C

private theorem regionInsertOfPhysicalOp_congr
    (B : Tensor (torusGraph width height) d)
    {R S : Finset (TorusVertex width height)} (h : R = S)
    (O : Module.End ℂ
      (RegionPhysicalConfig (V := TorusVertex width height) (d := d) R → ℂ)) :
    regionInsertCongr B h (regionInsertOfPhysicalOp (G := torusGraph width height) B R O) =
      regionInsertOfPhysicalOp (G := torusGraph width height) B S
        (regionPhysicalOperationCongr h O) := by
  subst S
  rfl

private theorem extendInsert_congr_region
    (B : Tensor (torusGraph width height) d)
    {R S P : Finset (TorusVertex width height)} (h : R = S)
    (hRP : R ⊆ P) (hSP : S ⊆ P)
    (C : RegionInsert (G := torusGraph width height) (d := d) B R) :
    extendInsert (G := torusGraph width height) hRP C =
      extendInsert (G := torusGraph width height) hSP (regionInsertCongr B h C) := by
  subst S
  rfl

/-- The paper's left end operation `O₁` for the staircase family of `A`.

The last staircase window is the left end window, whose right boundary contains the highlighted
edge.  The canonical physical realization of `X` on that window is therefore the operation named
`O₁` in Lemma 5.

Source: arXiv:1804.04964, Lemma 5 at lines 2045--2129 and the staircase windows at lines
2320--2415 of `Papers/1804.04964/paper_normal.tex`. -/
noncomputable def staircaseO1PhysicalOp (A : Tensor (torusGraph width height) d) {a b : ℕ}
    (hA : NormalTorusArcWindowInjectivityHypotheses L K
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hL : 0 < L) (hK : 0 < K) (haw : a + 2 * L ≤ width) (hyh : 2 * K ≤ height)
    (X : Matrix
      (Fin (A.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K)))
      (Fin (A.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K))) ℂ) :
    Module.End ℂ
      (RegionPhysicalConfig (V := TorusVertex width height) (d := d)
        (horizontalStaircaseLeftWindow
          ((a : ZMod width), (b : ZMod height)) L K) → ℂ) :=
  regionPhysicalOperationCongr
    (staircaseWindow_last ((a : ZMod width), (b : ZMod height)) hL hK)
    (staircaseVirtualOperationPhysicalOp (B := A) hA hL hK haw hyh X (L + K - 1))

/-- The paper's right end operation `O₃` for the staircase family of `A`.

The first staircase window is the right end window, whose left boundary contains the highlighted
edge.  Its canonical physical realization is the underlying operation `O₃`; the extracted
relation is read in the paper's `O₃ᵀ` orientation.

Source: arXiv:1804.04964, Lemma 5 at lines 2045--2129 and the staircase windows at lines
2320--2415 of `Papers/1804.04964/paper_normal.tex`. -/
noncomputable def staircaseO3PhysicalOp (A : Tensor (torusGraph width height) d) {a b : ℕ}
    (hA : NormalTorusArcWindowInjectivityHypotheses L K
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hL : 0 < L) (hK : 0 < K) (haw : a + 2 * L ≤ width) (hyh : 2 * K ≤ height)
    (X : Matrix
      (Fin (A.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K)))
      (Fin (A.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K))) ℂ) :
    Module.End ℂ
      (RegionPhysicalConfig (V := TorusVertex width height) (d := d)
        (horizontalStaircaseRightWindow
          ((a : ZMod width), (b : ZMod height)) L K) → ℂ) :=
  regionPhysicalOperationCongr
    (staircaseWindow_zero ((a : ZMod width), (b : ZMod height)) L K)
    (staircaseVirtualOperationPhysicalOp (B := A) hA hL hK haw hyh X 0)

/-- **The virtual operation on `B` extracted from the staircase operations of `A`.**

Let `A` and `B` be translation-invariant tensors with the same closed state and with every cyclic
`L × K` window injective.  Apply the canonical physical operations `Oⱼᴬ(X)` to the genuine
window tensors of `B`.  Their common transformed state gives, by the paper's consecutive-window
and corner-completion argument, an equality of the two open end-window inserts.  Injectivity of
those two genuine `B` windows then extracts a unique matrix `Y` on the highlighted bond of
`B` such that the left operation `O₁ᴬ(X)` realizes `Y`, while the right operation `O₃ᴬ(X)`
realizes `Y` in the paper's transposed `O₃ᵀ` orientation.

No equality between the bond dimensions of `A` and `B` is assumed or concluded.  This theorem
does not compare `X` and `Y`, nor does it assert that the assignment `X ↦ Y` is multiplicative.

Source: arXiv:1804.04964, the common open-boundary family at lines 2368--2415, the end-window
comparison at lines 2415--2444, and the two-end extraction of Lemma 5 at lines 2213--2252 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem existsUnique_crossTensorVirtualOperation_of_staircasePhysicalOp_sameState
    (A B : Tensor (torusGraph width height) d) {a b : ℕ}
    (hA : NormalTorusArcWindowInjectivityHypotheses L K
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hB : NormalTorusArcWindowInjectivityHypotheses L K
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hATI : IsTorusTranslationInvariant A) (hBTI : IsTorusTranslationInvariant B)
    (hAB : SameState A B)
    (hposA : ∀ e : Edge (torusGraph width height), 0 < A.bondDim e)
    (hposB : ∀ e : Edge (torusGraph width height), 0 < B.bondDim e)
    (hL : 2 ≤ L) (hK : 2 ≤ K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (hxw : 2 * L + 1 ≤ width) (hyh : 2 * K + 1 ≤ height)
    (X : Matrix
      (Fin (A.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K)))
      (Fin (A.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K))) ℂ) :
    let s : TorusVertex width height := ((a : ZMod width), (b : ZMod height))
    let Wleft := horizontalStaircaseLeftWindow s L K
    let Wright := horizontalStaircaseRightWindow s L K
    let Eleft := horizontalStaircaseLeftWindowBoundaryConfigEquiv B
      (by omega) (by omega) ha0 haw hbh
    let Eright := horizontalStaircaseRightWindowBoundaryConfigEquiv B
      (by omega) (by omega) ha0 haw hbh
    ∃! Y : Matrix
        (Fin (B.bondDim (horizontalStaircaseReferenceEdge s L K)))
        (Fin (B.bondDim (horizontalStaircaseReferenceEdge s L K))) ℂ,
      (∀ etaLeft : HorizontalStaircaseLeftExternalBoundaryConfig B (L := L) (K := K) s,
        IsO1VirtualOperation
          (fun k : Fin (B.bondDim (horizontalStaircaseReferenceEdge s L K)) ↦
            regionBlockedWeight (G := torusGraph width height) B Wleft
              (Eleft.symm (k, etaLeft)))
          (staircaseO1PhysicalOp A hA (by omega) (by omega) haw (by omega) X) Y) ∧
      ∀ etaRight : HorizontalStaircaseRightExternalBoundaryConfig B (L := L) (K := K) s,
        IsO3TransposeVirtualOperation
          (fun k : Fin (B.bondDim (horizontalStaircaseReferenceEdge s L K)) ↦
            regionBlockedWeight (G := torusGraph width height) B Wright
              (Eright.symm (k, etaRight)))
          (staircaseO3PhysicalOp A hA (by omega) (by omega) haw (by omega) X) Y := by
  classical
  dsimp only
  let s : TorusVertex width height := ((a : ZMod width), (b : ZMod height))
  let O₁ := staircaseO1PhysicalOp A hA (by omega) (by omega) haw (by omega) X
  let O₃ := staircaseO3PhysicalOp A hA (by omega) (by omega) haw (by omega) X
  let C : ∀ j, RegionInsert (G := torusGraph width height) (d := d) B
      (staircaseWindow s L K j) :=
    fun j ↦ regionInsertOfPhysicalOp (G := torusGraph width height) B
      (staircaseWindow s L K j)
      (staircaseVirtualOperationPhysicalOp (B := A) hA
        (by omega) (by omega) haw (by omega) X j)
  let common := deformedRegionStateAssembled (G := torusGraph width height) B
    (staircaseWindow s L K 0) (C 0)
  have hagree : ∀ j, j < L + K →
      deformedRegionStateAssembled (G := torusGraph width height) B
        (staircaseWindow s L K j) (C j) = common := by
    intro j _
    exact deformedRegionStateAssembled_staircasePhysicalOp_sameState
      (L := L) (K := K) (a := a) (b := b) (j := j) (j' := 0)
      hA hATI hBTI hAB hposA (by omega) (by omega) haw (by omega) X
  have hUB : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) B) :=
    regionInjectivityUnionClosure_of_overlap B hposB
  have hend := staircasePair_insert_eq_open hB hUB hposB hL hK hxw hyh s C common hagree
  have hleftInjective : RegionBlockedTensorInjective (G := torusGraph width height) B
      (horizontalStaircaseLeftWindow s L K) := by
    have hi := hB.horizontalStaircaseLeftWindow_injective s
    rwa [regionInjectivityDataOf_isInjective] at hi
  have hrightInjective : RegionBlockedTensorInjective (G := torusGraph width height) B
      (horizontalStaircaseRightWindow s L K) := by
    have hi := hB.horizontalStaircaseRightWindow_injective s
    rwa [regionInjectivityDataOf_isInjective] at hi
  have hLpos : 0 < L := by omega
  have hKpos : 0 < K := by omega
  have hlast := staircaseWindow_last s hLpos hKpos
  have hzero := staircaseWindow_zero s L K
  have hCleft :
      regionInsertCongr B hlast (C (L + K - 1)) =
        regionInsertOfPhysicalOp (G := torusGraph width height) B
          (horizontalStaircaseLeftWindow s L K) O₁ := by
    simpa only [C, O₁, s, staircaseO1PhysicalOp] using
      regionInsertOfPhysicalOp_congr B hlast
        (staircaseVirtualOperationPhysicalOp (B := A) hA hLpos hKpos haw (by omega) X
          (L + K - 1))
  have hCright :
      regionInsertCongr B hzero (C 0) =
        regionInsertOfPhysicalOp (G := torusGraph width height) B
          (horizontalStaircaseRightWindow s L K) O₃ := by
    simpa only [C, O₃, s, staircaseO3PhysicalOp] using
      regionInsertOfPhysicalOp_congr B hzero
        (staircaseVirtualOperationPhysicalOp (B := A) hA hLpos hKpos haw (by omega) X 0)
  have heq :
      extendInsert (G := torusGraph width height)
          (horizontalStaircaseLeftWindow_subset_endPair s)
          (fun μ ↦ O₁ (regionBlockedWeight (G := torusGraph width height) B
            (horizontalStaircaseLeftWindow s L K) μ)) =
        extendInsert (G := torusGraph width height)
          (horizontalStaircaseRightWindow_subset_endPair s)
          (fun μ ↦ O₃ (regionBlockedWeight (G := torusGraph width height) B
            (horizontalStaircaseRightWindow s L K) μ)) := by
    calc
      _ = extendInsert (G := torusGraph width height)
          (horizontalStaircaseLeftWindow_subset_endPair s)
          (regionInsertCongr B hlast (C (L + K - 1))) := by
            exact congrArg
              (extendInsert (G := torusGraph width height)
                (horizontalStaircaseLeftWindow_subset_endPair s)) hCleft.symm
      _ = extendInsert (G := torusGraph width height)
          (staircaseWindow_last_subset_endPair hLpos hKpos s) (C (L + K - 1)) :=
            (extendInsert_congr_region B hlast
              (staircaseWindow_last_subset_endPair hLpos hKpos s)
              (horizontalStaircaseLeftWindow_subset_endPair s) (C (L + K - 1))).symm
      _ = extendInsert (G := torusGraph width height)
          (staircaseWindow_zero_subset_endPair s L K) (C 0) := hend.symm
      _ = extendInsert (G := torusGraph width height)
          (horizontalStaircaseRightWindow_subset_endPair s)
          (regionInsertCongr B hzero (C 0)) :=
            extendInsert_congr_region B hzero
              (staircaseWindow_zero_subset_endPair s L K)
              (horizontalStaircaseRightWindow_subset_endPair s) (C 0)
      _ = _ := by
        exact congrArg
          (extendInsert (G := torusGraph width height)
            (horizontalStaircaseRightWindow_subset_endPair s)) hCright
  simpa only [s, O₁, O₃] using
    existsUnique_virtualOperation_of_horizontalStaircaseEndPhysicalOperations
      B hBTI (by omega) (by omega) ha0 haw hbh hposB hleftInjective hrightInjective O₁ O₃ heq

end Torus

end PEPS
end TNLean
