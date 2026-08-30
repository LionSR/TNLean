/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusWindowBondUniform
import TNLean.PEPS.TorusWindowChain5
import TNLean.PEPS.TorusWindowPeeling.BoundaryGeometry

/-!
# Coupling the highlighted staircase end windows

For the two end windows in the two-dimensional proof of the normal PEPS Fundamental Theorem,
the reference edge is their sole common virtual index.  This file identifies the normalized
three-block blue coupling with the genuine blocked tensor of the opposite window.  It also proves
that incompatible external boundary labels give zero and that translation invariance makes the
two end-window normalization factors equal.

These are the boundary-coordinate identities used when the proof compares the first and last
open-boundary expressions, exactly as in Lemma 5.

## Main statements

* `horizontalStaircaseLeftWindow_normalized_threeBlockBlueCoeff_factorization` and its right-end
  counterpart identify the surviving normalized coupling with the genuine opposite-window block.
* `horizontalStaircaseEndWindows_externalCrossingBondProd_eq` identifies the two normalization
  factors for a translation-invariant tensor.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Lemma 5 at lines 2213--2252 and the highlighted
  open-boundary end regions at lines 2415--2444 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964).
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

section CompatibleBoundaryLabels

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
variable {A : Tensor G d}

private noncomputable def compatibleBoundaryVirtualConfig (R S : Finset V)
    (μ : RegionBoundaryConfig (G := G) A R)
    (ν : RegionBoundaryConfig (G := G) A S)
    (hpos : ∀ eg : Edge G, 0 < A.bondDim eg) : VirtualConfig A :=
  fun eg =>
    if hR : IsRegionBoundaryEdge (G := G) R eg then μ ⟨eg, hR⟩
    else if hS : IsRegionBoundaryEdge (G := G) S eg then ν ⟨eg, hS⟩
    else ⟨0, hpos eg⟩

omit [Fintype V] in
private theorem compatibleBoundaryVirtualConfig_apply_left (R S : Finset V)
    (μ : RegionBoundaryConfig (G := G) A R)
    (ν : RegionBoundaryConfig (G := G) A S)
    (hpos : ∀ eg : Edge G, 0 < A.bondDim eg)
    (eg : Edge G) (hR : IsRegionBoundaryEdge (G := G) R eg) :
    compatibleBoundaryVirtualConfig (G := G) R S μ ν hpos eg = μ ⟨eg, hR⟩ := by
  rw [compatibleBoundaryVirtualConfig, dite_eq_left hR]

omit [Fintype V] in
private theorem compatibleBoundaryVirtualConfig_apply_right (R S : Finset V)
    (μ : RegionBoundaryConfig (G := G) A R)
    (ν : RegionBoundaryConfig (G := G) A S)
    (hpos : ∀ eg : Edge G, 0 < A.bondDim eg)
    (hcompat : ∀ (eg : Edge G) (hR : IsRegionBoundaryEdge (G := G) R eg)
      (hS : IsRegionBoundaryEdge (G := G) S eg), μ ⟨eg, hR⟩ = ν ⟨eg, hS⟩)
    (eg : Edge G) (hS : IsRegionBoundaryEdge (G := G) S eg) :
    compatibleBoundaryVirtualConfig (G := G) R S μ ν hpos eg = ν ⟨eg, hS⟩ := by
  rw [compatibleBoundaryVirtualConfig]
  by_cases hR : IsRegionBoundaryEdge (G := G) R eg
  · rw [dite_eq_left hR]
    exact hcompat eg hR hS
  · rw [dite_eq_right hR, dite_eq_left hS]

private theorem compatibleBoundaryVirtualConfig_host_label (R S : Finset V)
    (μ : RegionBoundaryConfig (G := G) A R)
    (ν : RegionBoundaryConfig (G := G) A S)
    (hpos : ∀ eg : Edge G, 0 < A.bondDim eg) :
    regionBoundaryLabel (G := G) A (Finset.univ \ R)
        (compatibleBoundaryVirtualConfig (G := G) R S μ ν hpos) =
      regionComplementBoundaryConfig (G := G) A R μ := by
  funext f
  rw [regionBoundaryLabel_apply, regionComplementBoundaryConfig]
  exact compatibleBoundaryVirtualConfig_apply_left R S μ ν hpos f.1
    ((isRegionBoundaryEdge_compl_iff (G := G) R f.1).mp f.2)

private theorem compatibleBoundaryVirtualConfig_complement_label (R S : Finset V)
    (μ : RegionBoundaryConfig (G := G) A R)
    (ν : RegionBoundaryConfig (G := G) A S)
    (hpos : ∀ eg : Edge G, 0 < A.bondDim eg)
    (hcompat : ∀ (eg : Edge G) (hR : IsRegionBoundaryEdge (G := G) R eg)
      (hS : IsRegionBoundaryEdge (G := G) S eg), μ ⟨eg, hR⟩ = ν ⟨eg, hS⟩) :
    regionBoundaryLabel (G := G) A (Finset.univ \ S)
        (compatibleBoundaryVirtualConfig (G := G) R S μ ν hpos) =
      regionComplementBoundaryConfig (G := G) A S ν := by
  funext f
  rw [regionBoundaryLabel_apply, regionComplementBoundaryConfig]
  exact compatibleBoundaryVirtualConfig_apply_right R S μ ν hpos hcompat f.1
    ((isRegionBoundaryEdge_compl_iff (G := G) S f.1).mp f.2)

private theorem boundary_compatible_of_virtualConfig_labels (R S : Finset V)
    (μ : RegionBoundaryConfig (G := G) A R)
    (ν : RegionBoundaryConfig (G := G) A S)
    (q : VirtualConfig A)
    (hhost : regionBoundaryLabel (G := G) A (Finset.univ \ R) q =
      regionComplementBoundaryConfig (G := G) A R μ)
    (hcompl : regionBoundaryLabel (G := G) A (Finset.univ \ S) q =
      regionComplementBoundaryConfig (G := G) A S ν) :
    ∀ (eg : Edge G) (hR : IsRegionBoundaryEdge (G := G) R eg)
      (hS : IsRegionBoundaryEdge (G := G) S eg), μ ⟨eg, hR⟩ = ν ⟨eg, hS⟩ := by
  intro eg hR hS
  have hqR := congrFun hhost (regionBoundaryEdgeToCompl (G := G) R ⟨eg, hR⟩)
  have hqS := congrFun hcompl (regionBoundaryEdgeToCompl (G := G) S ⟨eg, hS⟩)
  rw [regionBoundaryLabel_apply, regionComplementBoundaryConfig_apply_toCompl] at hqR hqS
  exact hqR.symm.trans hqS

end CompatibleBoundaryLabels

section Torus

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (1 < width)] [Fact (1 < height)]
variable {d : ℕ}

/-! ### Compatible external boundary labels -/

private theorem horizontalStaircaseLeft_endPair_boundary_compatible
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (μ : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K))
    (ν : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K))
    (hcompat :
      (horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh μ).2 =
        (horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh ν).1) :
    ∀ (eg : Edge (torusGraph width height))
      (hW : IsRegionBoundaryEdge (G := torusGraph width height)
        (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K) eg)
      (hS : IsRegionBoundaryEdge (G := torusGraph width height)
        (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K) eg),
      μ ⟨eg, hW⟩ = ν ⟨eg, hS⟩ := by
  intro eg hW hS
  let f : HorizontalStaircaseLeftExternalBoundaryEdge (width := width) (height := height)
      (L := L) (K := K) ((a : ZMod width), (b : ZMod height)) := ⟨⟨eg, hS⟩, hW⟩
  have h := congrFun hcompat f
  simpa [f] using h

private theorem horizontalStaircaseRight_endPair_boundary_compatible
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (μ : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K))
    (ν : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K))
    (hcompat :
      (horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh μ).2 =
        (horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh ν).2) :
    ∀ (eg : Edge (torusGraph width height))
      (hW : IsRegionBoundaryEdge (G := torusGraph width height)
        (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K) eg)
      (hS : IsRegionBoundaryEdge (G := torusGraph width height)
        (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K) eg),
      μ ⟨eg, hW⟩ = ν ⟨eg, hS⟩ := by
  intro eg hW hS
  let f : HorizontalStaircaseRightExternalBoundaryEdge (width := width) (height := height)
      (L := L) (K := K) ((a : ZMod width), (b : ZMod height)) := ⟨⟨eg, hS⟩, hW⟩
  have h := congrFun hcompat f
  simpa [f] using h

private theorem compatibleBoundaryVirtualConfig_rightWindow_label
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (hpos : ∀ eg : Edge (torusGraph width height), 0 < A.bondDim eg)
    (μ : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K))
    (ν : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K))
    (hcompat :
      (horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh μ).2 =
        (horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh ν).1) :
    regionBoundaryLabel (G := torusGraph width height) A
        (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K)
        (compatibleBoundaryVirtualConfig (G := torusGraph width height)
          (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
          (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K) μ ν hpos) =
      (horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh).symm
        ((horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh μ).1,
          (horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh ν).2) := by
  let E := horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
  apply E.injective
  rw [E.apply_symm_apply]
  apply Prod.ext
  · simp only [E, horizontalStaircaseRightWindowBoundaryConfigEquiv_fst,
      horizontalStaircaseLeftWindowBoundaryConfigEquiv_fst, regionBoundaryLabel_apply]
    exact compatibleBoundaryVirtualConfig_apply_left _ _ μ ν hpos _
      (isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A
        hL hK ha0 haw hbh)
  · funext f
    simp only [E, horizontalStaircaseRightWindowBoundaryConfigEquiv_snd,
      horizontalStaircaseEndPairBoundaryConfigEquiv_snd, regionBoundaryLabel_apply]
    exact compatibleBoundaryVirtualConfig_apply_right _ _ μ ν hpos
      (horizontalStaircaseLeft_endPair_boundary_compatible A hL hK ha0 haw hbh μ ν hcompat)
      f.1.1 f.1.2

private theorem compatibleBoundaryVirtualConfig_leftWindow_label
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (hpos : ∀ eg : Edge (torusGraph width height), 0 < A.bondDim eg)
    (μ : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K))
    (ν : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K))
    (hcompat :
      (horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh μ).2 =
        (horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh ν).2) :
    regionBoundaryLabel (G := torusGraph width height) A
        (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
        (compatibleBoundaryVirtualConfig (G := torusGraph width height)
          (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K)
          (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K) μ ν hpos) =
      (horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh).symm
        ((horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh μ).1,
          (horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh ν).1) := by
  let E := horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
  apply E.injective
  rw [E.apply_symm_apply]
  apply Prod.ext
  · simp only [E, horizontalStaircaseLeftWindowBoundaryConfigEquiv_fst,
      horizontalStaircaseRightWindowBoundaryConfigEquiv_fst, regionBoundaryLabel_apply]
    exact compatibleBoundaryVirtualConfig_apply_left _ _ μ ν hpos _
      (isRegionBoundaryEdge_horizontalStaircaseRightWindow_referenceEdge A
        hL hK ha0 haw hbh)
  · funext f
    simp only [E, horizontalStaircaseLeftWindowBoundaryConfigEquiv_snd,
      horizontalStaircaseEndPairBoundaryConfigEquiv_fst, regionBoundaryLabel_apply]
    exact compatibleBoundaryVirtualConfig_apply_right _ _ μ ν hpos
      (horizontalStaircaseRight_endPair_boundary_compatible A hL hK ha0 haw hbh μ ν hcompat)
      f.1.1 f.1.2

/-! ### The common external-boundary normalization of the two end windows

For either end window, the red/exterior crossing edges in the nested three-block geometry are
precisely the window boundary edges other than the reference edge `e`.  Translation invariance
makes the full boundary-bond products of the two congruent windows equal, and removing the same
horizontal edge `e` from both products leaves one common crossing-bond normalization. -/

/-- In the nested geometry whose red block is the left end window, the red/exterior crossing
edges are exactly the left-window boundary edges other than the reference edge.

Source: arXiv:1804.04964, the two highlighted open-boundary end regions at lines 2415--2444 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem horizontalStaircaseLeftWindow_isExternalCrossingEdge_iff
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (eg : Edge (torusGraph width height)) :
    let g := nestedThreeBlockGeometry (V := TorusVertex width height)
      (horizontalStaircaseLeftWindow_subset_endPair
        ((a : ZMod width), (b : ZMod height)) (L := L) (K := K))
    g.swapBlueComplement.IsBlueRedCrossingEdge A eg ↔
      IsRegionBoundaryEdge (G := torusGraph width height)
          (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K) eg ∧
        eg ≠ horizontalStaircaseReferenceEdge
          ((a : ZMod width), (b : ZMod height)) L K := by
  dsimp only
  change (IsRegionBoundaryEdge (G := torusGraph width height)
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K) eg ∧
    IsRegionBoundaryEdge (G := torusGraph width height)
      (Finset.univ \ horizontalStaircaseEndPair
        ((a : ZMod width), (b : ZMod height)) L K) eg) ↔ _
  rw [isRegionBoundaryEdge_compl_iff]
  constructor
  · rintro ⟨hleft, hpair⟩
    exact ⟨hleft,
      ne_referenceEdge_of_isRegionBoundaryEdge_endPair hL hK ha0 haw hbh hpair⟩
  · rintro ⟨hleft, hne⟩
    exact ⟨hleft,
      isRegionBoundaryEdge_endPair_of_leftWindow A hL hK ha0 haw hbh hleft hne⟩

/-- In the nested geometry whose red block is the right end window, the red/exterior crossing
edges are exactly the right-window boundary edges other than the reference edge.

Source: arXiv:1804.04964, the two highlighted open-boundary end regions at lines 2415--2444 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem horizontalStaircaseRightWindow_isExternalCrossingEdge_iff
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (eg : Edge (torusGraph width height)) :
    let g := nestedThreeBlockGeometry (V := TorusVertex width height)
      (horizontalStaircaseRightWindow_subset_endPair
        ((a : ZMod width), (b : ZMod height)) (L := L) (K := K))
    g.swapBlueComplement.IsBlueRedCrossingEdge A eg ↔
      IsRegionBoundaryEdge (G := torusGraph width height)
          (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K) eg ∧
        eg ≠ horizontalStaircaseReferenceEdge
          ((a : ZMod width), (b : ZMod height)) L K := by
  dsimp only
  change (IsRegionBoundaryEdge (G := torusGraph width height)
      (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K) eg ∧
    IsRegionBoundaryEdge (G := torusGraph width height)
      (Finset.univ \ horizontalStaircaseEndPair
        ((a : ZMod width), (b : ZMod height)) L K) eg) ↔ _
  rw [isRegionBoundaryEdge_compl_iff]
  constructor
  · rintro ⟨hright, hpair⟩
    exact ⟨hright,
      ne_referenceEdge_of_isRegionBoundaryEdge_endPair hL hK ha0 haw hbh hpair⟩
  · rintro ⟨hright, hne⟩
    exact ⟨hright,
      isRegionBoundaryEdge_endPair_of_rightWindow A hL hK ha0 haw hbh hright hne⟩

/-- **The two end-window blue-coupling normalizations agree.**

For each end window the crossing product is the bond-dimension product over its external legs,
namely its full boundary with the common reference edge removed.  The two end windows are
translates of the same `L × K` rectangle, so translation invariance makes their interior-bond
products equal.  Splitting the product over every torus edge into boundary and non-boundary parts
then makes their full boundary products equal; removing the same positive reference-edge factor
gives the displayed equality.

Source: arXiv:1804.04964, the translation-invariant corollary at lines 2296--2318 and its two
highlighted open-boundary end regions at lines 2415--2444 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem horizontalStaircaseEndWindows_externalCrossingBondProd_eq
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hTI : IsTorusTranslationInvariant A)
    (hpos : ∀ eg : Edge (torusGraph width height), 0 < A.bondDim eg)
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height) :
    let gleft := nestedThreeBlockGeometry (V := TorusVertex width height)
      (horizontalStaircaseLeftWindow_subset_endPair
        ((a : ZMod width), (b : ZMod height)) (L := L) (K := K))
    let gright := nestedThreeBlockGeometry (V := TorusVertex width height)
      (horizontalStaircaseRightWindow_subset_endPair
        ((a : ZMod width), (b : ZMod height)) (L := L) (K := K))
    gleft.swapBlueComplement.blueRedCrossingBondProd A =
      gright.swapBlueComplement.blueRedCrossingBondProd A := by
  dsimp only
  let s : TorusVertex width height := ((a : ZMod width), (b : ZMod height))
  let Wleft := horizontalStaircaseLeftWindow s L K
  let Wright := horizontalStaircaseRightWindow s L K
  let e := horizontalStaircaseReferenceEdge s L K
  let gleft := nestedThreeBlockGeometry (V := TorusVertex width height)
    (horizontalStaircaseLeftWindow_subset_endPair (L := L) (K := K) s)
  let gright := nestedThreeBlockGeometry (V := TorusVertex width height)
    (horizontalStaircaseRightWindow_subset_endPair (L := L) (K := K) s)
  let boundaryProd := fun W : Finset (TorusVertex width height) ↦
    ∏ eg ∈ Finset.univ.filter (fun eg : Edge (torusGraph width height) ↦
      IsRegionBoundaryEdge (G := torusGraph width height) W eg), A.bondDim eg
  have hinterior : regionInteriorBondProd (G := torusGraph width height) A Wleft =
      regionInteriorBondProd (G := torusGraph width height) A Wright := by
    exact regionInteriorBondProd_torusArcRectangle_eq hTI _ _ L K
  have hinteriorPos : 0 < regionInteriorBondProd (G := torusGraph width height) A Wleft :=
    regionInteriorBondProd_pos (G := torusGraph width height) A Wleft hpos
  have hboundary : boundaryProd Wleft = boundaryProd Wright := by
    apply Nat.eq_of_mul_eq_mul_right hinteriorPos
    calc
      boundaryProd Wleft * regionInteriorBondProd (G := torusGraph width height) A Wleft =
          ∏ eg : Edge (torusGraph width height), A.bondDim eg := by
        exact Finset.prod_filter_mul_prod_filter_not Finset.univ
          (fun eg : Edge (torusGraph width height) ↦
            IsRegionBoundaryEdge (G := torusGraph width height) Wleft eg) A.bondDim
      _ = boundaryProd Wright *
          regionInteriorBondProd (G := torusGraph width height) A Wright := by
        exact (Finset.prod_filter_mul_prod_filter_not Finset.univ
          (fun eg : Edge (torusGraph width height) ↦
            IsRegionBoundaryEdge (G := torusGraph width height) Wright eg) A.bondDim).symm
      _ = boundaryProd Wright *
          regionInteriorBondProd (G := torusGraph width height) A Wleft := by rw [hinterior]
  have hleftFilter :
      Finset.univ.filter (fun eg : Edge (torusGraph width height) ↦
          gleft.swapBlueComplement.IsBlueRedCrossingEdge A eg) =
        (Finset.univ.filter (fun eg : Edge (torusGraph width height) ↦
          IsRegionBoundaryEdge (G := torusGraph width height) Wleft eg)).erase e := by
    ext eg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    rw [and_comm]
    exact horizontalStaircaseLeftWindow_isExternalCrossingEdge_iff
      A hL hK ha0 haw hbh eg
  have hrightFilter :
      Finset.univ.filter (fun eg : Edge (torusGraph width height) ↦
          gright.swapBlueComplement.IsBlueRedCrossingEdge A eg) =
        (Finset.univ.filter (fun eg : Edge (torusGraph width height) ↦
          IsRegionBoundaryEdge (G := torusGraph width height) Wright eg)).erase e := by
    ext eg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    rw [and_comm]
    exact horizontalStaircaseRightWindow_isExternalCrossingEdge_iff
      A hL hK ha0 haw hbh eg
  have heLeft : e ∈ Finset.univ.filter (fun eg : Edge (torusGraph width height) ↦
      IsRegionBoundaryEdge (G := torusGraph width height) Wleft eg) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge
      A hL hK ha0 haw hbh
  have heRight : e ∈ Finset.univ.filter (fun eg : Edge (torusGraph width height) ↦
      IsRegionBoundaryEdge (G := torusGraph width height) Wright eg) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact isRegionBoundaryEdge_horizontalStaircaseRightWindow_referenceEdge
      A hL hK ha0 haw hbh
  apply Nat.eq_of_mul_eq_mul_right (hpos e)
  calc
    gleft.swapBlueComplement.blueRedCrossingBondProd A * A.bondDim e =
        boundaryProd Wleft := by
      rw [ThreeBlockGeometry.blueRedCrossingBondProd, hleftFilter]
      exact Finset.prod_erase_mul _ _ heLeft
    _ = boundaryProd Wright := hboundary
    _ = gright.swapBlueComplement.blueRedCrossingBondProd A * A.bondDim e := by
      rw [ThreeBlockGeometry.blueRedCrossingBondProd, hrightFilter]
      exact (Finset.prod_erase_mul _ _ heRight).symm

/-- **The left-end blue coupling is the genuine right-window block.**

Suppose the left-window boundary configuration and the end-pair boundary configuration agree on
the left external legs.  In the nested geometry with red block the left window and blue block the
right window, the red/exterior crossing-bond multiple of `threeBlockBlueCoeff` is exactly the
right window's blocked-region weight.  Its boundary data are the reference-edge coordinate of
the left-window configuration and the right external data of the end-pair configuration.

Source: arXiv:1804.04964, the end comparison in Lemma 5 at lines 2213--2252 and the two
highlighted open-boundary regions at lines 2415--2444 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem horizontalStaircaseLeftWindow_threeBlockBlueCoeff_factorization
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (hpos : ∀ eg : Edge (torusGraph width height), 0 < A.bondDim eg)
    (μ : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K))
    (ν : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K))
    (hcompat :
      (horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh μ).2 =
        (horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh ν).1)
    (σright : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
      (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K)) :
    let g := nestedThreeBlockGeometry (V := TorusVertex width height)
      (horizontalStaircaseLeftWindow_subset_endPair
        ((a : ZMod width), (b : ZMod height)) (L := L) (K := K))
    (g.swapBlueComplement.blueRedCrossingBondProd A : ℂ) •
        g.threeBlockBlueCoeff
          (regionComplementBoundaryConfig (G := torusGraph width height) A
            (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K) μ)
          ((regionPhysicalConfigCongr (d := d)
            (horizontalStaircaseEndPair_sdiff_leftWindow (by omega)
              ((a : ZMod width), (b : ZMod height)))).symm σright)
          (regionComplementBoundaryConfig (G := torusGraph width height) A
            (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K) ν) =
      regionBlockedWeight (G := torusGraph width height) A
        (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K)
        ((horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh).symm
          ((horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh μ).1,
            (horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh ν).2))
        σright := by
  dsimp only
  let Wleft := horizontalStaircaseLeftWindow
    ((a : ZMod width), (b : ZMod height)) L K
  let Wright := horizontalStaircaseRightWindow
    ((a : ZMod width), (b : ZMod height)) L K
  let S := horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K
  let hWS : Wleft ⊆ S := horizontalStaircaseLeftWindow_subset_endPair _
  let g := nestedThreeBlockGeometry (V := TorusVertex width height) hWS
  let hblue : g.blue = Wright := horizontalStaircaseEndPair_sdiff_leftWindow (by omega) _
  let q₀ : VirtualConfig A := compatibleBoundaryVirtualConfig (G := torusGraph width height)
    Wleft S μ ν hpos
  have hqhost : regionBoundaryLabel (G := torusGraph width height) A
      (Finset.univ \ g.red) q₀ =
        regionComplementBoundaryConfig (G := torusGraph width height) A Wleft μ := by
    simpa [g, hWS, Wleft, S, q₀, nestedThreeBlockGeometry] using
      compatibleBoundaryVirtualConfig_host_label Wleft S μ ν hpos
  have hqcompl : regionBoundaryLabel (G := torusGraph width height) A g.complement q₀ =
      regionComplementBoundaryConfig (G := torusGraph width height) A S ν := by
    simpa [g, hWS, Wleft, S, q₀, nestedThreeBlockGeometry] using
      compatibleBoundaryVirtualConfig_complement_label Wleft S μ ν hpos
        (horizontalStaircaseLeft_endPair_boundary_compatible A hL hK ha0 haw hbh μ ν hcompat)
  have hfactor := g.crossingBondProd_smul_threeBlockBlueCoeff_eq_regionBlockedWeight
    (A := A)
    (regionComplementBoundaryConfig (G := torusGraph width height) A Wleft μ)
    (regionComplementBoundaryConfig (G := torusGraph width height) A S ν)
    ((regionPhysicalConfigCongr (d := d) hblue).symm σright) q₀ hqhost hqcompl
  change (g.swapBlueComplement.blueRedCrossingBondProd A : ℂ) •
      g.threeBlockBlueCoeff
        (regionComplementBoundaryConfig (G := torusGraph width height) A Wleft μ)
        ((regionPhysicalConfigCongr (d := d) hblue).symm σright)
        (regionComplementBoundaryConfig (G := torusGraph width height) A S ν) =
    regionBlockedWeight (G := torusGraph width height) A Wright
      ((horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh).symm
        ((horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh μ).1,
          (horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh ν).2)) σright
  rw [hfactor]
  rw [regionBlockedWeight_congr (A := A) hblue]
  have hlabel : regionBoundaryConfigCongr (A := A) hblue
      (regionBoundaryLabel (G := torusGraph width height) A g.blue q₀) =
      regionBoundaryLabel (G := torusGraph width height) A Wright q₀ := by
    funext f
    rfl
  rw [hlabel, Equiv.apply_symm_apply]
  rw [compatibleBoundaryVirtualConfig_rightWindow_label A hL hK ha0 haw hbh hpos μ ν hcompat]

/-- If the left-window and end-pair boundary configurations disagree on a left external leg,
then the corresponding blue coupling is zero: no global virtual configuration can carry both
prescribed boundary labels.

Source: arXiv:1804.04964, the two highlighted open-boundary regions at lines 2415--2444 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem horizontalStaircaseLeftWindow_threeBlockBlueCoeff_eq_zero_of_external_ne
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (μ : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K))
    (ν : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K))
    (hne :
      (horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh μ).2 ≠
        (horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh ν).1)
    (σblue : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
      ((horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K) \
        horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)) :
    let g := nestedThreeBlockGeometry (V := TorusVertex width height)
      (horizontalStaircaseLeftWindow_subset_endPair
        ((a : ZMod width), (b : ZMod height)) (L := L) (K := K))
    g.threeBlockBlueCoeff
        (regionComplementBoundaryConfig (G := torusGraph width height) A
          (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K) μ)
        σblue
        (regionComplementBoundaryConfig (G := torusGraph width height) A
          (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K) ν) = 0 := by
  dsimp only
  let Wleft := horizontalStaircaseLeftWindow
    ((a : ZMod width), (b : ZMod height)) L K
  let S := horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K
  let hWS : Wleft ⊆ S := horizontalStaircaseLeftWindow_subset_endPair _
  let g := nestedThreeBlockGeometry (V := TorusVertex width height) hWS
  change g.threeBlockBlueCoeff
      (regionComplementBoundaryConfig (G := torusGraph width height) A Wleft μ) σblue
      (regionComplementBoundaryConfig (G := torusGraph width height) A S ν) = 0
  apply g.threeBlockBlueCoeff_eq_zero_of_no_compatible_boundary
  rintro ⟨q, hqhost, hqcompl⟩
  apply hne
  funext f
  have hcompat := boundary_compatible_of_virtualConfig_labels Wleft S μ ν q
    (by simpa [g, hWS, Wleft, S, nestedThreeBlockGeometry] using hqhost)
    (by simpa [g, hWS, Wleft, S, nestedThreeBlockGeometry] using hqcompl)
    f.1.1 f.2 f.1.2
  simpa using hcompat

/-- **Normalized left-end blue coupling.**

After the normalization appearing in `extendInsert`, the blue coupling for the left end window
vanishes unless its external boundary data agree with the left part of the end-pair boundary.
In the surviving case it is the genuine right-window blocked weight at the same reference-edge
coordinate and the right external data, multiplied by the inverse product of the exterior
interior-bond factor and the left external crossing-bond factor.

Source: arXiv:1804.04964, the end comparison in Lemma 5 at lines 2213--2252 and the two
highlighted open-boundary regions at lines 2415--2444 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem horizontalStaircaseLeftWindow_normalized_threeBlockBlueCoeff_factorization
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (hpos : ∀ eg : Edge (torusGraph width height), 0 < A.bondDim eg)
    (mu : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K))
    (nu : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K))
    (sigmaRight : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
      (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K)) :
    let S := horizontalStaircaseEndPair
      ((a : ZMod width), (b : ZMod height)) L K
    let g := nestedThreeBlockGeometry (V := TorusVertex width height)
      (horizontalStaircaseLeftWindow_subset_endPair
        ((a : ZMod width), (b : ZMod height)) (L := L) (K := K))
    (regionInteriorBondProd (G := torusGraph width height) A (Finset.univ \ S) : ℂ)⁻¹ *
        g.threeBlockBlueCoeff
          (regionComplementBoundaryConfig (G := torusGraph width height) A
            (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K) mu)
          ((regionPhysicalConfigCongr (d := d)
            (horizontalStaircaseEndPair_sdiff_leftWindow (by omega)
              ((a : ZMod width), (b : ZMod height)))).symm sigmaRight)
          (regionComplementBoundaryConfig (G := torusGraph width height) A S nu) =
      if _hcompat :
          (horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh mu).2 =
            (horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh nu).1
        then
          ((regionInteriorBondProd (G := torusGraph width height) A
              (Finset.univ \ S) : ℂ) *
            (g.swapBlueComplement.blueRedCrossingBondProd A : ℂ))⁻¹ *
            regionBlockedWeight (G := torusGraph width height) A
              (horizontalStaircaseRightWindow
                ((a : ZMod width), (b : ZMod height)) L K)
              ((horizontalStaircaseRightWindowBoundaryConfigEquiv
                A hL hK ha0 haw hbh).symm
                ((horizontalStaircaseLeftWindowBoundaryConfigEquiv
                  A hL hK ha0 haw hbh mu).1,
                  (horizontalStaircaseEndPairBoundaryConfigEquiv
                    A hL hK ha0 haw hbh nu).2)) sigmaRight
        else 0 := by
  dsimp only
  let S := horizontalStaircaseEndPair
    ((a : ZMod width), (b : ZMod height)) L K
  let hWS := horizontalStaircaseLeftWindow_subset_endPair
    ((a : ZMod width), (b : ZMod height)) (L := L) (K := K)
  let g := nestedThreeBlockGeometry (V := TorusVertex width height) hWS
  let coeff := g.threeBlockBlueCoeff
    (regionComplementBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K) mu)
    ((regionPhysicalConfigCongr (d := d)
      (horizontalStaircaseEndPair_sdiff_leftWindow (by omega)
        ((a : ZMod width), (b : ZMod height)))).symm sigmaRight)
    (regionComplementBoundaryConfig (G := torusGraph width height) A S nu)
  let weight := regionBlockedWeight (G := torusGraph width height) A
    (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K)
    ((horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh).symm
      ((horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh mu).1,
        (horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh nu).2)) sigmaRight
  change (regionInteriorBondProd (G := torusGraph width height) A (Finset.univ \ S) : ℂ)⁻¹ *
      coeff = if hcompat : _ then
        ((regionInteriorBondProd (G := torusGraph width height) A
            (Finset.univ \ S) : ℂ) *
          (g.swapBlueComplement.blueRedCrossingBondProd A : ℂ))⁻¹ * weight else 0
  by_cases hcompat :
      (horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh mu).2 =
        (horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh nu).1
  · rw [dite_eq_left hcompat]
    have hfactor := horizontalStaircaseLeftWindow_threeBlockBlueCoeff_factorization
      A hL hK ha0 haw hbh hpos mu nu hcompat sigmaRight
    dsimp only at hfactor
    change (g.swapBlueComplement.blueRedCrossingBondProd A : ℂ) *
      coeff = weight at hfactor
    have houter :
        (regionInteriorBondProd (G := torusGraph width height) A
          (Finset.univ \ S) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr
        (regionInteriorBondProd_pos (G := torusGraph width height) A
          (Finset.univ \ S) hpos).ne'
    have hcrossPos : 0 < g.swapBlueComplement.blueRedCrossingBondProd A := by
      rw [ThreeBlockGeometry.blueRedCrossingBondProd]
      exact Finset.prod_pos (fun eg _ ↦ hpos eg)
    have hcross : (g.swapBlueComplement.blueRedCrossingBondProd A : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr hcrossPos.ne'
    calc
      _ = ((regionInteriorBondProd (G := torusGraph width height) A
              (Finset.univ \ S) : ℂ) *
            (g.swapBlueComplement.blueRedCrossingBondProd A : ℂ))⁻¹ *
          ((g.swapBlueComplement.blueRedCrossingBondProd A : ℂ) *
            coeff) := by
        rw [mul_inv_rev]
        field_simp
      _ = _ := by rw [hfactor]
  · rw [dite_eq_right hcompat]
    have hzero := horizontalStaircaseLeftWindow_threeBlockBlueCoeff_eq_zero_of_external_ne
      A hL hK ha0 haw hbh mu nu hcompat
        ((regionPhysicalConfigCongr (d := d)
          (horizontalStaircaseEndPair_sdiff_leftWindow (by omega)
            ((a : ZMod width), (b : ZMod height)))).symm sigmaRight)
    dsimp only at hzero
    change coeff = 0 at hzero
    rw [hzero, mul_zero]

/-- **The right-end blue coupling is the genuine left-window block.**

Suppose the right-window boundary configuration and the end-pair boundary configuration agree on
the right external legs.  In the nested geometry with red block the right window and blue block
the left window, the red/exterior crossing-bond multiple of `threeBlockBlueCoeff` is exactly the
left window's blocked-region weight.  Its boundary data are the reference-edge coordinate of the
right-window configuration and the left external data of the end-pair configuration.

Source: arXiv:1804.04964, the end comparison in Lemma 5 at lines 2213--2252 and the two
highlighted open-boundary regions at lines 2415--2444 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem horizontalStaircaseRightWindow_threeBlockBlueCoeff_factorization
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (hpos : ∀ eg : Edge (torusGraph width height), 0 < A.bondDim eg)
    (μ : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K))
    (ν : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K))
    (hcompat :
      (horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh μ).2 =
        (horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh ν).2)
    (σleft : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)) :
    let g := nestedThreeBlockGeometry (V := TorusVertex width height)
      (horizontalStaircaseRightWindow_subset_endPair
        ((a : ZMod width), (b : ZMod height)) (L := L) (K := K))
    (g.swapBlueComplement.blueRedCrossingBondProd A : ℂ) •
        g.threeBlockBlueCoeff
          (regionComplementBoundaryConfig (G := torusGraph width height) A
            (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K) μ)
          ((regionPhysicalConfigCongr (d := d)
            (horizontalStaircaseEndPair_sdiff_rightWindow (by omega)
              ((a : ZMod width), (b : ZMod height)))).symm σleft)
          (regionComplementBoundaryConfig (G := torusGraph width height) A
            (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K) ν) =
      regionBlockedWeight (G := torusGraph width height) A
        (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
        ((horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh).symm
          ((horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh μ).1,
            (horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh ν).1))
        σleft := by
  dsimp only
  let Wright := horizontalStaircaseRightWindow
    ((a : ZMod width), (b : ZMod height)) L K
  let Wleft := horizontalStaircaseLeftWindow
    ((a : ZMod width), (b : ZMod height)) L K
  let S := horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K
  let hWS : Wright ⊆ S := horizontalStaircaseRightWindow_subset_endPair _
  let g := nestedThreeBlockGeometry (V := TorusVertex width height) hWS
  let hblue : g.blue = Wleft := horizontalStaircaseEndPair_sdiff_rightWindow (by omega) _
  let q₀ : VirtualConfig A := compatibleBoundaryVirtualConfig (G := torusGraph width height)
    Wright S μ ν hpos
  have hqhost : regionBoundaryLabel (G := torusGraph width height) A
      (Finset.univ \ g.red) q₀ =
        regionComplementBoundaryConfig (G := torusGraph width height) A Wright μ := by
    simpa [g, hWS, Wright, S, q₀, nestedThreeBlockGeometry] using
      compatibleBoundaryVirtualConfig_host_label Wright S μ ν hpos
  have hqcompl : regionBoundaryLabel (G := torusGraph width height) A g.complement q₀ =
      regionComplementBoundaryConfig (G := torusGraph width height) A S ν := by
    simpa [g, hWS, Wright, S, q₀, nestedThreeBlockGeometry] using
      compatibleBoundaryVirtualConfig_complement_label Wright S μ ν hpos
        (horizontalStaircaseRight_endPair_boundary_compatible A hL hK ha0 haw hbh μ ν hcompat)
  have hfactor := g.crossingBondProd_smul_threeBlockBlueCoeff_eq_regionBlockedWeight
    (A := A)
    (regionComplementBoundaryConfig (G := torusGraph width height) A Wright μ)
    (regionComplementBoundaryConfig (G := torusGraph width height) A S ν)
    ((regionPhysicalConfigCongr (d := d) hblue).symm σleft) q₀ hqhost hqcompl
  change (g.swapBlueComplement.blueRedCrossingBondProd A : ℂ) •
      g.threeBlockBlueCoeff
        (regionComplementBoundaryConfig (G := torusGraph width height) A Wright μ)
        ((regionPhysicalConfigCongr (d := d) hblue).symm σleft)
        (regionComplementBoundaryConfig (G := torusGraph width height) A S ν) =
    regionBlockedWeight (G := torusGraph width height) A Wleft
      ((horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh).symm
        ((horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh μ).1,
          (horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh ν).1)) σleft
  rw [hfactor]
  rw [regionBlockedWeight_congr (A := A) hblue]
  have hlabel : regionBoundaryConfigCongr (A := A) hblue
      (regionBoundaryLabel (G := torusGraph width height) A g.blue q₀) =
      regionBoundaryLabel (G := torusGraph width height) A Wleft q₀ := by
    funext f
    rfl
  rw [hlabel, Equiv.apply_symm_apply]
  rw [compatibleBoundaryVirtualConfig_leftWindow_label A hL hK ha0 haw hbh hpos μ ν hcompat]

/-- If the right-window and end-pair boundary configurations disagree on a right external leg,
then the corresponding blue coupling is zero.

Source: arXiv:1804.04964, the two highlighted open-boundary regions at lines 2415--2444 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem horizontalStaircaseRightWindow_threeBlockBlueCoeff_eq_zero_of_external_ne
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (μ : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K))
    (ν : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K))
    (hne :
      (horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh μ).2 ≠
        (horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh ν).2)
    (σblue : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
      ((horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K) \
        horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K)) :
    let g := nestedThreeBlockGeometry (V := TorusVertex width height)
      (horizontalStaircaseRightWindow_subset_endPair
        ((a : ZMod width), (b : ZMod height)) (L := L) (K := K))
    g.threeBlockBlueCoeff
        (regionComplementBoundaryConfig (G := torusGraph width height) A
          (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K) μ)
        σblue
        (regionComplementBoundaryConfig (G := torusGraph width height) A
          (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K) ν) = 0 := by
  dsimp only
  let Wright := horizontalStaircaseRightWindow
    ((a : ZMod width), (b : ZMod height)) L K
  let S := horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K
  let hWS : Wright ⊆ S := horizontalStaircaseRightWindow_subset_endPair _
  let g := nestedThreeBlockGeometry (V := TorusVertex width height) hWS
  change g.threeBlockBlueCoeff
      (regionComplementBoundaryConfig (G := torusGraph width height) A Wright μ) σblue
      (regionComplementBoundaryConfig (G := torusGraph width height) A S ν) = 0
  apply g.threeBlockBlueCoeff_eq_zero_of_no_compatible_boundary
  rintro ⟨q, hqhost, hqcompl⟩
  apply hne
  funext f
  have hcompat := boundary_compatible_of_virtualConfig_labels Wright S μ ν q
    (by simpa [g, hWS, Wright, S, nestedThreeBlockGeometry] using hqhost)
    (by simpa [g, hWS, Wright, S, nestedThreeBlockGeometry] using hqcompl)
    f.1.1 f.2 f.1.2
  simpa using hcompat

/-- **Normalized right-end blue coupling.**

After the normalization appearing in `extendInsert`, the blue coupling for the right end window
vanishes unless its external boundary data agree with the right part of the end-pair boundary.
In the surviving case it is the genuine left-window blocked weight at the same reference-edge
coordinate and the left external data, multiplied by the inverse product of the exterior
interior-bond factor and the right external crossing-bond factor.

Source: arXiv:1804.04964, the end comparison in Lemma 5 at lines 2213--2252 and the two
highlighted open-boundary regions at lines 2415--2444 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem horizontalStaircaseRightWindow_normalized_threeBlockBlueCoeff_factorization
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (hpos : ∀ eg : Edge (torusGraph width height), 0 < A.bondDim eg)
    (mu : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K))
    (nu : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K))
    (sigmaLeft : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)) :
    let S := horizontalStaircaseEndPair
      ((a : ZMod width), (b : ZMod height)) L K
    let g := nestedThreeBlockGeometry (V := TorusVertex width height)
      (horizontalStaircaseRightWindow_subset_endPair
        ((a : ZMod width), (b : ZMod height)) (L := L) (K := K))
    (regionInteriorBondProd (G := torusGraph width height) A (Finset.univ \ S) : ℂ)⁻¹ *
        g.threeBlockBlueCoeff
          (regionComplementBoundaryConfig (G := torusGraph width height) A
            (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K) mu)
          ((regionPhysicalConfigCongr (d := d)
            (horizontalStaircaseEndPair_sdiff_rightWindow (by omega)
              ((a : ZMod width), (b : ZMod height)))).symm sigmaLeft)
          (regionComplementBoundaryConfig (G := torusGraph width height) A S nu) =
      if _hcompat :
          (horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh mu).2 =
            (horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh nu).2
        then
          ((regionInteriorBondProd (G := torusGraph width height) A
              (Finset.univ \ S) : ℂ) *
            (g.swapBlueComplement.blueRedCrossingBondProd A : ℂ))⁻¹ *
            regionBlockedWeight (G := torusGraph width height) A
              (horizontalStaircaseLeftWindow
                ((a : ZMod width), (b : ZMod height)) L K)
              ((horizontalStaircaseLeftWindowBoundaryConfigEquiv
                A hL hK ha0 haw hbh).symm
                ((horizontalStaircaseRightWindowBoundaryConfigEquiv
                  A hL hK ha0 haw hbh mu).1,
                  (horizontalStaircaseEndPairBoundaryConfigEquiv
                    A hL hK ha0 haw hbh nu).1)) sigmaLeft
        else 0 := by
  dsimp only
  let S := horizontalStaircaseEndPair
    ((a : ZMod width), (b : ZMod height)) L K
  let hWS := horizontalStaircaseRightWindow_subset_endPair
    ((a : ZMod width), (b : ZMod height)) (L := L) (K := K)
  let g := nestedThreeBlockGeometry (V := TorusVertex width height) hWS
  let coeff := g.threeBlockBlueCoeff
    (regionComplementBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K) mu)
    ((regionPhysicalConfigCongr (d := d)
      (horizontalStaircaseEndPair_sdiff_rightWindow (by omega)
        ((a : ZMod width), (b : ZMod height)))).symm sigmaLeft)
    (regionComplementBoundaryConfig (G := torusGraph width height) A S nu)
  let weight := regionBlockedWeight (G := torusGraph width height) A
    (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
    ((horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh).symm
      ((horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh mu).1,
        (horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh nu).1)) sigmaLeft
  change (regionInteriorBondProd (G := torusGraph width height) A (Finset.univ \ S) : ℂ)⁻¹ *
      coeff = if hcompat : _ then
        ((regionInteriorBondProd (G := torusGraph width height) A
            (Finset.univ \ S) : ℂ) *
          (g.swapBlueComplement.blueRedCrossingBondProd A : ℂ))⁻¹ * weight else 0
  by_cases hcompat :
      (horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh mu).2 =
        (horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh nu).2
  · rw [dite_eq_left hcompat]
    have hfactor := horizontalStaircaseRightWindow_threeBlockBlueCoeff_factorization
      A hL hK ha0 haw hbh hpos mu nu hcompat sigmaLeft
    dsimp only at hfactor
    change (g.swapBlueComplement.blueRedCrossingBondProd A : ℂ) *
      coeff = weight at hfactor
    have houter :
        (regionInteriorBondProd (G := torusGraph width height) A
          (Finset.univ \ S) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr
        (regionInteriorBondProd_pos (G := torusGraph width height) A
          (Finset.univ \ S) hpos).ne'
    have hcrossPos : 0 < g.swapBlueComplement.blueRedCrossingBondProd A := by
      rw [ThreeBlockGeometry.blueRedCrossingBondProd]
      exact Finset.prod_pos (fun eg _ ↦ hpos eg)
    have hcross : (g.swapBlueComplement.blueRedCrossingBondProd A : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr hcrossPos.ne'
    calc
      _ = ((regionInteriorBondProd (G := torusGraph width height) A
              (Finset.univ \ S) : ℂ) *
            (g.swapBlueComplement.blueRedCrossingBondProd A : ℂ))⁻¹ *
          ((g.swapBlueComplement.blueRedCrossingBondProd A : ℂ) * coeff) := by
        rw [mul_inv_rev]
        field_simp
      _ = _ := by rw [hfactor]
  · rw [dite_eq_right hcompat]
    have hzero := horizontalStaircaseRightWindow_threeBlockBlueCoeff_eq_zero_of_external_ne
      A hL hK ha0 haw hbh mu nu hcompat
        ((regionPhysicalConfigCongr (d := d)
          (horizontalStaircaseEndPair_sdiff_rightWindow (by omega)
            ((a : ZMod width), (b : ZMod height)))).symm sigmaLeft)
    dsimp only at hzero
    change coeff = 0 at hzero
    rw [hzero, mul_zero]

end Torus

end PEPS
end TNLean
