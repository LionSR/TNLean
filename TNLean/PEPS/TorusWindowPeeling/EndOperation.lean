/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusWindowChain2
import TNLean.PEPS.TorusWindowPeeling.BoundaryGeometry
import TNLean.PEPS.TorusWindowPeeling.EndWindowCoupling
import TNLean.PEPS.TwoInjectiveComparison.Basic

/-!
# The Lemma 5 virtual operation on a staircase end pair

The open-boundary equality on the two highlighted staircase end windows is first rewritten as a
contraction over their sole common virtual index, the reference edge.  Injectivity of the two
genuine blocked end-window tensors then gives the unique matrix `X` whose insertion produces both
modified end tensors.  No injectivity is assumed for either modified insert, a single vertex, the
end pair, or its complement.

This is the two-dimensional realization of the ``compare the two ends'' step in Lemma 5.  The
composition laws for the maps from the physical operations to `X` belong to the subsequent
cross-tensor construction.

## Main statements

* `singleBondContraction_eq_of_horizontalStaircaseEndPair_extendInsert_eq` removes the common
  normalization from equal end-pair extensions.
* `existsUnique_virtualOperation_of_horizontalStaircaseEndPair` extracts the unique matrix on the
  highlighted reference edge.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Lemma 5 at lines 2213--2252 and the two-dimensional
  open-boundary comparison at lines 2415--2444 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964).
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

section EndPairAlgebra

private theorem sum_mul_dite_eq_sum_fiber
    {I K X : Type*} [Fintype I] [Fintype K] [Finite X] [DecidableEq X]
    (E : I ≃ K × X) (x : X) (f : I → ℂ) (w : K → ℂ) :
    (∑ i : I, f i * (if _h : (E i).2 = x then w (E i).1 else 0)) =
      ∑ k : K, f (E.symm (k, x)) * w k := by
  classical
  let _ : Fintype X := Fintype.ofFinite X
  rw [← Equiv.sum_comp E.symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun k _ ↦ ?_)
  rw [Finset.sum_eq_single x]
  · simp
  · intro x' _ hx'
    simp only [E.apply_symm_apply]
    rw [dite_eq_right hx']
    exact mul_zero _
  · intro hx
    exact absurd (Finset.mem_univ x) hx

private theorem linearIndependent_shared_of_joint
    {External K Physical : Type*} [Finite K] [Nonempty External]
    (T : External → K → Physical → ℂ)
    (hT : LinearIndependent ℂ
      (fun p : External × K ↦ (T p.1 p.2 : Physical → ℂ))) :
    LinearIndependent ℂ
      (fun k : K ↦ fun p : External × Physical ↦ T p.1 k p.2) := by
  classical
  let _ : Fintype K := Fintype.ofFinite K
  rw [Fintype.linearIndependent_iff]
  intro c hc k₀
  let eta₀ : External := Classical.arbitrary External
  have hjoint := linearIndependent_iff'.1 hT
  let support : Finset (External × K) :=
    {eta₀} ×ˢ (Finset.univ : Finset K)
  have hzero : (∑ p ∈ support, (fun p : External × K ↦ c p.2) p •
      (T p.1 p.2 : Physical → ℂ)) = 0 := by
    funext sigma
    rw [Finset.sum_apply]
    have hcsigma := congrFun hc (eta₀, sigma)
    rw [Finset.sum_apply] at hcsigma
    simp only [Pi.smul_apply, smul_eq_mul] at hcsigma ⊢
    rw [show support = {eta₀} ×ˢ (Finset.univ : Finset K) from rfl,
      Finset.sum_product]
    simp only [Finset.sum_singleton, Pi.zero_apply]
    exact hcsigma
  have hmem : (eta₀, k₀) ∈ support := by
    simp [support]
  simpa using hjoint support (fun p ↦ c p.2) hzero (eta₀, k₀) hmem

end EndPairAlgebra

section Torus

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (1 < width)] [Fact (1 < height)]
variable {d : ℕ}

private def horizontalStaircaseEndPairPhysicalConfig
    {L K : ℕ} (s : TorusVertex width height)
    (sigmaLeft : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
      (horizontalStaircaseLeftWindow s L K))
    (sigmaRight : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
      (horizontalStaircaseRightWindow s L K)) :
    RegionPhysicalConfig (V := TorusVertex width height) (d := d)
      (horizontalStaircaseEndPair s L K) :=
  fun w ↦
    if hleft : w.1 ∈ horizontalStaircaseLeftWindow s L K then
      sigmaLeft ⟨w.1, hleft⟩
    else
      sigmaRight ⟨w.1, by
        have hw : w.1 ∈ horizontalStaircaseLeftWindow s L K ∪
            horizontalStaircaseRightWindow s L K := by
          simpa only [horizontalStaircaseEndPair] using w.2
        exact (Finset.mem_union.mp hw).resolve_left hleft⟩

omit [Fact (1 < width)] [Fact (1 < height)] in
private theorem restrictSubRegionσ_horizontalStaircaseEndPairPhysicalConfig_left
    {L K : ℕ} (s : TorusVertex width height)
    (sigmaLeft : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
      (horizontalStaircaseLeftWindow s L K))
    (sigmaRight : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
      (horizontalStaircaseRightWindow s L K)) :
    restrictSubRegionσ (V := TorusVertex width height) (d := d)
        (horizontalStaircaseLeftWindow_subset_endPair s)
        (horizontalStaircaseEndPairPhysicalConfig s sigmaLeft sigmaRight) =
      sigmaLeft := by
  funext w
  rw [restrictSubRegionσ, horizontalStaircaseEndPairPhysicalConfig,
    dite_eq_left w.2]

omit [Fact (1 < width)] [Fact (1 < height)] in
private theorem restrictSubRegionσ_horizontalStaircaseEndPairPhysicalConfig_right
    {L K : ℕ} (hxw : 2 * L ≤ width) (s : TorusVertex width height)
    (sigmaLeft : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
      (horizontalStaircaseLeftWindow s L K))
    (sigmaRight : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
      (horizontalStaircaseRightWindow s L K)) :
    restrictSubRegionσ (V := TorusVertex width height) (d := d)
        (horizontalStaircaseRightWindow_subset_endPair s)
        (horizontalStaircaseEndPairPhysicalConfig s sigmaLeft sigmaRight) =
      sigmaRight := by
  funext w
  have hnotLeft : w.1 ∉ horizontalStaircaseLeftWindow s L K := fun hleft ↦
    (Finset.disjoint_left.mp (horizontalStaircaseEndPair_disjoint hxw s)) hleft w.2
  rw [restrictSubRegionσ, horizontalStaircaseEndPairPhysicalConfig,
    dite_eq_right hnotLeft]

/-! ### The end-pair inserts as single-bond contractions -/

/-- **The left-window extension is a contraction across the reference edge.**

In boundary coordinates, extending an arbitrary insert on the left end window to the end pair
vanishes away from the fiber where the left external labels match.  Reindexing that surviving
fiber leaves exactly one sum, over the reference-edge coordinate: the insert on the left window
contracted with the genuine blocked tensor of the right window.  The displayed scalar is the
normalization already present in `extendInsert` and `threeBlockBlueCoeff`.

Source: arXiv:1804.04964, the comparison of the two ends in Lemma 5 at lines 2213--2252 and the
two highlighted open-boundary regions at lines 2415--2444 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem horizontalStaircaseLeftWindow_extendInsert_eq_singleBondContraction
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (hpos : ∀ eg : Edge (torusGraph width height), 0 < A.bondDim eg)
    (C : RegionInsert (G := torusGraph width height) (d := d) A
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K))
    (nu : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K))
    (sigma : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
      (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K)) :
    let s : TorusVertex width height := ((a : ZMod width), (b : ZMod height))
    let Wleft := horizontalStaircaseLeftWindow s L K
    let Wright := horizontalStaircaseRightWindow s L K
    let S := horizontalStaircaseEndPair s L K
    let hWS : Wleft ⊆ S := horizontalStaircaseLeftWindow_subset_endPair s
    let hblue : S \ Wleft = Wright :=
      horizontalStaircaseEndPair_sdiff_leftWindow (by omega) s
    let g := nestedThreeBlockGeometry (V := TorusVertex width height) hWS
    let Eleft := horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
    let Eright := horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
    let Eend := horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh
    let sigmaLeft := restrictSubRegionσ (V := TorusVertex width height) (d := d) hWS sigma
    let sigmaRight := regionPhysicalConfigCongr (d := d) hblue
      (restrictSubRegionσ (V := TorusVertex width height) (d := d)
        (Finset.sdiff_subset : S \ Wleft ⊆ S) sigma)
    extendInsert (G := torusGraph width height) hWS C nu sigma =
      ((regionInteriorBondProd (G := torusGraph width height) A
          (Finset.univ \ S) : ℂ) *
        (g.swapBlueComplement.blueRedCrossingBondProd A : ℂ))⁻¹ *
        ∑ k : Fin (A.bondDim (horizontalStaircaseReferenceEdge s L K)),
          C (Eleft.symm (k, (Eend nu).1)) sigmaLeft *
            regionBlockedWeight (G := torusGraph width height) A Wright
              (Eright.symm (k, (Eend nu).2)) sigmaRight := by
  classical
  dsimp only
  let s : TorusVertex width height := ((a : ZMod width), (b : ZMod height))
  let Wleft := horizontalStaircaseLeftWindow s L K
  let Wright := horizontalStaircaseRightWindow s L K
  let S := horizontalStaircaseEndPair s L K
  let hWS : Wleft ⊆ S := horizontalStaircaseLeftWindow_subset_endPair s
  let hblue : S \ Wleft = Wright :=
    horizontalStaircaseEndPair_sdiff_leftWindow (by omega) s
  let g := nestedThreeBlockGeometry (V := TorusVertex width height) hWS
  let Eleft := horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
  let Eright := horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
  let Eend := horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh
  let sigmaLeft := restrictSubRegionσ (V := TorusVertex width height) (d := d) hWS sigma
  let sigmaBlue := restrictSubRegionσ (V := TorusVertex width height) (d := d)
    (Finset.sdiff_subset : S \ Wleft ⊆ S) sigma
  let sigmaRight := regionPhysicalConfigCongr (d := d) hblue sigmaBlue
  let scalar : ℂ := ((regionInteriorBondProd (G := torusGraph width height) A
      (Finset.univ \ S) : ℂ) *
    (g.swapBlueComplement.blueRedCrossingBondProd A : ℂ))⁻¹
  change extendInsert (G := torusGraph width height) hWS C nu sigma =
    scalar * ∑ k, C (Eleft.symm (k, (Eend nu).1)) sigmaLeft *
      regionBlockedWeight (G := torusGraph width height) A Wright
        (Eright.symm (k, (Eend nu).2)) sigmaRight
  rw [extendInsert]
  rw [Finset.mul_sum]
  change (∑ mu : RegionBoundaryConfig (G := torusGraph width height) A Wleft,
      (regionInteriorBondProd (G := torusGraph width height) A
          (Finset.univ \ S) : ℂ)⁻¹ *
        (C mu sigmaLeft *
          g.threeBlockBlueCoeff
            (regionComplementBoundaryConfig (G := torusGraph width height) A Wleft mu)
            sigmaBlue
            (regionComplementBoundaryConfig (G := torusGraph width height) A S nu))) =
    scalar * ∑ k, C (Eleft.symm (k, (Eend nu).1)) sigmaLeft *
      regionBlockedWeight (G := torusGraph width height) A Wright
        (Eright.symm (k, (Eend nu).2)) sigmaRight
  rw [show (∑ mu : RegionBoundaryConfig (G := torusGraph width height) A Wleft,
        (regionInteriorBondProd (G := torusGraph width height) A
            (Finset.univ \ S) : ℂ)⁻¹ *
          (C mu sigmaLeft *
            g.threeBlockBlueCoeff
              (regionComplementBoundaryConfig (G := torusGraph width height) A Wleft mu)
              sigmaBlue
              (regionComplementBoundaryConfig (G := torusGraph width height) A S nu))) =
      ∑ mu : RegionBoundaryConfig (G := torusGraph width height) A Wleft,
        C mu sigmaLeft *
          ((regionInteriorBondProd (G := torusGraph width height) A
              (Finset.univ \ S) : ℂ)⁻¹ *
            g.threeBlockBlueCoeff
              (regionComplementBoundaryConfig (G := torusGraph width height) A Wleft mu)
              sigmaBlue
              (regionComplementBoundaryConfig (G := torusGraph width height) A S nu)) from by
      refine Finset.sum_congr rfl (fun mu _ ↦ ?_)
      ring]
  rw [show (∑ mu : RegionBoundaryConfig (G := torusGraph width height) A Wleft,
        C mu sigmaLeft *
          ((regionInteriorBondProd (G := torusGraph width height) A
              (Finset.univ \ S) : ℂ)⁻¹ *
            g.threeBlockBlueCoeff
              (regionComplementBoundaryConfig (G := torusGraph width height) A Wleft mu)
              sigmaBlue
              (regionComplementBoundaryConfig (G := torusGraph width height) A S nu)) =
      ∑ mu : RegionBoundaryConfig (G := torusGraph width height) A Wleft,
        C mu sigmaLeft *
          (if _hcompat : (Eleft mu).2 = (Eend nu).1 then
            scalar * regionBlockedWeight (G := torusGraph width height) A Wright
              (Eright.symm ((Eleft mu).1, (Eend nu).2)) sigmaRight else 0)) from by
      refine Finset.sum_congr rfl (fun mu _ ↦ congrArg (C mu sigmaLeft * ·) ?_)
      have hnorm := horizontalStaircaseLeftWindow_normalized_threeBlockBlueCoeff_factorization
        A hL hK ha0 haw hbh hpos mu nu sigmaRight
      dsimp only at hnorm
      rw [Equiv.symm_apply_apply] at hnorm
      change _ = if _hcompat : (Eleft mu).2 = (Eend nu).1 then
        scalar * regionBlockedWeight (G := torusGraph width height) A Wright
          (Eright.symm ((Eleft mu).1, (Eend nu).2)) sigmaRight else 0 at hnorm
      exact hnorm]
  rw [sum_mul_dite_eq_sum_fiber Eleft (Eend nu).1
    (fun mu ↦ C mu sigmaLeft)
    (fun k ↦ scalar * regionBlockedWeight (G := torusGraph width height) A Wright
      (Eright.symm (k, (Eend nu).2)) sigmaRight)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ ↦ ?_)
  ring

/-- **The right-window extension is a contraction across the reference edge.**

This is the opposite-end form of
`horizontalStaircaseLeftWindow_extendInsert_eq_singleBondContraction`.  Reindexing the unique
compatible external-label fiber leaves the genuine left-window blocked tensor contracted with
the insert on the right window over the single reference-edge coordinate.

Source: arXiv:1804.04964, the comparison of the two ends in Lemma 5 at lines 2213--2252 and the
two highlighted open-boundary regions at lines 2415--2444 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem horizontalStaircaseRightWindow_extendInsert_eq_singleBondContraction
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (hpos : ∀ eg : Edge (torusGraph width height), 0 < A.bondDim eg)
    (C : RegionInsert (G := torusGraph width height) (d := d) A
      (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K))
    (nu : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K))
    (sigma : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
      (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K)) :
    let s : TorusVertex width height := ((a : ZMod width), (b : ZMod height))
    let Wright := horizontalStaircaseRightWindow s L K
    let Wleft := horizontalStaircaseLeftWindow s L K
    let S := horizontalStaircaseEndPair s L K
    let hWS : Wright ⊆ S := horizontalStaircaseRightWindow_subset_endPair s
    let hblue : S \ Wright = Wleft :=
      horizontalStaircaseEndPair_sdiff_rightWindow (by omega) s
    let g := nestedThreeBlockGeometry (V := TorusVertex width height) hWS
    let Eright := horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
    let Eleft := horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
    let Eend := horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh
    let sigmaRight := restrictSubRegionσ (V := TorusVertex width height) (d := d) hWS sigma
    let sigmaLeft := regionPhysicalConfigCongr (d := d) hblue
      (restrictSubRegionσ (V := TorusVertex width height) (d := d)
        (Finset.sdiff_subset : S \ Wright ⊆ S) sigma)
    extendInsert (G := torusGraph width height) hWS C nu sigma =
      ((regionInteriorBondProd (G := torusGraph width height) A
          (Finset.univ \ S) : ℂ) *
        (g.swapBlueComplement.blueRedCrossingBondProd A : ℂ))⁻¹ *
        ∑ k : Fin (A.bondDim (horizontalStaircaseReferenceEdge s L K)),
          regionBlockedWeight (G := torusGraph width height) A Wleft
              (Eleft.symm (k, (Eend nu).1)) sigmaLeft *
            C (Eright.symm (k, (Eend nu).2)) sigmaRight := by
  classical
  dsimp only
  let s : TorusVertex width height := ((a : ZMod width), (b : ZMod height))
  let Wright := horizontalStaircaseRightWindow s L K
  let Wleft := horizontalStaircaseLeftWindow s L K
  let S := horizontalStaircaseEndPair s L K
  let hWS : Wright ⊆ S := horizontalStaircaseRightWindow_subset_endPair s
  let hblue : S \ Wright = Wleft :=
    horizontalStaircaseEndPair_sdiff_rightWindow (by omega) s
  let g := nestedThreeBlockGeometry (V := TorusVertex width height) hWS
  let Eright := horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
  let Eleft := horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
  let Eend := horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh
  let sigmaRight := restrictSubRegionσ (V := TorusVertex width height) (d := d) hWS sigma
  let sigmaBlue := restrictSubRegionσ (V := TorusVertex width height) (d := d)
    (Finset.sdiff_subset : S \ Wright ⊆ S) sigma
  let sigmaLeft := regionPhysicalConfigCongr (d := d) hblue sigmaBlue
  let scalar : ℂ := ((regionInteriorBondProd (G := torusGraph width height) A
      (Finset.univ \ S) : ℂ) *
    (g.swapBlueComplement.blueRedCrossingBondProd A : ℂ))⁻¹
  change extendInsert (G := torusGraph width height) hWS C nu sigma =
    scalar * ∑ k,
      regionBlockedWeight (G := torusGraph width height) A Wleft
          (Eleft.symm (k, (Eend nu).1)) sigmaLeft *
        C (Eright.symm (k, (Eend nu).2)) sigmaRight
  rw [extendInsert]
  rw [Finset.mul_sum]
  change (∑ mu : RegionBoundaryConfig (G := torusGraph width height) A Wright,
      (regionInteriorBondProd (G := torusGraph width height) A
          (Finset.univ \ S) : ℂ)⁻¹ *
        (C mu sigmaRight *
          g.threeBlockBlueCoeff
            (regionComplementBoundaryConfig (G := torusGraph width height) A Wright mu)
            sigmaBlue
            (regionComplementBoundaryConfig (G := torusGraph width height) A S nu))) =
    scalar * ∑ k,
      regionBlockedWeight (G := torusGraph width height) A Wleft
          (Eleft.symm (k, (Eend nu).1)) sigmaLeft *
        C (Eright.symm (k, (Eend nu).2)) sigmaRight
  rw [show (∑ mu : RegionBoundaryConfig (G := torusGraph width height) A Wright,
        (regionInteriorBondProd (G := torusGraph width height) A
            (Finset.univ \ S) : ℂ)⁻¹ *
          (C mu sigmaRight *
            g.threeBlockBlueCoeff
              (regionComplementBoundaryConfig (G := torusGraph width height) A Wright mu)
              sigmaBlue
              (regionComplementBoundaryConfig (G := torusGraph width height) A S nu))) =
      ∑ mu : RegionBoundaryConfig (G := torusGraph width height) A Wright,
        C mu sigmaRight *
          ((regionInteriorBondProd (G := torusGraph width height) A
              (Finset.univ \ S) : ℂ)⁻¹ *
            g.threeBlockBlueCoeff
              (regionComplementBoundaryConfig (G := torusGraph width height) A Wright mu)
              sigmaBlue
              (regionComplementBoundaryConfig (G := torusGraph width height) A S nu)) from by
      refine Finset.sum_congr rfl (fun mu _ ↦ ?_)
      ring]
  rw [show (∑ mu : RegionBoundaryConfig (G := torusGraph width height) A Wright,
        C mu sigmaRight *
          ((regionInteriorBondProd (G := torusGraph width height) A
              (Finset.univ \ S) : ℂ)⁻¹ *
            g.threeBlockBlueCoeff
              (regionComplementBoundaryConfig (G := torusGraph width height) A Wright mu)
              sigmaBlue
              (regionComplementBoundaryConfig (G := torusGraph width height) A S nu)) =
      ∑ mu : RegionBoundaryConfig (G := torusGraph width height) A Wright,
        C mu sigmaRight *
          (if _hcompat : (Eright mu).2 = (Eend nu).2 then
            scalar * regionBlockedWeight (G := torusGraph width height) A Wleft
              (Eleft.symm ((Eright mu).1, (Eend nu).1)) sigmaLeft else 0)) from by
      refine Finset.sum_congr rfl (fun mu _ ↦ congrArg (C mu sigmaRight * ·) ?_)
      have hnorm := horizontalStaircaseRightWindow_normalized_threeBlockBlueCoeff_factorization
        A hL hK ha0 haw hbh hpos mu nu sigmaLeft
      dsimp only at hnorm
      rw [Equiv.symm_apply_apply] at hnorm
      change _ = if _hcompat : (Eright mu).2 = (Eend nu).2 then
        scalar * regionBlockedWeight (G := torusGraph width height) A Wleft
          (Eleft.symm ((Eright mu).1, (Eend nu).1)) sigmaLeft else 0 at hnorm
      exact hnorm]
  rw [sum_mul_dite_eq_sum_fiber Eright (Eend nu).2
    (fun mu ↦ C mu sigmaRight)
    (fun k ↦ scalar * regionBlockedWeight (G := torusGraph width height) A Wleft
      (Eleft.symm (k, (Eend nu).1)) sigmaLeft)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ ↦ ?_)
  ring

/-- **Equal end-pair extensions give the single-bond contraction identity.**

If an insert on the left end window and an insert on the right end window have equal extensions
to the end pair, then their boundary-coordinate forms agree after contraction over the sole shared
reference edge.  Translation invariance is used exactly once: it identifies the two external
crossing-bond normalization factors.  Their common nonzero scalar then cancels.  No injectivity of
a single vertex, of the end pair, or of its torus complement is used.

This is the contraction identity consumed by
`existsUnique_virtualOperation_of_endPair`: the two genuine end-window blocked tensors occur on
the unmodified sides, while the arbitrary inserts occur on the opposite sides.

Source: arXiv:1804.04964, the comparison of the two ends in Lemma 5 at lines 2213--2252 and the
translation-invariant two-dimensional end-window comparison at lines 2415--2444 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem singleBondContraction_eq_of_horizontalStaircaseEndPair_extendInsert_eq
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hTI : IsTorusTranslationInvariant A)
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (hpos : ∀ eg : Edge (torusGraph width height), 0 < A.bondDim eg)
    (Cleft : RegionInsert (G := torusGraph width height) (d := d) A
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K))
    (Cright : RegionInsert (G := torusGraph width height) (d := d) A
      (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K))
    (heq :
      extendInsert (G := torusGraph width height)
          (horizontalStaircaseLeftWindow_subset_endPair
            ((a : ZMod width), (b : ZMod height))) Cleft =
        extendInsert (G := torusGraph width height)
          (horizontalStaircaseRightWindow_subset_endPair
            ((a : ZMod width), (b : ZMod height))) Cright)
    (nu : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K))
    (sigma : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
      (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K)) :
    let s : TorusVertex width height := ((a : ZMod width), (b : ZMod height))
    let Wleft := horizontalStaircaseLeftWindow s L K
    let Wright := horizontalStaircaseRightWindow s L K
    let S := horizontalStaircaseEndPair s L K
    let hleft : Wleft ⊆ S := horizontalStaircaseLeftWindow_subset_endPair s
    let hright : Wright ⊆ S := horizontalStaircaseRightWindow_subset_endPair s
    let Eleft := horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
    let Eright := horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
    let Eend := horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh
    let sigmaLeft := restrictSubRegionσ (V := TorusVertex width height) (d := d) hleft sigma
    let sigmaRight := restrictSubRegionσ (V := TorusVertex width height) (d := d) hright sigma
    (∑ k : Fin (A.bondDim (horizontalStaircaseReferenceEdge s L K)),
        Cleft (Eleft.symm (k, (Eend nu).1)) sigmaLeft *
          regionBlockedWeight (G := torusGraph width height) A Wright
            (Eright.symm (k, (Eend nu).2)) sigmaRight) =
      ∑ k : Fin (A.bondDim (horizontalStaircaseReferenceEdge s L K)),
        regionBlockedWeight (G := torusGraph width height) A Wleft
            (Eleft.symm (k, (Eend nu).1)) sigmaLeft *
          Cright (Eright.symm (k, (Eend nu).2)) sigmaRight := by
  classical
  dsimp only
  let s : TorusVertex width height := ((a : ZMod width), (b : ZMod height))
  let Wleft := horizontalStaircaseLeftWindow s L K
  let Wright := horizontalStaircaseRightWindow s L K
  let S := horizontalStaircaseEndPair s L K
  let hleft : Wleft ⊆ S := horizontalStaircaseLeftWindow_subset_endPair s
  let hright : Wright ⊆ S := horizontalStaircaseRightWindow_subset_endPair s
  let hblueLeft : S \ Wleft = Wright :=
    horizontalStaircaseEndPair_sdiff_leftWindow (by omega) s
  let hblueRight : S \ Wright = Wleft :=
    horizontalStaircaseEndPair_sdiff_rightWindow (by omega) s
  let gleft := nestedThreeBlockGeometry (V := TorusVertex width height) hleft
  let gright := nestedThreeBlockGeometry (V := TorusVertex width height) hright
  let Eleft := horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
  let Eright := horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
  let Eend := horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh
  let sigmaLeft := restrictSubRegionσ (V := TorusVertex width height) (d := d) hleft sigma
  let sigmaRight := restrictSubRegionσ (V := TorusVertex width height) (d := d) hright sigma
  let sigmaLeftFromBlue := regionPhysicalConfigCongr (d := d) hblueRight
    (restrictSubRegionσ (V := TorusVertex width height) (d := d)
      (Finset.sdiff_subset : S \ Wright ⊆ S) sigma)
  let sigmaRightFromBlue := regionPhysicalConfigCongr (d := d) hblueLeft
    (restrictSubRegionσ (V := TorusVertex width height) (d := d)
      (Finset.sdiff_subset : S \ Wleft ⊆ S) sigma)
  let scalarLeft : ℂ := ((regionInteriorBondProd (G := torusGraph width height) A
      (Finset.univ \ S) : ℂ) *
    (gleft.swapBlueComplement.blueRedCrossingBondProd A : ℂ))⁻¹
  let scalarRight : ℂ := ((regionInteriorBondProd (G := torusGraph width height) A
      (Finset.univ \ S) : ℂ) *
    (gright.swapBlueComplement.blueRedCrossingBondProd A : ℂ))⁻¹
  have hsigmaLeft : sigmaLeftFromBlue = sigmaLeft := by
    funext w
    rfl
  have hsigmaRight : sigmaRightFromBlue = sigmaRight := by
    funext w
    rfl
  have hpoint := congrFun (congrFun heq nu) sigma
  rw [horizontalStaircaseLeftWindow_extendInsert_eq_singleBondContraction
      A hL hK ha0 haw hbh hpos Cleft nu sigma,
    horizontalStaircaseRightWindow_extendInsert_eq_singleBondContraction
      A hL hK ha0 haw hbh hpos Cright nu sigma] at hpoint
  change scalarLeft *
      (∑ k, Cleft (Eleft.symm (k, (Eend nu).1)) sigmaLeft *
        regionBlockedWeight (G := torusGraph width height) A Wright
          (Eright.symm (k, (Eend nu).2)) sigmaRightFromBlue) =
    scalarRight *
      (∑ k, regionBlockedWeight (G := torusGraph width height) A Wleft
          (Eleft.symm (k, (Eend nu).1)) sigmaLeftFromBlue *
        Cright (Eright.symm (k, (Eend nu).2)) sigmaRight) at hpoint
  rw [hsigmaLeft, hsigmaRight] at hpoint
  have hcross := horizontalStaircaseEndWindows_externalCrossingBondProd_eq
    A hTI hpos hL hK ha0 haw hbh
  dsimp only at hcross
  change gleft.swapBlueComplement.blueRedCrossingBondProd A =
    gright.swapBlueComplement.blueRedCrossingBondProd A at hcross
  have hscalar : scalarLeft = scalarRight := by
    simp only [scalarLeft, scalarRight, hcross]
  rw [← hscalar] at hpoint
  have houter :
      (regionInteriorBondProd (G := torusGraph width height) A
        (Finset.univ \ S) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr
      (regionInteriorBondProd_pos (G := torusGraph width height) A
        (Finset.univ \ S) hpos).ne'
  have hcrossPos : 0 < gleft.swapBlueComplement.blueRedCrossingBondProd A := by
    rw [ThreeBlockGeometry.blueRedCrossingBondProd]
    exact Finset.prod_pos (fun eg _ ↦ hpos eg)
  have hcrossNe : (gleft.swapBlueComplement.blueRedCrossingBondProd A : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hcrossPos.ne'
  have hscalarNe : scalarLeft ≠ 0 :=
    inv_ne_zero (mul_ne_zero houter hcrossNe)
  exact mul_left_cancel₀ hscalarNe hpoint

/-- **The unique virtual operation extracted from the two end windows.**

Let the genuine blocked tensors of the two highlighted end windows be injective, and let arbitrary
inserts on those windows have equal extensions to their open end pair.  Then there is a unique
matrix `X` on the highlighted reference edge such that the left insert is obtained from the genuine
left block by inserting `X`, while the right insert is obtained from the genuine right block by the
transpose-side action of the same `X`.

The proof first uses
`singleBondContraction_eq_of_horizontalStaircaseEndPair_extendInsert_eq` to obtain the exact
single-bond contraction identity.  It then invokes
`existsUnique_virtualOperation_of_endPair`, whose operator-Schmidt argument requires linear
independence only of the two genuine blocked tensors.  In particular, neither modified insert is
assumed injective, and no injectivity is imposed on a vertex, the end pair, or its complement.

Source: arXiv:1804.04964, Lemma 5, especially the comparison of the two ends at lines 2213--2252,
and the two-dimensional open-boundary realization at lines 2415--2444 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem existsUnique_virtualOperation_of_horizontalStaircaseEndPair
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hTI : IsTorusTranslationInvariant A)
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (hpos : ∀ eg : Edge (torusGraph width height), 0 < A.bondDim eg)
    (hleftInjective : RegionBlockedTensorInjective (G := torusGraph width height) A
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K))
    (hrightInjective : RegionBlockedTensorInjective (G := torusGraph width height) A
      (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K))
    (Cleft : RegionInsert (G := torusGraph width height) (d := d) A
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K))
    (Cright : RegionInsert (G := torusGraph width height) (d := d) A
      (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K))
    (heq :
      extendInsert (G := torusGraph width height)
          (horizontalStaircaseLeftWindow_subset_endPair
            ((a : ZMod width), (b : ZMod height))) Cleft =
        extendInsert (G := torusGraph width height)
          (horizontalStaircaseRightWindow_subset_endPair
            ((a : ZMod width), (b : ZMod height))) Cright) :
    let s : TorusVertex width height := ((a : ZMod width), (b : ZMod height))
    let Wleft := horizontalStaircaseLeftWindow s L K
    let Wright := horizontalStaircaseRightWindow s L K
    let Eleft := horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
    let Eright := horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
    ∃! X : Matrix
        (Fin (A.bondDim (horizontalStaircaseReferenceEdge s L K)))
        (Fin (A.bondDim (horizontalStaircaseReferenceEdge s L K))) ℂ,
      (∀ (k : Fin (A.bondDim (horizontalStaircaseReferenceEdge s L K)))
          (etaLeft : HorizontalStaircaseLeftExternalBoundaryConfig A (L := L) (K := K) s)
          (sigmaLeft : RegionPhysicalConfig (V := TorusVertex width height) (d := d) Wleft),
        Cleft (Eleft.symm (k, etaLeft)) sigmaLeft =
          ∑ j, regionBlockedWeight (G := torusGraph width height) A Wleft
              (Eleft.symm (j, etaLeft)) sigmaLeft * X j k) ∧
      ∀ (k : Fin (A.bondDim (horizontalStaircaseReferenceEdge s L K)))
          (etaRight : HorizontalStaircaseRightExternalBoundaryConfig A (L := L) (K := K) s)
          (sigmaRight : RegionPhysicalConfig (V := TorusVertex width height) (d := d) Wright),
        Cright (Eright.symm (k, etaRight)) sigmaRight =
          ∑ j, X k j * regionBlockedWeight (G := torusGraph width height) A Wright
            (Eright.symm (j, etaRight)) sigmaRight := by
  classical
  dsimp only
  let s : TorusVertex width height := ((a : ZMod width), (b : ZMod height))
  let Wleft := horizontalStaircaseLeftWindow s L K
  let Wright := horizontalStaircaseRightWindow s L K
  let S := horizontalStaircaseEndPair s L K
  let hleft : Wleft ⊆ S := horizontalStaircaseLeftWindow_subset_endPair s
  let hright : Wright ⊆ S := horizontalStaircaseRightWindow_subset_endPair s
  let Eleft := horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
  let Eright := horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
  let Eend := horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh
  let Kedge := Fin (A.bondDim (horizontalStaircaseReferenceEdge s L K))
  let LeftExternal := HorizontalStaircaseLeftExternalBoundaryConfig A (L := L) (K := K) s
  let RightExternal := HorizontalStaircaseRightExternalBoundaryConfig A (L := L) (K := K) s
  let LeftPhysical := RegionPhysicalConfig (V := TorusVertex width height) (d := d) Wleft
  let RightPhysical := RegionPhysicalConfig (V := TorusVertex width height) (d := d) Wright
  let Aleft : Kedge → LeftExternal × LeftPhysical → ℂ :=
    fun k p ↦ regionBlockedWeight (G := torusGraph width height) A Wleft
      (Eleft.symm (k, p.1)) p.2
  let CleftFamily : Kedge → LeftExternal × LeftPhysical → ℂ :=
    fun k p ↦ Cleft (Eleft.symm (k, p.1)) p.2
  let Aright : Kedge → RightExternal × RightPhysical → ℂ :=
    fun k p ↦ regionBlockedWeight (G := torusGraph width height) A Wright
      (Eright.symm (k, p.1)) p.2
  let CrightFamily : Kedge → RightExternal × RightPhysical → ℂ :=
    fun k p ↦ Cright (Eright.symm (k, p.1)) p.2
  let _ : Nonempty LeftExternal := ⟨fun f ↦ ⟨0, hpos f.1.1⟩⟩
  let _ : Nonempty RightExternal := ⟨fun f ↦ ⟨0, hpos f.1.1⟩⟩
  have hleftJoint : LinearIndependent ℂ
      (fun p : LeftExternal × Kedge ↦ fun sigmaLeft : LeftPhysical ↦
        regionBlockedWeight (G := torusGraph width height) A Wleft
          (Eleft.symm (p.2, p.1)) sigmaLeft) := by
    let F : LeftExternal × Kedge ≃
        RegionBoundaryConfig (G := torusGraph width height) A Wleft :=
      (Equiv.prodComm LeftExternal Kedge).trans Eleft.symm
    have hreindexed := (linearIndependent_equiv F).mpr hleftInjective
    change LinearIndependent ℂ
      (regionBlockedTensorFamily (G := torusGraph width height) A Wleft ∘ F)
    exact hreindexed
  have hrightJoint : LinearIndependent ℂ
      (fun p : RightExternal × Kedge ↦ fun sigmaRight : RightPhysical ↦
        regionBlockedWeight (G := torusGraph width height) A Wright
          (Eright.symm (p.2, p.1)) sigmaRight) := by
    let F : RightExternal × Kedge ≃
        RegionBoundaryConfig (G := torusGraph width height) A Wright :=
      (Equiv.prodComm RightExternal Kedge).trans Eright.symm
    have hreindexed := (linearIndependent_equiv F).mpr hrightInjective
    change LinearIndependent ℂ
      (regionBlockedTensorFamily (G := torusGraph width height) A Wright ∘ F)
    exact hreindexed
  have hAleft : LinearIndependent ℂ (fun k : Kedge ↦ (Aleft k :
      LeftExternal × LeftPhysical → ℂ)) := by
    exact linearIndependent_shared_of_joint
      (fun eta k sigmaLeft ↦ regionBlockedWeight (G := torusGraph width height) A Wleft
        (Eleft.symm (k, eta)) sigmaLeft) hleftJoint
  have hAright : LinearIndependent ℂ (fun k : Kedge ↦ (Aright k :
      RightExternal × RightPhysical → ℂ)) := by
    exact linearIndependent_shared_of_joint
      (fun eta k sigmaRight ↦ regionBlockedWeight (G := torusGraph width height) A Wright
        (Eright.symm (k, eta)) sigmaRight) hrightJoint
  have hcontract : ∀ (pLeft : LeftExternal × LeftPhysical)
      (pRight : RightExternal × RightPhysical),
      (∑ k : Kedge, CleftFamily k pLeft * Aright k pRight) =
        ∑ k : Kedge, Aleft k pLeft * CrightFamily k pRight := by
    intro pLeft pRight
    let nu : RegionBoundaryConfig (G := torusGraph width height) A S :=
      Eend.symm (pLeft.1, pRight.1)
    let sigma : RegionPhysicalConfig (V := TorusVertex width height) (d := d) S :=
      horizontalStaircaseEndPairPhysicalConfig s pLeft.2 pRight.2
    have hsingle :=
      singleBondContraction_eq_of_horizontalStaircaseEndPair_extendInsert_eq
        A hTI hL hK ha0 haw hbh hpos Cleft Cright heq nu sigma
    dsimp only at hsingle
    rw [Eend.apply_symm_apply,
      restrictSubRegionσ_horizontalStaircaseEndPairPhysicalConfig_left,
      restrictSubRegionσ_horizontalStaircaseEndPairPhysicalConfig_right (by omega)] at hsingle
    change (∑ k : Kedge, CleftFamily k pLeft * Aright k pRight) =
      ∑ k : Kedge, Aleft k pLeft * CrightFamily k pRight
    exact hsingle
  have hexists := existsUnique_virtualOperation_of_endPair
    Aleft CleftFamily Aright CrightFamily hAleft hAright hcontract
  rcases hexists with ⟨X, hX, hXunique⟩
  refine ⟨X, ⟨?_, ?_⟩, ?_⟩
  · intro k etaLeft sigmaLeft
    simpa only [Aleft, CleftFamily] using hX.1 k (etaLeft, sigmaLeft)
  · intro k etaRight sigmaRight
    simpa only [Aright, CrightFamily] using hX.2 k (etaRight, sigmaRight)
  · intro Y hY
    apply hXunique
    constructor
    · intro k pLeft
      simpa only [Aleft, CleftFamily] using hY.1 k pLeft.1 pLeft.2
    · intro k pRight
      simpa only [Aright, CrightFamily] using hY.2 k pRight.1 pRight.2

end Torus

end PEPS
end TNLean
