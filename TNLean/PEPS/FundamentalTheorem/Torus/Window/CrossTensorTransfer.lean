/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.FundamentalTheorem.Torus.Window.ConjugationCoefficient
import TNLean.PEPS.FundamentalTheorem.Torus.TorusEdgeGaugeCovariance
import TNLean.PEPS.FundamentalTheorem.Torus.TorusCoordinateSwap
import TNLean.PEPS.FundamentalTheorem.Torus.Window.CrossTensorAlgebra

/-!
# The unscaled staircase coefficient transfer

Equality of the bond dimensions on every edge identifies the two products of dimensions
away from the window boundary. Cancelling their nonzero common value gives the exact
coefficient correspondence for the canonical staircase assignment. Its algebraic laws and
reverse assignment give a region-insertion transfer and an invertible conjugating gauge.

The comparison uses a displayed non-wrapping horizontal staircase with positive window
lengths. Coordinate exchange gives the vertical witness, and translation gives all edges.
The derivation is recorded in `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`.

**Local fix (nonzero virtual spaces):** the source treats the virtual bond spaces as nonzero
(arXiv:1804.04964, lines 582 and 1037 of `Papers/1804.04964/paper_normal.tex`). The steps here
take the window hypotheses as region data and state the positive bond dimensions of both
tensors explicitly; their caller `exists_translationCovariantGauge_of_normalArcWindows_sameState`
takes both from the tensor hypothesis `IsNormalTorusArcWindowPEPS`. Documented in
`docs/paper-gaps/peps_injective_ft_section3_route.tex`.

Source: arXiv:1804.04964, lines 563--586 and 2368--2444 of
`Papers/1804.04964/paper_normal.tex`.

## A vertical reference-edge coefficient identity

Exchange the torus coordinates and apply the horizontal staircase construction at placement
`(1, 0)`, with the window lengths exchanged. Pull the resulting witness back to the original
tensor pair. The distinguished edge does not cross a coordinate seam, so its first stored
endpoint is preserved by the coordinate exchange.

All positive window lengths are allowed. The torus bounds are `2L+1 ≤ width` and
`2K+1 ≤ height`, without a larger-window injectivity assumption. The derivation is recorded
in `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`.

Source: arXiv:1804.04964, the exchange of directions at lines 2368--2444 of
`Papers/1804.04964/paper_normal.tex`.

It also contains the following results.

* `TNLean.PEPS.bondDim_eq_of_normalArcWindows_sameState`: equality of all torus bond dimensions from
  normal arc windows.
-/

section CrossTensorDimensions

/-!
## Equality of all torus bond dimensions from normal arc windows

The staircase algebra isomorphism determines one horizontal bond dimension.
Exchanging coordinates gives a vertical comparison. Translation invariance then
identifies the dimensions at every edge. The argument uses the same arc-window
hypotheses in both directions and does not assume equality of the products of
non-boundary bond dimensions.

The bond-dimension theorem accepts all positive window lengths at the source's minimal
torus sizes. The complete derivation is recorded in
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`.

**Local fix (nonzero virtual spaces):** the source treats the virtual bond spaces as nonzero
(arXiv:1804.04964, lines 582 and 1037 of `Papers/1804.04964/paper_normal.tex`) without listing
this among the hypotheses of its corollaries. The bond-dimension theorem takes the tensor
hypothesis `IsNormalTorusArcWindowPEPS`, whose field `bondDim_pos` carries it; the private
horizontal step receives the positivity from that theorem. Documented in
`docs/paper-gaps/peps_injective_ft_section3_route.tex`.

Source: arXiv:1804.04964, lines 582--586 and 2368--2444 of
`Papers/1804.04964/paper_normal.tex`.
-/

open ManyBody (Edge)

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

/-- Equality of PEPS states determines every bond dimension of two normal torus tensors at
window size `L × K`. The torus has at least `2 * L + 1` columns and `2 * K + 1` rows,
with positive `L` and `K`. The proof compares a horizontal staircase bond, exchanges the
coordinates for the vertical comparison, and uses translation invariance.

Source: arXiv:1804.04964, lines 582--586 and 2368--2444 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem bondDim_eq_of_normalArcWindows_sameState
    (A B : Tensor (torusGraph width height) d)
    (hAn : IsNormalTorusArcWindowPEPS L K A) (hBn : IsNormalTorusArcWindowPEPS L K B)
    (hATI : IsTorusTranslationInvariant A) (hBTI : IsTorusTranslationInvariant B)
    (hAB : SameState A B) (hL : 0 < L) (hK : 0 < K)
    (hxw : 2 * L + 1 ≤ width) (hyh : 2 * K + 1 ≤ height) :
    A.bondDim = B.bondDim := by
  obtain ⟨hA, hposA⟩ := hAn
  obtain ⟨hB, hposB⟩ := hBn
  have hH := horizontalBondDim_eq_at_origin A B hA hB hATI hBTI hAB
    hposA hposB hL hK hxw hyh
  have hV' := horizontalBondDim_eq_at_origin
    (A.transport torusCoordinateSwap) (B.transport torusCoordinateSwap)
    (hA.transportCoordinateSwap A) (hB.transportCoordinateSwap B)
    (hATI.transportCoordinateSwap A) (hBTI.transportCoordinateSwap B)
    (hAB.transport torusCoordinateSwap)
    (fun e ↦ hposA (ManyBody.Edge.map torusCoordinateSwap.symm e))
    (fun e ↦ hposB (ManyBody.Edge.map torusCoordinateSwap.symm e)) hK hL hyh hxw
  have hzero : (0 : TorusVertex width height) = (0, 0) := rfl
  have hV : A.bondDim (torusUpEdge 0) = B.bondDim (torusUpEdge 0) := by
    rw [hzero]
    simpa [Tensor.transport_bondDim, torusCoordinateSwap_symm,
      ManyBody.Edge.map_torusCoordinateSwap_rightEdge] using hV'
  exact bondDim_eq_of_orientation_references A B hATI hBTI hH hV

end TNLean.PEPS

end CrossTensorDimensions

section CrossTensorTransfer

section

open ManyBody (Edge)

namespace TNLean.PEPS
open scoped Matrix

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
variable (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
variable (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
variable (hxw : 2 * L + 1 ≤ width) (hyh : 2 * K + 1 ≤ height)

include hA hB hATI hBTI hAB hposA hposB hL hK ha0 haw hbh hxw hyh in
/-- The canonical staircase assignment matches the unscaled inserted coefficients at every
physical configuration. All-edge bond-dimension equality identifies the non-boundary-bond
products, and their positivity permits cancellation.

Source: arXiv:1804.04964, the insertion correspondence at lines 563--582 and the
two-dimensional comparison at lines 2368--2444 of `Papers/1804.04964/paper_normal.tex`. -/
theorem staircaseCrossTensorVirtualOperation_coeff
    (X : Matrix
      (Fin (A.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K)))
      (Fin (A.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K))) ℂ)
    (σ : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K))
    (τ : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
      (Finset.univ \ horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)) :
    let W := horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K
    let f : {f : Edge (torusGraph width height) // ManyBody.IsRegionBoundaryEdge W f} :=
      ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A
        (by omega) (by omega) ha0 haw hbh⟩
    regionInsertedCoeff A W f X σ τ = regionInsertedCoeff B W f
      (staircaseCrossTensorVirtualOperation A B hA hB hATI hBTI hAB hposA hposB
        hL hK ha0 haw hbh hxw hyh X) σ τ := by
  have hDim := bondDim_eq_of_normalArcWindows_sameState A B ⟨hA, hposA⟩ ⟨hB, hposB⟩
    hATI hBTI hAB hL hK hxw hyh
  have h := staircaseCrossTensorVirtualOperation_normalized_coeff A B hA hB hATI hBTI hAB
    hposA hposB hL hK ha0 haw hbh hxw hyh X σ τ
  simp only [regionInteriorBondProd_congr A B _ hDim] at h
  exact mul_left_cancel₀
    (Nat.cast_ne_zero.mpr (regionInteriorBondProd_pos B _ hposB).ne' :
      (regionInteriorBondProd B _ : ℂ) ≠ 0) h

include hA hB hATI hBTI hAB hposA hposB hL hK ha0 haw hbh hxw hyh in
/-- The canonical staircase assignment and its reverse give a region-insertion transfer,
with the coefficient identities and algebraic laws proved from the equal-state hypotheses.

Source: arXiv:1804.04964, the insertion correspondence at lines 563--582 and the
two-dimensional comparison at lines 2368--2444. -/
noncomputable def staircaseRegionInsertionTransfer :
    let W := horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K
    let f : {f : Edge (torusGraph width height) // ManyBody.IsRegionBoundaryEdge W f} :=
      ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A
        (by omega) (by omega) ha0 haw hbh⟩
    RegionInsertionTransfer A B W f where
  fwd := staircaseCrossTensorVirtualOperation A B hA hB hATI hBTI hAB
    hposA hposB hL hK ha0 haw hbh hxw hyh
  bwd := staircaseCrossTensorVirtualOperation B A hB hA hBTI hATI hAB.symm
    hposB hposA hL hK ha0 haw hbh hxw hyh
  fwd_coeff := staircaseCrossTensorVirtualOperation_coeff A B hA hB hATI hBTI hAB
    hposA hposB hL hK ha0 haw hbh hxw hyh
  bwd_coeff := staircaseCrossTensorVirtualOperation_coeff B A hB hA hBTI hATI hAB.symm
    hposB hposA hL hK ha0 haw hbh hxw hyh
  fwd_mul := staircaseCrossTensorVirtualOperation_mul A B hA hB hATI hBTI hAB
    hposA hposB hL hK ha0 haw hbh hxw hyh
  fwd_one := staircaseCrossTensorVirtualOperation_one A B hA hB hATI hBTI hAB
    hposA hposB hL hK ha0 haw hbh hxw hyh

include hA hB hATI hBTI hAB hposA hposB hL hK ha0 haw hbh hxw hyh in
/-- Any chosen coefficient transfer on the staircase window equals the canonical virtual
assignment. Injectivity of the second tensor on the window and its complement gives uniqueness.

Source: arXiv:1804.04964, the uniqueness of the insertion correspondence at lines 563--582. -/
theorem coeffTransferMap_eq_staircaseCrossTensorVirtualOperation :
    let W := horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K
    let f : {f : Edge (torusGraph width height) // ManyBody.IsRegionBoundaryEdge W f} :=
      ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A
        (by omega) (by omega) ha0 haw hbh⟩
    ∀ (htransfer : ∀ X : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ,
      ∃ Y : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ,
        ∀ (σ : RegionPhysicalConfig (V := TorusVertex width height) (d := d) W)
          (τ : RegionPhysicalConfig (V := TorusVertex width height) (d := d) (Finset.univ \ W)),
          regionInsertedCoeff A W f X σ τ = regionInsertedCoeff B W f Y σ τ)
      (X : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ),
      coeffTransferMap A B W f htransfer X =
        staircaseCrossTensorVirtualOperation A B hA hB hATI hBTI hAB
          hposA hposB hL hK ha0 haw hbh hxw hyh X := by
  dsimp only
  intro htransfer X
  have hRB : RegionBlockedTensorInjective B
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K) := by
    simpa only [regionInjectivityDataOf_isInjective] using
      hB.horizontalStaircaseLeftWindow_injective ((a : ZMod width), (b : ZMod height))
  apply regionInsertedCoeff_injective B _ hRB
    (hB.regionBlockedTensorInjective_windowComplement
      (regionInjectivityUnionClosure_of_overlap B hposB) hL hK hxw hyh _) hposB
  intro σ τ
  have hChosen := coeffTransferMap_coeff A B
    (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
    ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A
      (by omega) (by omega) ha0 haw hbh⟩ htransfer X σ τ
  exact hChosen.symm.trans (staircaseCrossTensorVirtualOperation_coeff
    A B hA hB hATI hBTI hAB hposA hposB hL hK ha0 haw hbh hxw hyh X σ τ)

include hA hB hATI hBTI hAB hposA hposB hL hK ha0 haw hbh hxw hyh in
/-- The staircase insertion correspondence is conjugation by an invertible bond matrix,
with the unscaled coefficient identity at every pair of physical configurations.

Source: arXiv:1804.04964, the Skolem--Noether conclusion at lines 582--586 and its
two-dimensional reduction at lines 2368--2444. -/
theorem exists_staircaseWindowConjCoeffIdentity :
    let W := horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K
    let f : {f : Edge (torusGraph width height) // ManyBody.IsRegionBoundaryEdge W f} :=
      ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A
        (by omega) (by omega) ha0 haw hbh⟩
    ∃ (hE : A.bondDim f.1 = B.bondDim f.1) (Z : GL (Fin (B.bondDim f.1)) ℂ),
      ∀ (X : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
        (σ : RegionPhysicalConfig (V := TorusVertex width height) (d := d) W)
        (τ : RegionPhysicalConfig (V := TorusVertex width height) (d := d) (Finset.univ \ W)),
        regionInsertedCoeff A W f X σ τ = regionInsertedCoeff B W f
          ((Z : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) *
            Matrix.reindexAlgEquiv ℂ ℂ (finCongr hE) X *
            (↑Z⁻¹ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)) σ τ := by
  obtain ⟨hE, Z, hZ⟩ := Matrix.matrixAlgEquiv_inner_of_fin
    (staircaseCrossTensorAlgEquiv A B hA hB hATI hBTI hAB
      hposA hposB hL hK ha0 haw hbh hxw hyh)
  refine ⟨hE, Z, ?_⟩
  intro X σ τ
  have hZ' : staircaseCrossTensorVirtualOperation A B hA hB hATI hBTI hAB
      hposA hposB hL hK ha0 haw hbh hxw hyh X =
      (Z : Matrix (Fin (B.bondDim _)) (Fin (B.bondDim _)) ℂ) *
        Matrix.reindexAlgEquiv ℂ ℂ (finCongr hE) X *
        (↑Z⁻¹ : Matrix (Fin (B.bondDim _)) (Fin (B.bondDim _)) ℂ) := hZ X
  simpa only [hZ'] using staircaseCrossTensorVirtualOperation_coeff
    A B hA hB hATI hBTI hAB hposA hposB hL hK ha0 haw hbh hxw hyh X σ τ

include hA hB hATI hBTI hAB hposA hposB hL hK ha0 haw hbh hxw hyh in
/-- The displayed horizontal edge has a coefficient-identity witness on its left window.
The first stored endpoint belongs to that window, as required by the translation-covariant
gauge construction.

Source: arXiv:1804.04964, the two-dimensional gauge construction at lines 2368--2444. -/
theorem exists_staircaseWindowEdgeCoeffIdentityWitness :
    let e := horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K
    ∃ (hE : A.bondDim e = B.bondDim e) (Z : GL (Fin (B.bondDim e)) ℂ)
      (T : EdgeCoeffIdentityWitness A B e Z Z hE),
      T.region = horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K ∧
        e.1.1 ∈ T.region := by
  obtain ⟨hE, Z, hZ⟩ := exists_staircaseWindowConjCoeffIdentity
    A B hA hB hATI hBTI hAB hposA hposB hL hK ha0 haw hbh hxw hyh
  let T := windowEdgeCoeffIdentityWitness_of_hypotheses hB
    (regionInjectivityUnionClosure_of_overlap B hposB) hL hK ha0 haw hbh hxw hyh
    Z hE hposB hZ
  refine ⟨hE, Z, T, rfl, ?_⟩
  change (horizontalStaircaseReferenceEdge
    ((a : ZMod width), (b : ZMod height)) L K).1.1 ∈
    horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K
  have hep := torusRightEdge_endpoints_of_lt
    (p := ((a : ZMod width) + ((L - 1 : ℕ) : ZMod width), (b : ZMod height) +
      ((K - 1 : ℕ) : ZMod height)))
    (width := width) (height := height)
    (by rw [show (a : ZMod width) + ((L - 1 : ℕ) : ZMod width) =
          ((a + L - 1 : ℕ) : ZMod width)
          by rw [show a + L - 1 = a + (L - 1) by omega]; push_cast; ring,
        ZMod.val_natCast_of_lt (by omega)]; omega)
  rw [horizontalStaircaseReferenceEdge, hep.1, horizontalStaircaseLeftWindow,
    mem_torusArcRectangle]
  constructor <;>
    rw [add_sub_cancel_left, ZMod.val_natCast_of_lt (by omega)] <;> omega

end TNLean.PEPS

end

section

open ManyBody (Edge)

namespace TNLean.PEPS
variable {width height d L K : ℕ} [NeZero width] [NeZero height]
variable [Fact (1 < width)] [Fact (1 < height)]

/-- Normal translation-invariant tensors generating the same torus state have a vertical
reference-edge coefficient identity, with its first stored endpoint in the witnessing region.
The torus sizes are the original window bounds; no larger rectangle is assumed injective.

Source: arXiv:1804.04964, the two-dimensional comparison at lines 2368--2444 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem exists_verticalEdgeCoeffIdentityWitness_of_normalArcWindows
    (A B : Tensor (torusGraph width height) d)
    (hA : NormalTorusArcWindowInjectivityHypotheses L K (regionInjectivityDataOf A))
    (hB : NormalTorusArcWindowInjectivityHypotheses L K (regionInjectivityDataOf B))
    (hATI : IsTorusTranslationInvariant A) (hBTI : IsTorusTranslationInvariant B)
    (hAB : SameState A B)
    (hposA : ∀ e : Edge (torusGraph width height), 0 < A.bondDim e)
    (hposB : ∀ e : Edge (torusGraph width height), 0 < B.bondDim e)
    (hL : 0 < L) (hK : 0 < K)
    (hxw : 2 * L + 1 ≤ width) (hyh : 2 * K + 1 ≤ height) :
    ∃ e : Edge (torusGraph width height), IsVerticalTorusEdge e ∧
      ∃ (hE : A.bondDim e = B.bondDim e) (Z : GL (Fin (B.bondDim e)) ℂ)
        (w : EdgeCoeffIdentityWitness A B e Z Z hE), e.1.1 ∈ w.region := by
  classical
  obtain ⟨hE, Z, w, hR, hmem⟩ := exists_staircaseWindowEdgeCoeffIdentityWitness
    (a := 1) (b := 0) (A.transport torusCoordinateSwap) (B.transport torusCoordinateSwap)
    (hA.transportCoordinateSwap A) (hB.transportCoordinateSwap B)
    (hATI.transportCoordinateSwap A) (hBTI.transportCoordinateSwap B)
    (hAB.transport torusCoordinateSwap)
    (fun e ↦ hposA (ManyBody.Edge.map torusCoordinateSwap.symm e))
    (fun e ↦ hposB (ManyBody.Edge.map torusCoordinateSwap.symm e)) hK hL
    (by omega) (by omega) (by omega) hyh hxw
  let eh := horizontalStaircaseReferenceEdge
    (((1 : ℕ) : ZMod height), ((0 : ℕ) : ZMod width)) K L
  let p : TorusVertex width height :=
    (((L - 1 : ℕ) : ZMod width), (1 : ZMod height) + ((K - 1 : ℕ) : ZMod height))
  have hmap : ManyBody.Edge.map torusCoordinateSwap.symm eh = torusUpEdge p := by
    simp only [eh, horizontalStaircaseReferenceEdge, Nat.cast_one, Nat.cast_zero, zero_add,
      torusCoordinateSwap_symm, ManyBody.Edge.map_torusCoordinateSwap_rightEdge]
    rfl
  have hp : p.2.val + 1 < height := by
    have hk : (1 : ZMod height) + ((K - 1 : ℕ) : ZMod height) = (K : ZMod height) := by
      rw [← Nat.cast_one, ← Nat.cast_add]
      congr 1
      omega
    simp only [p, hk, ZMod.val_natCast_of_lt (show K < height by omega)]
    omega
  have hUp := torusUpEdge_endpoints_of_lt (p := p) hp
  have hRight := torusRightEdge_endpoints_of_lt (p := (p.2, p.1)) hp
  have hfirst : torusCoordinateSwap
      (ManyBody.Edge.map torusCoordinateSwap.symm eh).1.1 = eh.1.1 := by
    rw [hmap, hUp.1]
    simpa only [torusCoordinateSwap_apply, eh, horizontalStaircaseReferenceEdge,
      Nat.cast_one, Nat.cast_zero, zero_add, p] using hRight.1.symm
  have hPull := exists_edgeCoeffIdentityWitness_of_transport
    (A := A) (B := B) torusCoordinateSwap (ManyBody.Edge.map torusCoordinateSwap.symm eh)
  generalize hImage : ManyBody.Edge.map torusCoordinateSwap
    (ManyBody.Edge.map torusCoordinateSwap.symm eh) = ehImage at hPull
  rw [ManyBody.Edge.map_map_symm] at hImage
  subst ehImage
  obtain ⟨hE₀, Z₀, w₀, hm₀, _⟩ := hPull hE Z w hfirst hmem
  refine ⟨ManyBody.Edge.map torusCoordinateSwap.symm eh, ?_, hE₀, Z₀, w₀, hm₀⟩
  rw [hmap]
  exact isVerticalTorusEdge_torusUpEdge p

end TNLean.PEPS

end

end CrossTensorTransfer
