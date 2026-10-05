/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusWindowCrossTensorDimensions
import TNLean.PEPS.TorusWindowMult

/-!
# The unscaled staircase coefficient transfer

Equality of the bond dimensions on every edge identifies the two products of dimensions
away from the window boundary. Cancelling their nonzero common value gives the exact
coefficient correspondence for the canonical staircase assignment. Its algebraic laws and
reverse assignment give a region-insertion transfer and an invertible conjugating gauge.

The comparison uses a displayed non-wrapping horizontal staircase with positive window
lengths. Coordinate exchange gives the vertical witness, and translation gives all edges.
The derivation is recorded in `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`.

Source: arXiv:1804.04964, lines 563--586 and 2368--2444 of
`Papers/1804.04964/paper_normal.tex`.
-/

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
    let f : {f : Edge (torusGraph width height) // IsRegionBoundaryEdge W f} :=
      ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A
        (by omega) (by omega) ha0 haw hbh⟩
    regionInsertedCoeff A W f X σ τ = regionInsertedCoeff B W f
      (staircaseCrossTensorVirtualOperation A B hA hB hATI hBTI hAB hposA hposB
        hL hK ha0 haw hbh hxw hyh X) σ τ := by
  have hDim := bondDim_eq_of_normalArcWindows_sameState A B hA hB hATI hBTI hAB
    hposA hposB hL hK hxw hyh
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
    let f : {f : Edge (torusGraph width height) // IsRegionBoundaryEdge W f} :=
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
    let f : {f : Edge (torusGraph width height) // IsRegionBoundaryEdge W f} :=
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
    let f : {f : Edge (torusGraph width height) // IsRegionBoundaryEdge W f} :=
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
