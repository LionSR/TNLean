/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusWindowCrossTensorAlgebra
import QICLean.Algebra.MatrixAlgEquiv

/-!
# The gauge on a staircase bond

The staircase algebra isomorphism identifies the dimensions of the displayed bond.
Skolem--Noether then expresses its virtual assignment as conjugation by an invertible
matrix. Substitution gives the corresponding coefficient identity, with the non-boundary-bond
multiplicities retained.

**Scope restriction (displayed horizontal staircase, `L, K ≥ 2`):** These results use the
non-wrapping horizontal staircase. The rotation and translation argument needed to identify
all bond dimensions, and hence cancel these multiplicities, remains recorded in
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`.

Source: arXiv:1804.04964, the dimension and Skolem--Noether argument at lines 582--586
and the two-dimensional reduction at lines 2368--2444 of
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
variable (hL : 2 ≤ L) (hK : 2 ≤ K) (ha0 : 1 ≤ a)
variable (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
variable (hxw : 2 * L + 1 ≤ width) (hyh : 2 * K + 1 ≤ height)

include hA hB hATI hBTI hAB hposA hposB hL hK ha0 haw hbh hxw hyh in
/-- Equality of the full matrix algebras identifies the displayed staircase bond dimensions.

Source: arXiv:1804.04964, the dimension argument at lines 582--584. -/
theorem staircaseCrossTensor_bondDim_eq :
    A.bondDim (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K) =
      B.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K) :=
  Matrix.matrixAlgEquiv_fin_eq (staircaseCrossTensorAlgEquiv A B hA hB hATI hBTI hAB
    hposA hposB hL hK ha0 haw hbh hxw hyh)

include hA hB hATI hBTI hAB hposA hposB hL hK ha0 haw hbh hxw hyh in
/-- The displayed staircase bond admits an invertible conjugating gauge. The inserted
coefficient identity retains the non-boundary-bond multiplicities of both tensors.

Source: arXiv:1804.04964, the Skolem--Noether argument at lines 582--586 and its
two-dimensional reduction at lines 2368--2444. -/
theorem exists_staircaseWindowConjCoeffIdentity_normalized :
    let W := horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K
    let f : {f : Edge (torusGraph width height) // IsRegionBoundaryEdge W f} :=
      ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A
        (by omega) (by omega) ha0 haw hbh⟩
    ∃ (hE : A.bondDim f.1 = B.bondDim f.1) (Z : GL (Fin (B.bondDim f.1)) ℂ),
      ∀ (X : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
        (σ : RegionPhysicalConfig (V := TorusVertex width height) (d := d) W)
        (τ : RegionPhysicalConfig (V := TorusVertex width height) (d := d) (Finset.univ \ W)),
        (regionInteriorBondProd B W : ℂ) * regionInsertedCoeff A W f X σ τ =
          (regionInteriorBondProd A W : ℂ) * regionInsertedCoeff B W f
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
  simpa only [hZ'] using staircaseCrossTensorVirtualOperation_normalized_coeff
    A B hA hB hATI hBTI hAB hposA hposB hL hK ha0 haw hbh hxw hyh X σ τ

end TNLean.PEPS
