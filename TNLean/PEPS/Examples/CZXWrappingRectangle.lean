/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Examples.CZXWrappingRectangleTransport
import TNLean.PEPS.Examples.CZXRectangleDensity
import TNLean.PEPS.Examples.CZXSymmetry

/-!
# Faithful CZX boundaries of cyclic coordinate rectangles

The region is the actual cyclic product `torusArcRectangle s w h`, at an
arbitrary torus start. Its clockwise crossing bonds and actual contraction
are transported from the bounded origin rectangle. Both coordinate intervals
may cross their seams. The independent boundary spins retain their order;
bottom and left native pairs are reversed exactly as in the bounded theorem.

**Scope restriction:** the periods are at least three and `0 < w < width`,
`0 < h < height`. Full-width cylinders and nonrectangular regions are excluded.
See `docs/paper-gaps/rmp_peps_czx_boundary_chain.tex`.

**Local fixes:** the bond reversal and the printed-matrix MPO normalization
are those of `docs/paper-gaps/rmp_peps_czx_bond_orientation.tex` and
`docs/paper-gaps/mpu_czx_tensor_normalization.tex`.

Source: arXiv:2011.12127, Appendix A, lines 2502–2518 and 2582–2605.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

variable (s : TorusVertex width height) (w h : ℕ)
variable (hw : 0 < w) (hh : 0 < h) (hwp : w < width) (hhp : h < height)

/-- Physical configurations on the cyclic rectangle, pulled back along the
actual vertex translation to the bounded origin rectangle. -/
noncomputable def czxWrappingRectanglePhysicalEquiv :
    RegionPhysicalConfig (d := 16) (torusArcRectangle s w h) ≃
      RegionPhysicalConfig (d := 16)
        (torusContiguousRectangle (width := width) (height := height) 0 0 w h) :=
  (regionPhysicalConfigCongr (d := 16)
    (czxWrappingRectangle_eq_map s w h hw hh hwp hhp)).trans
      (regionPhysicalConfigMapEquiv (d := 16) (translate s.1 s.2)
        (torusContiguousRectangle 0 0 w h)).symm

/-- Actual crossing-bond configurations, pulled back by the translated graph
isomorphism. No boundary support condition is part of this equivalence. -/
noncomputable def czxWrappingRectangleBoundaryEquiv :
    RegionBoundaryConfig (czxPEPS width height) (torusArcRectangle s w h) ≃
      RegionBoundaryConfig (czxPEPS width height) (torusContiguousRectangle 0 0 w h) :=
  (regionBoundaryConfigCongr (A := czxPEPS width height)
    (czxWrappingRectangle_eq_map s w h hw hh hwp hhp)).trans
      (czxWrappingRectangleBoundaryTransport s.1 s.2
        (torusContiguousRectangle 0 0 w h)).symm

/-- Clockwise bijection onto all actual crossing bonds. It is the origin
enumeration followed by the graph translation, so no bonds are lost at seams. -/
noncomputable def czxWrappingRectanglePerimeterEquiv :
    Fin (2 * w + 2 * h) ≃
      {e : Edge (torusGraph width height) // IsRegionBoundaryEdge (torusArcRectangle s w h) e} :=
  (torusRectanglePerimeterEquiv 0 0 w h hw hh (by omega) (by omega) hwp hhp).trans
    ((regionBoundaryEdgeMapEquiv (translate s.1 s.2)
      (torusContiguousRectangle 0 0 w h)).symm.trans
        (Equiv.subtypeEquivRight (fun e =>
          isRegionBoundaryEdge_congr (czxWrappingRectangle_eq_map s w h hw hh hwp hhp).symm e)))

/-- The numbered cyclic crossing bond is the translate of the corresponding
clockwise origin bond, with the native stored endpoints reordered by `Edge.map`. -/
theorem czxWrappingRectanglePerimeterEquiv_apply_val (i : Fin (2 * w + 2 * h)) :
    (czxWrappingRectanglePerimeterEquiv s w h hw hh hwp hhp i).1 =
      Edge.map (translate s.1 s.2) (torusRectanglePerimeterEdge 0 0 w h i) := rfl

/-- Bottom and left pair reversal after clockwise enumeration of every
actual crossing bond. -/
noncomputable def czxWrappingRectangleCoordinatesEquiv :
    RegionBoundaryConfig (czxPEPS width height) (torusArcRectangle s w h) ≃
      (Fin (2 * w + 2 * h) → Fin 4) :=
  (czxWrappingRectangleBoundaryEquiv s w h hw hh hwp hhp).trans
    (czxRectangleCoordinatesEquiv 0 0 w h hw hh (by omega) (by omega) hwp hhp)

/-- The oriented labels read exactly the numbered actual crossing bonds. -/
theorem czxWrappingRectangleCoordinatesEquiv_apply
    (μ : RegionBoundaryConfig (czxPEPS width height) (torusArcRectangle s w h))
    (i : Fin (2 * w + 2 * h)) :
    czxWrappingRectangleCoordinatesEquiv s w h hw hh hwp hhp μ i =
      (if w + h ≤ i.val then czxBondSwap else Equiv.refl _)
        (μ (czxWrappingRectanglePerimeterEquiv s w h hw hh hwp hhp i)) := rfl

private theorem openRegionWeight_congr {R S : Finset (TorusVertex width height)} (he : R = S)
    (μ : RegionBoundaryConfig (czxPEPS width height) R)
    (σ : RegionPhysicalConfig (d := 16) R) :
    openRegionWeight (czxPEPS width height) R μ σ =
      openRegionWeight (czxPEPS width height) S
        (regionBoundaryConfigCongr (A := czxPEPS width height) he μ)
        (regionPhysicalConfigCongr (d := 16) he σ) := by
  subst he
  rfl

/-- The actual contraction of a cyclic rectangle equals the actual bounded
rectangle contraction at its physical and native boundary relabelings. -/
theorem openRegionWeight_czxWrappingRectangle
    (μ : RegionBoundaryConfig (czxPEPS width height) (torusArcRectangle s w h))
    (σ : RegionPhysicalConfig (d := 16) (torusArcRectangle s w h)) :
    openRegionWeight (czxPEPS width height) (torusArcRectangle s w h) μ σ =
      openRegionWeight (czxPEPS width height) (torusContiguousRectangle 0 0 w h)
        (czxWrappingRectangleBoundaryEquiv s w h hw hh hwp hhp μ)
        (czxWrappingRectanglePhysicalEquiv s w h hw hh hwp hhp σ) := by
  rw [openRegionWeight_congr (czxWrappingRectangle_eq_map s w h hw hh hwp hhp)]
  have ht := openRegionWeight_czxWrappingRectangle_translate s.1 s.2
    (torusContiguousRectangle 0 0 w h)
    (czxWrappingRectangleBoundaryEquiv s w h hw hh hwp hhp μ)
    (czxWrappingRectanglePhysicalEquiv s w h hw hh hwp hhp σ)
  simpa only [czxWrappingRectangleBoundaryEquiv, czxWrappingRectanglePhysicalEquiv,
    Equiv.trans_apply, Equiv.apply_symm_apply] using ht

variable [NeZero (2 * w + 2 * h)]

/-- The native actual boundary assignment of a cycle of independent spins. -/
noncomputable def czxWrappingRectangleEffectiveBoundaryConfig
    (c : Fin (2 * w + 2 * h) → Fin 2) :
    RegionBoundaryConfig (czxPEPS width height) (torusArcRectangle s w h) :=
  (czxWrappingRectangleBoundaryEquiv s w h hw hh hwp hhp).symm
    (czxRectangleEffectiveBoundaryConfig 0 0 w h hw hh (by omega) (by omega) hwp hhp c)

/-- Literal columns of the actual open-region contraction. -/
noncomputable def czxWrappingRectangleBoundaryMatrix :
    Matrix (RegionPhysicalConfig (d := 16) (torusArcRectangle s w h))
      (Fin (2 * w + 2 * h) → Fin 2) ℂ :=
  fun σ c => openRegionWeight (czxPEPS width height) (torusArcRectangle s w h)
    (czxWrappingRectangleEffectiveBoundaryConfig s w h hw hh hwp hhp c) σ

/-- The actual faithful boundary matrix is the established bounded matrix
with its physical rows relabeled by the torus translation. -/
theorem czxWrappingRectangleBoundaryMatrix_apply
    (σ : RegionPhysicalConfig (d := 16) (torusArcRectangle s w h))
    (c : Fin (2 * w + 2 * h) → Fin 2) :
    czxWrappingRectangleBoundaryMatrix s w h hw hh hwp hhp σ c =
      czxRectangleBoundaryMatrix 0 0 w h hw hh (by omega) (by omega) hwp hhp
        (czxWrappingRectanglePhysicalEquiv s w h hw hh hwp hhp σ) c := by
  rw [czxWrappingRectangleBoundaryMatrix,
    openRegionWeight_czxWrappingRectangle s w h hw hh hwp hhp]
  simp only [czxWrappingRectangleEffectiveBoundaryConfig, Equiv.apply_symm_apply,
    czxRectangleBoundaryMatrix]

/-- Distinct effective spin configurations remain distinct native assignments. -/
theorem czxWrappingRectangleEffectiveBoundaryConfig_injective :
    Function.Injective (czxWrappingRectangleEffectiveBoundaryConfig s w h hw hh hwp hhp) :=
  (czxWrappingRectangleBoundaryEquiv s w h hw hh hwp hhp).symm.injective.comp
    (czxRectangleEffectiveBoundaryConfig_injective 0 0 w h hw hh
      (by omega) (by omega) hwp hhp)

/-- Every independent boundary spin assignment extends to actual torus
plaquette bits, including at either seam. -/
theorem exists_czxWrappingRectanglePlaquetteBoundary
    (c : Fin (2 * w + 2 * h) → Fin 2) :
    ∃ q : TorusVertex width height → Fin 2,
      (fun e => czxPlaquetteBondConfig q e.1) =
        czxWrappingRectangleEffectiveBoundaryConfig s w h hw hh hwp hhp c := by
  obtain ⟨q, hq⟩ := exists_czxRectanglePlaquetteBoundary 0 0 w h hw hh
    (by omega) (by omega) hwp hhp c
  refine ⟨fun v => q ((translate s.1 s.2).symm v), ?_⟩
  apply (czxWrappingRectangleBoundaryEquiv s w h hw hh hwp hhp).injective
  rw [czxWrappingRectangleEffectiveBoundaryConfig, Equiv.apply_symm_apply, ← hq]
  funext e
  change czxPlaquetteBondConfig (fun v => q ((translate s.1 s.2).symm v))
    (Edge.map (translate s.1 s.2) e.1) = czxPlaquetteBondConfig q e.1
  exact czxWrappingRectangle_plaquetteBond_translate s.1 s.2 q e.1

/-- The physical boundary map is faithful for arbitrary cyclic starts. -/
theorem czxWrappingRectangleBoundaryMatrix_mulVec_injective :
    Function.Injective (czxWrappingRectangleBoundaryMatrix s w h hw hh hwp hhp).mulVec := by
  intro f g hfg
  apply czxRectangleBoundaryMatrix_mulVec_injective 0 0 w h hw hh
    (by omega) (by omega) hwp hhp
  funext σ
  have he := congrFun hfg ((czxWrappingRectanglePhysicalEquiv s w h hw hh hwp hhp).symm σ)
  simpa only [Matrix.mulVec, dotProduct, czxWrappingRectangleBoundaryMatrix_apply,
    Equiv.apply_symm_apply] using he

omit [NeZero (2 * w + 2 * h)] in
/-- The physical image of the actual open contraction is the translated
bounded image, under an explicitly bijective relabeling of physical states. -/
theorem range_openRegionMap_czxWrappingRectangle_transport :
    (openRegionMap (czxPEPS width height) (torusArcRectangle s w h)).range =
      ((openRegionMap (czxPEPS width height)
        (torusContiguousRectangle 0 0 w h)).range).map
          (LinearEquiv.funCongrLeft ℂ ℂ
            (czxWrappingRectanglePhysicalEquiv s w h hw hh hwp hhp)).toLinearMap := by
  classical
  let E := czxWrappingRectanglePhysicalEquiv s w h hw hh hwp hhp
  let B := czxWrappingRectangleBoundaryEquiv s w h hw hh hwp hhp
  have hm : openRegionMap (czxPEPS width height) (torusArcRectangle s w h) =
      (LinearEquiv.funCongrLeft ℂ ℂ E).toLinearMap.comp
        ((openRegionMap (czxPEPS width height) (torusContiguousRectangle 0 0 w h)).comp
          (LinearEquiv.funCongrLeft ℂ ℂ B.symm).toLinearMap) := by
    ext f σ
    simp only [openRegionMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
    rw [← B.symm.sum_comp]
    apply Finset.sum_congr rfl
    intro μ _
    rw [openRegionWeight_czxWrappingRectangle s w h hw hh hwp hhp]
    simp only [B, Equiv.apply_symm_apply, E]
  rw [hm, LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _
    (LinearEquiv.range _)]

/-- The actual open-region image is precisely the span of the faithful
effective spin columns. -/
theorem range_openRegionMap_czxWrappingRectangle :
    (openRegionMap (czxPEPS width height) (torusArcRectangle s w h)).range =
      Submodule.span ℂ (Set.range (fun c =>
        fun σ => czxWrappingRectangleBoundaryMatrix s w h hw hh hwp hhp σ c)) := by
  rw [range_openRegionMap_czxWrappingRectangle_transport s w h hw hh hwp hhp,
    range_openRegionMap_czxRectangle 0 0 w h hw hh (by omega) (by omega) hwp hhp,
    Submodule.map_span, ← Set.range_comp]
  congr 2
  funext c σ
  exact (czxWrappingRectangleBoundaryMatrix_apply s w h hw hh hwp hhp σ c).symm

include hw hh hwp hhp in
/-- One independent effective qubit per clockwise crossing bond. -/
theorem finrank_range_openRegionMap_czxWrappingRectangle :
    Module.finrank ℂ
      (openRegionMap (czxPEPS width height) (torusArcRectangle s w h)).range =
        2 ^ (2 * w + 2 * h) := by
  rw [range_openRegionMap_czxWrappingRectangle_transport s w h hw hh hwp hhp,
    LinearEquiv.finrank_map_eq]
  exact finrank_range_openRegionMap_czxRectangle 0 0 w h hw hh
    (by omega) (by omega) hwp hhp

/-- Actual vertices in the cyclic rectangle in translated origin order. -/
noncomputable def czxWrappingRectangleVertexEquiv :
    {v : TorusVertex width height // v ∈ torusContiguousRectangle 0 0 w h} ≃
      {v : TorusVertex width height // v ∈ torusArcRectangle s w h} :=
  (Finset.equivMap (translate s.1 s.2).toEquiv.toEmbedding
    (torusContiguousRectangle 0 0 w h)).trans
      (Equiv.subtypeEquivRight fun _ => by
        rw [czxWrappingRectangle_eq_map s w h hw hh hwp hhp]
        rfl)

omit [NeZero (2 * w + 2 * h)] in
/-- The physical relabeling evaluates at the actual translated vertex. -/
theorem czxWrappingRectanglePhysicalEquiv_apply
    (σ : RegionPhysicalConfig (d := 16) (torusArcRectangle s w h))
    (v : {v : TorusVertex width height // v ∈ torusContiguousRectangle 0 0 w h}) :
    czxWrappingRectanglePhysicalEquiv s w h hw hh hwp hhp σ v =
      σ (czxWrappingRectangleVertexEquiv s w h hw hh hwp hhp v) := by
  simp only [czxWrappingRectanglePhysicalEquiv, regionPhysicalConfigCongr,
    Equiv.piCongrLeft', regionPhysicalConfigMapEquiv, eq_rec_constant,
    Equiv.symm_mk, Equiv.trans_apply, Equiv.coe_fn_mk, czxWrappingRectangleVertexEquiv]
  apply congrArg σ
  apply Subtype.ext
  rfl

omit [NeZero (2 * w + 2 * h)] in
private theorem physicalProductMatrix_translate
    (σ τ : RegionPhysicalConfig (d := 16) (torusArcRectangle s w h)) :
    regionPhysicalProductMatrix (torusArcRectangle s w h) (fun _ => czxOnSite) σ τ =
      regionPhysicalProductMatrix (torusContiguousRectangle 0 0 w h) (fun _ => czxOnSite)
        (czxWrappingRectanglePhysicalEquiv s w h hw hh hwp hhp σ)
        (czxWrappingRectanglePhysicalEquiv s w h hw hh hwp hhp τ) := by
  unfold regionPhysicalProductMatrix
  symm
  refine Fintype.prod_equiv
    (czxWrappingRectangleVertexEquiv s w h hw hh hwp hhp) _ _ ?_
  intro v
  simp only [czxWrappingRectanglePhysicalEquiv_apply]

/-- The review's printed CZX MPO is the physical symmetry on the faithful
actual image of every positive proper cyclic coordinate rectangle. Its even
perimeter preserves the bounded theorem's printed-matrix normalization. -/
theorem regionPhysicalProductMatrix_czxWrappingRectangleBoundaryMatrix_review :
    regionPhysicalProductMatrix (torusArcRectangle s w h) (fun _ => czxOnSite) *
        czxWrappingRectangleBoundaryMatrix s w h hw hh hwp hhp =
      czxWrappingRectangleBoundaryMatrix s w h hw hh hwp hhp *
        MPOTensor.mpo CZXCompression.reviewCZXTensor (2 * w + 2 * h) := by
  classical
  ext σ c
  let E := czxWrappingRectanglePhysicalEquiv s w h hw hh hwp hhp
  have he := congrFun (congrFun
    (regionPhysicalProductMatrix_czxRectangleBoundaryMatrix_review
      0 0 w h hw hh (by omega) (by omega) hwp hhp) (E σ)) c
  change (∑ τ, regionPhysicalProductMatrix (torusContiguousRectangle 0 0 w h)
    (fun _ => czxOnSite) (E σ) τ *
      czxRectangleBoundaryMatrix 0 0 w h hw hh (by omega) (by omega) hwp hhp τ c) = _ at he
  simp only [Matrix.mul_apply] at he ⊢
  rw [← E.symm.sum_comp]
  simpa only [physicalProductMatrix_translate s w h hw hh hwp hhp,
    czxWrappingRectangleBoundaryMatrix_apply, E, Equiv.apply_symm_apply] using he

include hw hh hwp hhp in
/-- The actual closed-state reduced density has exactly the physical
open-region image as its support. The translated plaquette extensions select
literal closed-state slices through the general complement-slice theorem. -/
theorem range_regionReducedDensity_czxWrappingRectangle :
    (Matrix.mulVecLin (regionReducedDensity (czxPEPS width height)
      (torusArcRectangle s w h))).range =
        (openRegionMap (czxPEPS width height) (torusArcRectangle s w h)).range := by
  classical
  apply le_antisymm (range_regionReducedDensity_le _ _)
  change (openRegionMap (czxPEPS width height) (torusArcRectangle s w h)).range ≤ _
  rw [range_openRegionMap_czxWrappingRectangle s w h hw hh hwp hhp]
  apply Submodule.span_le.mpr
  rintro _ ⟨c, rfl⟩
  obtain ⟨q, hq⟩ := exists_czxWrappingRectanglePlaquetteBoundary s w h hw hh hwp hhp c
  rw [range_regionReducedDensity_eq_cutRange]
  refine ⟨Pi.single (fun v => czxPlaquettePhysical q v.1) 1, ?_⟩
  let M : Matrix (RegionPhysicalConfig (d := 16) (torusArcRectangle s w h))
      (RegionPhysicalConfig (d := 16) (Finset.univ \ torusArcRectangle s w h)) ℂ :=
    fun σ τ => stateCoeff (czxPEPS width height) (assembleRegionσ (torusArcRectangle s w h) σ τ)
  change M *ᵥ Pi.single (fun v => czxPlaquettePhysical q v.1) 1 = _
  rw [Matrix.mulVec_single_one]
  funext σ
  change stateCoeff (czxPEPS width height)
    (assembleRegionσ (torusArcRectangle s w h) σ (fun v => czxPlaquettePhysical q v.1)) = _
  rw [stateCoeff_czxPlaquetteComplement]
  exact congrArg (fun μ => openRegionWeight (czxPEPS width height)
    (torusArcRectangle s w h) μ σ) hq

include hw hh hwp hhp in
/-- Rank of the actual reduced density. No flat-spectrum assertion is used. -/
theorem rank_regionReducedDensity_czxWrappingRectangle :
    (regionReducedDensity (czxPEPS width height) (torusArcRectangle s w h)).rank =
      2 ^ (2 * w + 2 * h) := by
  change Module.finrank ℂ (Matrix.mulVecLin _).range = _
  rw [range_regionReducedDensity_czxWrappingRectangle s w h hw hh hwp hhp]
  exact finrank_range_openRegionMap_czxWrappingRectangle s w h hw hh hwp hhp

end TNLean.PEPS
