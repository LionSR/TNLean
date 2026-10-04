/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Examples.CZXRectangleSupport
import TNLean.PEPS.Examples.CZXRegionSymmetry
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Effective plaquette spins of the actual CZX rectangle map

Clockwise boundary coordinates identify the supported virtual configurations
with one effective qubit per boundary plaquette. The actual region contraction
retains the source's bottom/left bond orientation.

**Scope restriction (rectangular region):** both torus periods are at least
three and the region is a positive proper bounded coordinate rectangle.
Normalized reduced-density and nonrectangular-region assertions remain open;
see `docs/paper-gaps/rmp_peps_czx_boundary_chain.tex`.

## References

- [arXiv:1106.4752](https://arxiv.org/abs/1106.4752), CZX model boundary, lines 330–345.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

variable (xStart yStart w h : ℕ) (hw : 0 < w) (hh : 0 < h)
variable (hx : xStart + w ≤ width) (hy : yStart + h ≤ height)
variable (hwp : w < width) (hhp : h < height)

/-- Clockwise ordering and bottom/left pair reversal are a bijective change
of coordinates on the actual rectangle crossing bonds. -/
noncomputable def czxRectangleCoordinatesEquiv :
    RegionBoundaryConfig (czxPEPS width height)
      (torusContiguousRectangle xStart yStart w h) ≃ (Fin (2 * w + 2 * h) → Fin 4) :=
  (Equiv.arrowCongr
    (torusRectangleBoundaryEquiv xStart yStart w h hw hh hx hy hwp hhp).symm
    (Equiv.refl (Fin 4))).trans
      (Equiv.piCongrRight fun i => if w + h ≤ i.val then czxBondSwap else Equiv.refl _)

@[simp] theorem czxRectangleCoordinatesEquiv_apply
    (μ : RegionBoundaryConfig (czxPEPS width height)
      (torusContiguousRectangle xStart yStart w h)) :
    czxRectangleCoordinatesEquiv xStart yStart w h hw hh hx hy hwp hhp μ =
      czxRectangleBoundaryLabels xStart yStart w h hw hh hx hy hwp hhp μ := by
  change ({e : Edge (torusGraph width height) //
    IsRegionBoundaryEdge (torusContiguousRectangle xStart yStart w h) e} → Fin 4) at μ
  funext i
  change (if w + h ≤ i.val then czxBondSwap else Equiv.refl (Fin 4))
      (μ (torusRectangleBoundaryEquiv xStart yStart w h hw hh hx hy hwp hhp i)) = _
  unfold czxRectangleBoundaryLabels
  by_cases hi : w + h ≤ i.val <;> simp only [hi, ite_true, ite_false, Equiv.refl_apply]

variable [NeZero (2 * w + 2 * h)]

/-- The native virtual boundary configuration carrying a given cycle of
independent plaquette spins. -/
noncomputable def czxRectangleEffectiveBoundaryConfig
    (c : Fin (2 * w + 2 * h) → Fin 2) :
    RegionBoundaryConfig (czxPEPS width height)
      (torusContiguousRectangle xStart yStart w h) :=
  (czxRectangleCoordinatesEquiv xStart yStart w h hw hh hx hy hwp hhp).symm
    (czxBoundaryLegs (2 * w + 2 * h) c)

/-- Effective boundary columns are literal columns of the actual open-region
map, with no exterior-bond summation and no assumed support formula. -/
noncomputable def czxRectangleBoundaryMatrix :
    Matrix (RegionPhysicalConfig (d := 16)
      (torusContiguousRectangle (width := width) (height := height) xStart yStart w h))
      (Fin (2 * w + 2 * h) → Fin 2) ℂ :=
  fun σ c => openRegionWeight (czxPEPS width height)
    (torusContiguousRectangle xStart yStart w h)
    (czxRectangleEffectiveBoundaryConfig xStart yStart w h hw hh hx hy hwp hhp c) σ

/-- Each effective boundary spin configuration has one distinct native
crossing-bond configuration. -/
theorem czxRectangleEffectiveBoundaryConfig_injective :
    Function.Injective (czxRectangleEffectiveBoundaryConfig
      xStart yStart w h hw hh hx hy hwp hhp) :=
  (czxRectangleCoordinatesEquiv xStart yStart w h hw hh hx hy hwp hhp).symm.injective.comp
    (czxBoundaryLegs_injective (2 * w + 2 * h))

/-- Plaquette-copying configurations read on the rectangle boundary give the
adjacent pair of the actual consecutive perimeter corners. -/
theorem czxRectangleBoundaryLabels_plaquette (q : TorusVertex width height → Fin 2)
    (i : Fin (2 * w + 2 * h)) :
    czxRectangleBoundaryLabels xStart yStart w h hw hh hx hy hwp hhp
      (fun e => czxPlaquetteBondConfig q e.1) i =
      czxBond (q (torusRectanglePerimeterCorner xStart yStart w h i),
        q (torusRectanglePerimeterCorner xStart yStart w h (i + 1))) := by
  change (if w + h ≤ i.val then
    czxBondSwap (czxPlaquetteBondConfig q (torusRectanglePerimeterEdge xStart yStart w h i))
    else czxPlaquetteBondConfig q (torusRectanglePerimeterEdge xStart yStart w h i)) = _
  simp only [torusRectanglePerimeterEdge, czxPlaquetteBondConfig, Function.comp_apply,
    Equiv.symm_apply_apply, torusRectanglePerimeterCorner]
  rw [← rectanglePerimeterEnd_eq_corner_add_one w h hw hh i]
  unfold torusRectanglePerimeterCode rectanglePerimeterCorner rectanglePerimeterEnd
  by_cases ht : i.val < w <;> by_cases hr : i.val < w + h <;>
    by_cases hb : i.val < 2 * w + h <;> by_cases ho : w + h ≤ i.val <;> try omega
  all_goals
    simp only [ht, hr, hb, ho, ite_true, ite_false, Sum.elim_inl, Sum.elim_inr,
      czxBondSwap_czxBond, Nat.cast_add, Nat.cast_zero, Nat.cast_one, add_zero,
      sub_add_cancel]
  all_goals
    apply congrArg czxBond
    apply Prod.ext <;> apply congrArg q <;> apply Prod.ext
  all_goals
    simp only [← Nat.cast_add_one, ← Nat.cast_add]
  all_goals first | rfl | (congr 1; omega)

/-- Every effective plaquette-spin column has a physical basis coefficient
that selects exactly that column. Hence the effective boundary action is faithful. -/
theorem exists_czxRectangleBoundaryMatrix_selector
    (c : Fin (2 * w + 2 * h) → Fin 2) :
    ∃ σ, ∀ c', czxRectangleBoundaryMatrix xStart yStart w h hw hh hx hy hwp hhp σ c' =
      if c' = c then 1 else 0 := by
  classical
  let corner := torusRectanglePerimeterCorner (width := width) (height := height)
    xStart yStart w h
  have hcorner : Function.Injective corner :=
    torusRectanglePerimeterCorner_injective xStart yStart w h hw hh hwp hhp
  let q := Function.extend corner c (fun _ => (0 : Fin 2))
  have hq (i) : q (corner i) = c i := hcorner.extend_apply c (fun _ => 0) i
  let R : Finset (TorusVertex width height) := torusContiguousRectangle xStart yStart w h
  let μ : RegionBoundaryConfig (czxPEPS width height) R :=
    fun e => czxPlaquetteBondConfig q e.1
  have hμ : μ = czxRectangleEffectiveBoundaryConfig xStart yStart w h hw hh hx hy hwp hhp c := by
    apply (czxRectangleCoordinatesEquiv xStart yStart w h hw hh hx hy hwp hhp).injective
    rw [czxRectangleEffectiveBoundaryConfig, Equiv.apply_symm_apply,
      czxRectangleCoordinatesEquiv_apply]
    funext i
    have hi := czxRectangleBoundaryLabels_plaquette xStart yStart w h hw hh hx hy hwp hhp q i
    exact hi.trans (by simp only [← hq, czxBoundaryLegs]; rfl)
  let σ : RegionPhysicalConfig (d := 16) R := fun v => czxPlaquettePhysical q v.1
  have hself : openRegionWeight (czxPEPS width height) R
      (czxRectangleEffectiveBoundaryConfig xStart yStart w h hw hh hx hy hwp hhp c) σ = 1 := by
    rw [← hμ]
    exact openRegionWeight_czxPlaquettePhysical R q
  refine ⟨σ, fun c' => ?_⟩
  by_cases hc : c' = c
  · simpa [hc, czxRectangleBoundaryMatrix] using hself
  · have hne : czxRectangleEffectiveBoundaryConfig xStart yStart w h hw hh hx hy hwp hhp c ≠
        czxRectangleEffectiveBoundaryConfig xStart yStart w h hw hh hx hy hwp hhp c' :=
      fun he => hc ((czxRectangleEffectiveBoundaryConfig_injective
        xStart yStart w h hw hh hx hy hwp hhp) he).symm
    have hz := openRegionWeight_czxPEPS_disjoint R _ _ hne σ
    rw [hself, star_one, one_mul] at hz
    simpa only [czxRectangleBoundaryMatrix, hc, ite_false] using hz

/-- The actual rectangle contraction is injective on its effective boundary
plaquette spins. This excludes a vacuous symmetry intertwiner. -/
theorem czxRectangleBoundaryMatrix_mulVec_injective :
    Function.Injective
      (czxRectangleBoundaryMatrix xStart yStart w h hw hh hx hy hwp hhp).mulVec := by
  classical
  intro f g hfg
  funext c
  obtain ⟨σ, hσ⟩ := exists_czxRectangleBoundaryMatrix_selector
    xStart yStart w h hw hh hx hy hwp hhp c
  have he := congrFun hfg σ
  simpa [Matrix.mulVec, dotProduct, hσ] using he

/-- The independent effective boundary columns span exactly the image of the
actual open-region map. This is a physical support identification. -/
theorem range_openRegionMap_czxRectangle :
    LinearMap.range (openRegionMap (czxPEPS width height)
        (torusContiguousRectangle xStart yStart w h)) =
      Submodule.span ℂ (Set.range (fun c =>
        fun σ => czxRectangleBoundaryMatrix xStart yStart w h hw hh hx hy hwp hhp σ c)) := by
  classical
  rw [openRegionMap, Fintype.range_linearCombination]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨μ, rfl⟩
    by_cases hz : openRegionWeight (czxPEPS width height)
        (torusContiguousRectangle xStart yStart w h) μ = 0
    · simp [hz]
    · obtain ⟨σ, hσ⟩ := Function.ne_iff.mp hz
      obtain ⟨c, hc⟩ := czxRectangleBoundaryLabels_mem_range_of_openRegionWeight_ne_zero
        xStart yStart w h hw hh hx hy hwp hhp μ σ hσ
      have hμ : μ = czxRectangleEffectiveBoundaryConfig
          xStart yStart w h hw hh hx hy hwp hhp c := by
        apply (czxRectangleCoordinatesEquiv xStart yStart w h hw hh hx hy hwp hhp).injective
        rw [czxRectangleCoordinatesEquiv_apply, czxRectangleEffectiveBoundaryConfig,
          Equiv.apply_symm_apply]
        exact hc
      rw [hμ]
      exact Submodule.subset_span ⟨c, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨c, rfl⟩
    exact Submodule.subset_span
      ⟨czxRectangleEffectiveBoundaryConfig xStart yStart w h hw hh hx hy hwp hhp c, rfl⟩

include hw hh hx hy hwp hhp in
/-- The actual CZX rectangle image has one independent qubit per boundary
plaquette, hence dimension two to the lattice perimeter. -/
theorem finrank_range_openRegionMap_czxRectangle :
    Module.finrank ℂ (LinearMap.range (openRegionMap (czxPEPS width height)
      (torusContiguousRectangle xStart yStart w h))) = 2 ^ (2 * w + 2 * h) := by
  classical
  rw [range_openRegionMap_czxRectangle xStart yStart w h hw hh hx hy hwp hhp]
  have hlin := Matrix.mulVec_injective_iff.mp
    (czxRectangleBoundaryMatrix_mulVec_injective xStart yStart w h hw hh hx hy hwp hhp)
  have hcol : (czxRectangleBoundaryMatrix xStart yStart w h hw hh hx hy hwp hhp).col =
      (fun c σ => czxRectangleBoundaryMatrix xStart yStart w h hw hh hx hy hwp hhp σ c) := rfl
  rw [hcol] at hlin
  simpa using finrank_span_eq_card hlin

omit [NeZero (2 * w + 2 * h)] in
private theorem czxRectangleCoordinatesEquiv_flip
    (μ : RegionBoundaryConfig (czxPEPS width height)
      (torusContiguousRectangle xStart yStart w h)) :
    czxRectangleCoordinatesEquiv xStart yStart w h hw hh hx hy hwp hhp
      (czxRegionBoundaryFlip (torusContiguousRectangle xStart yStart w h) μ) =
      fun i => czxLegFlip (czxRectangleCoordinatesEquiv
        xStart yStart w h hw hh hx hy hwp hhp μ i) := by
  change ({e : Edge (torusGraph width height) //
    IsRegionBoundaryEdge (torusContiguousRectangle xStart yStart w h) e} → Fin 4) at μ
  funext i
  change (if w + h ≤ i.val then czxBondSwap else Equiv.refl (Fin 4))
      (czxLegFlip (μ (torusRectangleBoundaryEquiv xStart yStart w h hw hh hx hy hwp hhp i))) =
    czxLegFlip ((if w + h ≤ i.val then czxBondSwap else Equiv.refl (Fin 4))
      (μ (torusRectangleBoundaryEquiv xStart yStart w h hw hh hx hy hwp hhp i)))
  by_cases hi : w + h ≤ i.val
  · simp only [hi, ite_true]
    exact (czxLegFlip_swap _).symm
  · simp only [hi, ite_false, Equiv.refl_apply]

omit [NeZero (2 * w + 2 * h)] in
private theorem czxRectangleBoundaryPhase_coordinates
    (μ : RegionBoundaryConfig (czxPEPS width height)
      (torusContiguousRectangle xStart yStart w h)) :
    czxRegionBoundaryPhase (torusContiguousRectangle xStart yStart w h) μ =
      ∏ i, czxLegPhase (czxRectangleCoordinatesEquiv
        xStart yStart w h hw hh hx hy hwp hhp μ i) := by
  classical
  let e := torusRectangleBoundaryEquiv xStart yStart w h hw hh hx hy hwp hhp
  calc
    _ = ∏ i, czxLegPhase (μ (e i)) :=
      (Fintype.prod_equiv e _ _ (fun _ => rfl)).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      change czxLegPhase (μ (e i)) =
        czxLegPhase ((if w + h ≤ i.val then czxBondSwap else Equiv.refl (Fin 4)) (μ (e i)))
      by_cases hi : w + h ≤ i.val
      · simp only [hi, ite_true]
        exact (czxLegPhase_swap _).symm
      · simp only [hi, ite_false]
        rfl

private theorem czxRectangleEffectiveBoundaryConfig_flip
    (c : Fin (2 * w + 2 * h) → Fin 2) :
    czxRegionBoundaryFlip (torusContiguousRectangle xStart yStart w h)
        (czxRectangleEffectiveBoundaryConfig xStart yStart w h hw hh hx hy hwp hhp c) =
      czxRectangleEffectiveBoundaryConfig xStart yStart w h hw hh hx hy hwp hhp
        (fun i => (c i).rev) := by
  apply (czxRectangleCoordinatesEquiv xStart yStart w h hw hh hx hy hwp hhp).injective
  rw [czxRectangleCoordinatesEquiv_flip]
  simp only [czxRectangleEffectiveBoundaryConfig, Equiv.apply_symm_apply]
  funext i
  simp [czxBoundaryLegs]

/-- On the actual rectangle image the physical symmetry flips each effective
plaquette spin, with one controlled phase on each adjacent pair in the cycle. -/
theorem regionPhysicalMap_czxRectangleBoundaryMatrix_column
    (c : Fin (2 * w + 2 * h) → Fin 2) :
    regionPhysicalMap (torusContiguousRectangle xStart yStart w h) (fun _ => czxOnSite)
        (fun σ => czxRectangleBoundaryMatrix xStart yStart w h hw hh hx hy hwp hhp σ c) =
      (∏ i, czxLegPhase (czxBoundaryLegs (2 * w + 2 * h) c i)) •
        (fun σ => czxRectangleBoundaryMatrix xStart yStart w h hw hh hx hy hwp hhp
          σ (fun i => (c i).rev)) := by
  have hphys := regionPhysicalMap_czxOnSite_openRegionWeight
    (torusContiguousRectangle xStart yStart w h)
    (czxRectangleEffectiveBoundaryConfig xStart yStart w h hw hh hx hy hwp hhp c)
  rw [czxRectangleBoundaryPhase_coordinates xStart yStart w h hw hh hx hy hwp hhp,
    czxRectangleEffectiveBoundaryConfig_flip xStart yStart w h hw hh hx hy hwp hhp] at hphys
  simpa only [czxRectangleBoundaryMatrix, czxRectangleEffectiveBoundaryConfig,
    Equiv.apply_symm_apply] using hphys

end TNLean.PEPS
