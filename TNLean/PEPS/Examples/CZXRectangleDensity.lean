/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Examples.CZXRectangleMap
import TNLean.PEPS.ParentHamiltonian.RegionReducedDensity

/-!
# Actual reduced-density support of a CZX rectangle

The closed-state cut has every effective boundary column among its physical
slices. Consequently the actual unnormalized reduced density has exactly the
open-region image as its support. No flat-spectrum or entropy claim is used.

## References

- [arXiv:1106.4752](https://arxiv.org/abs/1106.4752), Section IV, CZX boundary.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

noncomputable section

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

open Classical in
/-- A global plaquette configuration on the complement selects exactly its
crossing-bond labels in the actual incident-only open contraction. -/
theorem openRegionWeight_czxPlaquetteComplement
    (R : Finset (TorusVertex width height)) (q : TorusVertex width height → Fin 2)
    (μ : RegionBoundaryConfig (czxPEPS width height) R) :
    openRegionWeight (czxPEPS width height) (Finset.univ \ R)
      (regionComplementBoundaryConfig (czxPEPS width height) R μ)
      (fun v => czxPlaquettePhysical q v.1) =
      if μ = (fun e => czxPlaquetteBondConfig q e.1) then 1 else 0 := by
  classical
  let ν : RegionBoundaryConfig (czxPEPS width height) R :=
    fun e => czxPlaquetteBondConfig q e.1
  have hself := openRegionWeight_czxPlaquettePhysical (Finset.univ \ R) q
  have hν : regionComplementBoundaryConfig (czxPEPS width height) R ν =
      (fun e => czxPlaquetteBondConfig q e.1) := rfl
  rw [← hν] at hself
  by_cases he : μ = ν
  · simpa only [show (fun e => czxPlaquetteBondConfig q e.1) = ν from rfl,
      he, ite_true] using hself
  · have hne : regionComplementBoundaryConfig (czxPEPS width height) R ν ≠
        regionComplementBoundaryConfig (czxPEPS width height) R μ := by
      intro hh
      apply he
      funext e
      have heq := congrFun hh (regionBoundaryEdgeToCompl R e)
      change μ e = ν e
      exact heq.symm
    have hz := openRegionWeight_czxPEPS_disjoint (Finset.univ \ R) _ _ hne
      (fun v => czxPlaquettePhysical q v.1)
    rw [hself, star_one, one_mul] at hz
    simpa only [show (fun e => czxPlaquetteBondConfig q e.1) = ν from rfl,
      he, ite_false] using hz

/-- A fixed complement plaquette configuration turns the actual closed-state
cut into the corresponding open-region boundary column. -/
theorem stateCoeff_czxPlaquetteComplement
    (R : Finset (TorusVertex width height)) (q : TorusVertex width height → Fin 2)
    (σ : RegionPhysicalConfig (d := 16) R) :
    stateCoeff (czxPEPS width height)
      (assembleRegionσ R σ (fun v => czxPlaquettePhysical q v.1)) =
      openRegionWeight (czxPEPS width height) R
        (fun e => czxPlaquetteBondConfig q e.1) σ := by
  classical
  let ν : RegionBoundaryConfig (czxPEPS width height) R :=
    fun e => czxPlaquetteBondConfig q e.1
  rw [stateCoeff_eq_openRegionComplement_unconditional, Finset.sum_eq_single ν]
  · have h := openRegionWeight_czxPlaquetteComplement R q ν
    have he : ν = (fun e => czxPlaquetteBondConfig q e.1) := rfl
    rw [ite_eq_left he] at h
    rw [h, mul_one]
  · intro μ _ hμ
    have h := openRegionWeight_czxPlaquetteComplement R q μ
    have he : μ ≠ (fun e => czxPlaquetteBondConfig q e.1) := hμ
    rw [ite_eq_right he] at h
    rw [h, mul_zero]
  · simp

variable (xStart yStart w h : ℕ) (hw : 0 < w) (hh : 0 < h)
variable (hx : xStart + w ≤ width) (hy : yStart + h ≤ height)
variable (hwp : w < width) (hhp : h < height) [NeZero (2 * w + 2 * h)]

include hw hh hx hy hwp hhp in
/-- The actual CZX reduced density on a positive proper rectangle has precisely
the physical open-region image as its support. -/
theorem range_regionReducedDensity_czxRectangle :
    (Matrix.mulVecLin (regionReducedDensity (czxPEPS width height)
      (torusContiguousRectangle xStart yStart w h))).range =
    (openRegionMap (czxPEPS width height)
      (torusContiguousRectangle xStart yStart w h)).range := by
  classical
  apply le_antisymm
  · exact range_regionReducedDensity_le _ _
  · rw [range_openRegionMap_czxRectangle xStart yStart w h hw hh hx hy hwp hhp]
    apply Submodule.span_le.mpr
    rintro _ ⟨c, rfl⟩
    obtain ⟨q, hq⟩ := exists_czxRectanglePlaquetteBoundary
      xStart yStart w h hw hh hx hy hwp hhp c
    rw [range_regionReducedDensity_eq_cutRange]
    refine ⟨Pi.single (fun v => czxPlaquettePhysical q v.1) 1, ?_⟩
    let M : Matrix
        (RegionPhysicalConfig (d := 16) (torusContiguousRectangle xStart yStart w h))
        (RegionPhysicalConfig (d := 16)
          (Finset.univ \ torusContiguousRectangle xStart yStart w h)) ℂ :=
      fun σ τ => stateCoeff (czxPEPS width height)
        (assembleRegionσ (torusContiguousRectangle xStart yStart w h) σ τ)
    calc
      _ = M.col (fun v => czxPlaquettePhysical q v.1) := Matrix.mulVec_single_one M _
      _ = _ := by
        funext σ
        change stateCoeff (czxPEPS width height)
          (assembleRegionσ (torusContiguousRectangle xStart yStart w h) σ
            (fun v => czxPlaquettePhysical q v.1)) = _
        rw [stateCoeff_czxPlaquetteComplement]
        exact congrArg (fun μ => openRegionWeight (czxPEPS width height)
          (torusContiguousRectangle xStart yStart w h) μ σ) hq

include hw hh hx hy hwp hhp in
/-- The actual rectangle reduced density has rank two to its perimeter.
This statement does not require or assert a flat nonzero spectrum. -/
theorem rank_regionReducedDensity_czxRectangle :
    (regionReducedDensity (czxPEPS width height)
      (torusContiguousRectangle xStart yStart w h)).rank = 2 ^ (2 * w + 2 * h) := by
  change Module.finrank ℂ (Matrix.mulVecLin _).range = _
  rw [range_regionReducedDensity_czxRectangle xStart yStart w h hw hh hx hy hwp hhp]
  exact finrank_range_openRegionMap_czxRectangle xStart yStart w h hw hh hx hy hwp hhp

include hw hh hx hy hwp hhp in
/-- The actual rectangle reduced density has nonzero trace, so normalization
by the squared closed PEPS norm is well-defined. -/
theorem trace_regionReducedDensity_czxRectangle_ne_zero :
    (regionReducedDensity (czxPEPS width height)
      (torusContiguousRectangle xStart yStart w h)).trace ≠ 0 := by
  intro hz
  have hzero := (regionReducedDensity_posSemidef (czxPEPS width height)
    (torusContiguousRectangle xStart yStart w h)).trace_eq_zero_iff.mp hz
  have hr := rank_regionReducedDensity_czxRectangle
    xStart yStart w h hw hh hx hy hwp hhp
  rw [hzero, Matrix.rank_zero] at hr
  exact (pow_ne_zero (2 * w + 2 * h) (by norm_num : (2 : ℕ) ≠ 0)) hr.symm

include hw hh hx hy hwp hhp in
/-- Dividing the actual reduced density by its nonzero trace preserves the
identified physical support. -/
theorem range_normalizedRegionReducedDensity_czxRectangle :
    let ρ := regionReducedDensity (czxPEPS width height)
      (torusContiguousRectangle xStart yStart w h)
    (Matrix.mulVecLin (ρ.trace⁻¹ • ρ)).range =
      (openRegionMap (czxPEPS width height)
        (torusContiguousRectangle xStart yStart w h)).range := by
  classical
  dsimp only
  have htr := trace_regionReducedDensity_czxRectangle_ne_zero
    xStart yStart w h hw hh hx hy hwp hhp
  let ρ := regionReducedDensity (czxPEPS width height)
    (torusContiguousRectangle xStart yStart w h)
  have hsmul : Matrix.mulVecLin (ρ.trace⁻¹ • ρ) = ρ.trace⁻¹ • Matrix.mulVecLin ρ := by
    ext x i
    exact congrFun (Matrix.smul_mulVec _ _ _) i
  rw [hsmul, LinearMap.range_smul _ _ (inv_ne_zero htr)]
  exact range_regionReducedDensity_czxRectangle xStart yStart w h hw hh hx hy hwp hhp

include hw hh hx hy hwp hhp in
/-- The trace-normalized physical density has the same perimeter rank. -/
theorem rank_normalizedRegionReducedDensity_czxRectangle :
    let ρ := regionReducedDensity (czxPEPS width height)
      (torusContiguousRectangle xStart yStart w h)
    (ρ.trace⁻¹ • ρ).rank = 2 ^ (2 * w + 2 * h) := by
  change Module.finrank ℂ (Matrix.mulVecLin _).range = _
  rw [range_normalizedRegionReducedDensity_czxRectangle
    xStart yStart w h hw hh hx hy hwp hhp]
  exact finrank_range_openRegionMap_czxRectangle xStart yStart w h hw hh hx hy hwp hhp

end

end TNLean.PEPS
