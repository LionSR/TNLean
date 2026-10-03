/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegionReducedDensity
import TNLean.PEPS.RegionBlock.KernelDescent

/-!
# Regional supports of ordinary injective PEPS

The actual open-region map differs from the globally indexed blocked map
only by the number of exterior virtual assignments. Injectivity of the
blocked map therefore implies injectivity of the actual map, even without
nonzero bond dimensions. With nonzero bonds their ranges coincide.

Across a physical cut, injectivity of the complementary open-region map
identifies the reduced-density support with the regional PEPS space.

Source: CPGSV21, arXiv:2011.12127, Section IV.C.1, lines 2003–2044;
the complementary-block Schmidt-span argument is also in
arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254–582.

**Scope restriction (nonzero virtual spaces):** The vertex-injective
consequences assume positive bond dimensions, following the convention
recorded in `docs/paper-gaps/peps_injective_ft_section3_route.tex`.
The complementary-map support theorem does not need this restriction.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}

private theorem range_mul_transpose_of_injective
    {ι κ τ : Type*} [Fintype κ] [Fintype τ]
    (T : Matrix ι κ ℂ) (S : Matrix τ κ ℂ)
    (hS : Function.Injective (Matrix.mulVecLin S)) :
    (Matrix.mulVecLin (T * S.transpose)).range = (Matrix.mulVecLin T).range := by
  classical
  obtain ⟨L, hL⟩ := (Matrix.mulVecLin S).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hS)
  have hLS : LinearMap.toMatrix' L * S = 1 := by
    simpa only [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply',
      LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] using
      congrArg LinearMap.toMatrix' hL
  have hSL : S.transpose * (LinearMap.toMatrix' L).transpose = 1 := by
    rw [← Matrix.transpose_mul, hLS, Matrix.transpose_one]
  have hsurj : Function.Surjective (Matrix.mulVecLin S.transpose) := by
    intro x
    refine ⟨Matrix.mulVecLin (LinearMap.toMatrix' L).transpose x, ?_⟩
    rw [← LinearMap.comp_apply, ← Matrix.mulVecLin_mul, hSL, Matrix.mulVecLin_one]
    rfl
  rw [Matrix.mulVecLin_mul, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr hsurj, Submodule.map_top]

/-- The globally indexed blocked map counts every exterior virtual assignment.
Source: the finite-region contraction of CPGSV21, Section IV.C.1,
lines 2003–2008. -/
theorem regionBlockedTensorMap_eq_exterior_smul_openRegionMap
    (A : Tensor Γ d) (R : Finset V) :
    regionBlockedTensorMap A R = (regionExteriorMultiplicity A R : ℂ) • openRegionMap A R := by
  refine LinearMap.ext fun x => funext fun σ => ?_
  simp only [regionBlockedTensorMap_apply, regionBlockedWeight_eq_exterior_mul_openRegionWeight,
    LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, openRegionMap_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun μ _ => by ring

/-- Injectivity of the globally indexed region family implies injectivity of
the genuine contraction. Source: ordinary regional injectivity in
arXiv:1804.04964, Section 3, lines 205–250 and 1205–1210. -/
theorem openRegionMap_injective_of_regionBlockedTensorInjective
    (A : Tensor Γ d) (R : Finset V) (hR : RegionBlockedTensorInjective A R) :
    Function.Injective (openRegionMap A R) := by
  have h := hR.fintypeLinearCombination_injective
  change Function.Injective (regionBlockedTensorMap A R) at h
  intro x y hxy
  apply h
  rw [regionBlockedTensorMap_eq_exterior_smul_openRegionMap]
  exact congrArg (fun ψ => (regionExteriorMultiplicity A R : ℂ) • ψ) hxy

/-- Contracting ordinary injective sites gives an injective actual region map.
Source: arXiv:1804.04964, Section 3, lines 205–250 and 1205–1210. -/
theorem openRegionMap_injective_of_isVertexInjective
    (A : Tensor Γ d) (R : Finset V) (hA : IsVertexInjective A)
    (hpos : ∀ e, 0 < A.bondDim e) : Function.Injective (openRegionMap A R) :=
  openRegionMap_injective_of_regionBlockedTensorInjective A R
    (regionBlockedTensorInjective_of_isVertexInjective A R hA hpos)

/-- An injective open-region map realizes the full boundary dimension.
Source: the boundary-parameter count for ordinary injective PEPS in
CPGSV21, Section IV.C.1, lines 2003–2044. -/
theorem finrank_regionGroundSpace_of_injective_openRegionMap
    (A : Tensor Γ d) (R : Finset V) (hR : Function.Injective (openRegionMap A R)) :
    Module.finrank ℂ (regionGroundSpace A R) =
      ∏ e : {e : Edge Γ // IsRegionBoundaryEdge R e}, A.bondDim e.1 := by
  change Module.finrank ℂ (openRegionMap A R).range = _
  rw [LinearMap.finrank_range_of_inj hR, Module.finrank_pi, Fintype.card_pi]
  exact Finset.prod_congr rfl fun e _ => Fintype.card_fin _

/-- Nonzero virtual spaces remove the exterior multiplicity from the range.
Source: actual regional contraction in CPGSV21, Section IV.C.1,
lines 2003–2008. -/
theorem range_regionBlockedTensorMap_eq_regionGroundSpace
    (A : Tensor Γ d) (R : Finset V) (hA : ∀ e, A.bondDim e ≠ 0) :
    (regionBlockedTensorMap A R).range = regionGroundSpace A R := by
  rw [regionBlockedTensorMap_eq_exterior_smul_openRegionMap]
  exact LinearMap.range_smul _ _ (by
    exact_mod_cast regionExteriorMultiplicity_ne_zero A R hA)

/-- An injective complementary open-region map makes the physical reduced
support exactly the original regional space. No injectivity of the region
itself is needed. Source: the Schmidt-span argument in arXiv:1804.04964,
Section 3, Lemma `inj_isomorph`, lines 254–582, for the actual contraction. -/
theorem range_regionReducedDensity_eq_regionGroundSpace_of_injective_complement
    (A : Tensor Γ d) (R : Finset V)
    (hC : Function.Injective (openRegionMap A (Finset.univ \ R))) :
    (Matrix.mulVecLin (regionReducedDensity A R)).range = regionGroundSpace A R := by
  classical
  let T := openRegionCoefficientMatrix A R
  let S : Matrix (RegionPhysicalConfig (d := d) (Finset.univ \ R))
      (RegionBoundaryConfig A R) ℂ :=
    fun τ μ => openRegionWeight A (Finset.univ \ R)
      (regionComplementBoundaryConfig A R μ) τ
  have hSC : Matrix.mulVecLin S = Fintype.linearCombination ℂ
      (fun μ => openRegionWeight A (Finset.univ \ R)
        (regionComplementBoundaryConfig A R μ)) := by
    refine LinearMap.ext fun x => funext fun τ => ?_
    change (∑ μ, S τ μ * x μ) = _
    simp only [Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun μ _ => mul_comm _ _
  have hS : Function.Injective (Matrix.mulVecLin S) := by
    rw [hSC]
    have hli : LinearIndependent ℂ (openRegionWeight A (Finset.univ \ R)) :=
      linearIndependent_iff_injective_fintypeLinearCombination.mpr hC
    exact (hli.comp (regionComplementBoundaryConfigEquiv A R)
      (regionComplementBoundaryConfigEquiv A R).injective).fintypeLinearCombination_injective
  have hM : (fun σ τ => stateCoeff A (assembleRegionσ R σ τ)) = T * S.transpose := by
    funext σ τ
    rw [stateCoeff_eq_openRegionComplement_unconditional, Matrix.mul_apply]
    rfl
  rw [range_regionReducedDensity_eq_cutRange, hM, range_mul_transpose_of_injective T S hS]
  change (Matrix.toLin' (openRegionCoefficientMatrix A R)).range = _
  rw [← toMatrix_openRegionMap, Matrix.toLin'_toMatrix']
  rfl

/-- Every cut of a vertex-injective PEPS has the full regional support.
No connectedness of either side is required. Source: the injective
Schmidt-span argument in arXiv:1804.04964, Lemma `inj_isomorph`,
lines 254–582, and CPGSV21, Section IV.C.1, lines 2003–2044. -/
theorem range_regionReducedDensity_eq_regionGroundSpace_of_isVertexInjective
    (A : Tensor Γ d) (R : Finset V) (hA : IsVertexInjective A)
    (hpos : ∀ e, 0 < A.bondDim e) :
    (Matrix.mulVecLin (regionReducedDensity A R)).range = regionGroundSpace A R :=
  range_regionReducedDensity_eq_regionGroundSpace_of_injective_complement A R
    (openRegionMap_injective_of_isVertexInjective A (Finset.univ \ R) hA hpos)

/-- Two injective actual region maps saturate the Schmidt boundary rank.
No site injectivity or connectedness hypothesis is imposed.
Source: the complementary-block Schmidt-span argument in arXiv:1804.04964,
Section 3, Lemma `inj_isomorph`, lines 254–582. -/
theorem rank_regionReducedDensity_of_injective_open_cut
    (A : Tensor Γ d) (R : Finset V)
    (hR : Function.Injective (openRegionMap A R))
    (hC : Function.Injective (openRegionMap A (Finset.univ \ R))) :
    (regionReducedDensity A R).rank =
      ∏ e : {e : Edge Γ // IsRegionBoundaryEdge R e}, A.bondDim e.1 := by
  change Module.finrank ℂ (Matrix.mulVecLin (regionReducedDensity A R)).range = _
  rw [range_regionReducedDensity_eq_regionGroundSpace_of_injective_complement A R hC]
  exact finrank_regionGroundSpace_of_injective_openRegionMap A R hR

/-- Equal physical coefficient vectors determine equal regional spaces
whenever both complementary actual region maps are injective.
Source: the physical-support argument of arXiv:1804.04964,
Section 3, Lemma `inj_isomorph`, lines 254–582, applied to the genuine contraction. -/
theorem SameState.regionGroundSpace_eq_of_injective_complements
    {A B : Tensor Γ d} (hAB : SameState A B) (R : Finset V)
    (hA : Function.Injective (openRegionMap A (Finset.univ \ R)))
    (hB : Function.Injective (openRegionMap B (Finset.univ \ R))) :
    regionGroundSpace A R = regionGroundSpace B R := by
  rw [← range_regionReducedDensity_eq_regionGroundSpace_of_injective_complement A R hA,
    hAB.regionReducedDensity_eq R,
    range_regionReducedDensity_eq_regionGroundSpace_of_injective_complement B R hB]

/-- The exact Schmidt rank across an arbitrary injective cut is the product
of its crossing-bond dimensions. Source: the injective boundary count of
CPGSV21, Section IV.C.1, lines 2003–2044. -/
theorem rank_regionReducedDensity_of_isVertexInjective
    (A : Tensor Γ d) (R : Finset V) (hA : IsVertexInjective A)
    (hpos : ∀ e, 0 < A.bondDim e) :
    (regionReducedDensity A R).rank =
      ∏ e : {e : Edge Γ // IsRegionBoundaryEdge R e}, A.bondDim e.1 := by
  exact rank_regionReducedDensity_of_injective_open_cut A R
    (openRegionMap_injective_of_isVertexInjective A R hA hpos)
    (openRegionMap_injective_of_isVertexInjective A (Finset.univ \ R) hA hpos)

end TNLean.PEPS
