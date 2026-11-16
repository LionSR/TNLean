/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.FullIntervalViability
import TNLean.MPS.AreaLaw.IntervalGenerators
import TNLean.MPS.AreaLaw.IntervalReferenceTrimming
import QICLean.Analysis.ViableSubspaceReferenceFilterTrimming

/-!
# Actual filtering and collective trimming at the same full-chain root

The native operator is carried to the original full-interval coordinates.
Its actual image space is given its standard orthonormal basis, and the
collective interval trim is applied to that basis. This is the final
filter-and-trim operation of ALVV, arXiv:1602.08828v2, Figure `fig:algo1`,
lines 1634–1640. It starts from the given root and constructs the next
space explicitly. Physical spectral hypotheses and a physical reference
supply the normalized-filter and reference bounds in the one-step lemma.

**Local fix (normalized gain and trimming constant):** The step uses the
normalized error recurrence in place of the printed multiplicative overlap
gain; see `docs/paper-gaps/alvv16_final_filter_gain.tex`. The collective trim
uses the proved `2 ξ √(m b)` increment and retains the squared whole-exterior
reference rank; see
https://sirui-lu.com/QICLean/paper-gaps/alvv16_trimming_constant.pdf.
-/

open scoped BigOperators InnerProductSpace

namespace TNLean.MPS.AreaLaw

/-- The literal native filter in full-interval coefficient coordinates.
Supporting ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1634–1640. -/
noncomputable def fullIntervalFilter (L q : ℕ)
    (K : EuclideanSpace ℂ (Fin L → Fin q) →L[ℂ]
      EuclideanSpace ℂ (Fin L → Fin q)) :
    EuclideanSpace ℂ (interval L 0 L → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L 0 L → Fin q) :=
  (fullIntervalEquiv L q).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L K ∘L
    (fullIntervalEquiv L q).toContinuousLinearEquiv.toContinuousLinearMap

/-- The coordinate filter is exactly conjugation by the coefficient-reading
isometry. Supporting ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1634–1640. -/
@[simp]
theorem fullIntervalFilter_apply (L q : ℕ)
    (K : EuclideanSpace ℂ (Fin L → Fin q) →L[ℂ]
      EuclideanSpace ℂ (Fin L → Fin q))
    (x : EuclideanSpace ℂ (interval L 0 L → Fin q)) :
    fullIntervalFilter L q K x =
      (fullIntervalEquiv L q).symm (K (fullIntervalEquiv L q x)) := rfl

/-- One actual image followed by one actual collective trim at the full
interval. The orthonormal basis is constructed from the image itself.
This is ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1634–1640. -/
noncomputable def fullIntervalFilterTrimStep (L q : ℕ)
    (K : EuclideanSpace ℂ (Fin L → Fin q) →L[ℂ]
      EuclideanSpace ℂ (Fin L → Fin q)) (xi : ℝ)
    (S : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q))) :
    Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q)) :=
  let V := S.map (fullIntervalFilter L q K).toLinearMap
  let b := stdOrthonormalBasis ℂ V
  intervalTrimSubspace L q 0 L xi (fun i ↦ (b i : _))

/-- Filtering and trimming do not increase the candidate dimension.
Supporting ALVV, arXiv:1602.08828v2, final iteration, lines 1634–1640,
and collective trimming, lines 662–663. -/
theorem finrank_fullIntervalFilterTrimStep_le {L q : ℕ}
    (K : EuclideanSpace ℂ (Fin L → Fin q) →L[ℂ]
      EuclideanSpace ℂ (Fin L → Fin q)) (xi : ℝ)
    (S : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q))) :
    Module.finrank ℂ (fullIntervalFilterTrimStep L q K xi S) ≤ Module.finrank ℂ S := by
  let V := S.map (fullIntervalFilter L q K).toLinearMap
  let b := stdOrthonormalBasis ℂ V
  exact (finrank_intervalTrimSubspace_le L q 0 L xi (fun i ↦ (b i : _))).trans
    (Submodule.finrank_map_le _ S)

/-- The next actual space has a recorded spanning family controlled by
the preceding dimension budget. The weighted rank bound concerns each
recorded vector. Supporting ALVV, arXiv:1602.08828v2, collective trimming,
lines 660–697, and the final iteration, lines 1634–1640. -/
theorem isIntervalSpanWithRankBound_fullIntervalFilterTrimStep
    {L q count : ℕ} {xi : ℝ} (hxi : 0 < xi)
    (K : EuclideanSpace ℂ (Fin L → Fin q) →L[ℂ]
      EuclideanSpace ℂ (Fin L → Fin q))
    (S : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q)))
    (hS : Module.finrank ℂ S ≤ count) :
    IsIntervalSpanWithRankBound L q 0 L count xi (fullIntervalFilterTrimStep L q K xi S) := by
  let V := S.map (fullIntervalFilter L q K).toLinearMap
  let b := stdOrthonormalBasis ℂ V
  exact isIntervalSpanWithRankBound_intervalTrimSubspace hxi b
    ((Submodule.finrank_map_le _ S).trans hS)

private theorem nativeFullIntervalSpace_filter_image {L q : ℕ}
    (K : EuclideanSpace ℂ (Fin L → Fin q) →L[ℂ]
      EuclideanSpace ℂ (Fin L → Fin q))
    (S : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q))) :
    nativeFullIntervalSpace L q (S.map (fullIntervalFilter L q K).toLinearMap) =
      (nativeFullIntervalSpace L q S).map K.toLinearMap := by
  unfold nativeFullIntervalSpace
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1

/-- A normalized native filter followed by the literal full-interval trim
satisfies the stable recurrence using one common physical MPS reference.
The image inclusion, product coordinates and actual trim are derived from
the recorded operation. The normalized-filter bounds are explicit premises
of this auxiliary; the physical spectral construction is separate.
Supporting ALVV, arXiv:1602.08828v2, proof of `t:alg1`, lines 1801–1813. -/
theorem isCloseTo_nativeFullIntervalSpace_filterTrimStep
    {L q D : ℕ} (hD : 1 ≤ D)
    {G U : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))}
    {xi c delta epsilon eta : ℝ} (hxi : 0 < xi) (hc : 0 < c) (hc1 : c ≤ 1)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ 1 / 2) (hepsilon : 0 ≤ epsilon)
    (K : EuclideanSpace ℂ (Fin L → Fin q) →L[ℂ]
      EuclideanSpace ℂ (Fin L → Fin q))
    (hKG : ∀ x ∈ G, K x ∈ G) (hKGo : ∀ x ∈ Gᗮ, K x ∈ Gᗮ)
    (hlow : ∀ x ∈ G, ‖x‖ ≤ ‖K x‖)
    (hhigh : ∀ x ∈ Gᗮ, ‖K x‖ ^ 2 ≤ (1 - c) * ‖x‖ ^ 2)
    (hGU : Submodule.IsCloseTo epsilon G U) (hUG : Submodule.IsCloseTo epsilon U G)
    (hU : ∀ v ∈ U, IsOpenMPS L q D (fun x ↦ v x))
    (hepsilonBudget : epsilon ≤ c ^ 2 * eta / 1024)
    (hxiBudget : xi * Real.sqrt (((L - 1 : ℕ) : ℝ) * (D ^ 2 : ℕ)) ≤ c * eta / 48)
    (S : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q)))
    (hS : Submodule.IsCloseTo delta (nativeFullIntervalSpace L q S) G) :
    Submodule.IsCloseTo ((1 - c / 4) * delta + c * eta / 8)
      (nativeFullIntervalSpace L q (fullIntervalFilterTrimStep L q K xi S)) G := by
  let F := Entropy.regionConfigurationSplit q (interval L 0 L)
  let V := S.map (fullIntervalFilter L q K).toLinearMap
  let b := stdOrthonormalBasis ℂ V
  let Kprod := F.toContinuousLinearEquiv.toContinuousLinearMap ∘L K ∘L
    F.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hKprod (x : EuclideanSpace ℂ (Fin L → Fin q)) : Kprod (F x) = F (K x) := by
    change F (K (F.symm (F x))) = F (K x)
    rw [F.symm_apply_apply]
  have hSprod : Submodule.IsCloseTo delta
      (Submodule.prodExt S (↥((interval L 0 L)ᶜ) → Fin q))
      (G.map F.toLinearEquiv.toLinearMap) := by
    rw [← map_nativeFullIntervalSpace_regionConfigurationSplit S]
    exact (Submodule.isCloseTo_map_iff F).mpr hS
  have himage : (Submodule.prodExt S (↥((interval L 0 L)ᶜ) → Fin q)).map Kprod.toLinearMap ≤
      Submodule.prodExt V (↥((interval L 0 L)ᶜ) → Fin q) := by
    rw [← map_nativeFullIntervalSpace_regionConfigurationSplit S,
      ← map_nativeFullIntervalSpace_regionConfigurationSplit V,
      nativeFullIntervalSpace_filter_image K S, ← Submodule.map_comp, ← Submodule.map_comp]
    apply le_of_eq
    congr 1
    exact LinearMap.ext hKprod
  have hKGprod : ∀ x ∈ G.map F.toLinearEquiv.toLinearMap,
      Kprod x ∈ G.map F.toLinearEquiv.toLinearMap := by
    rintro _ ⟨x, hx, rfl⟩
    change Kprod (F x) ∈ _
    rw [hKprod]
    exact ⟨K x, hKG x hx, rfl⟩
  have hKGoprod : ∀ x ∈ (G.map F.toLinearEquiv.toLinearMap)ᗮ,
      Kprod x ∈ (G.map F.toLinearEquiv.toLinearMap)ᗮ := by
    rw [← Submodule.map_orthogonal_equiv G F]
    rintro _ ⟨x, hx, rfl⟩
    change Kprod (F x) ∈ _
    rw [hKprod]
    exact ⟨K x, hKGo x hx, rfl⟩
  have hlowprod : ∀ x ∈ G.map F.toLinearEquiv.toLinearMap, ‖x‖ ≤ ‖Kprod x‖ := by
    rintro _ ⟨x, hx, rfl⟩
    change ‖F x‖ ≤ ‖Kprod (F x)‖
    simpa only [hKprod, F.norm_map] using hlow x hx
  have hhighprod : ∀ x ∈ (G.map F.toLinearEquiv.toLinearMap)ᗮ,
      ‖Kprod x‖ ^ 2 ≤ (1 - c) * ‖x‖ ^ 2 := by
    rw [← Submodule.map_orthogonal_equiv G F]
    rintro _ ⟨x, hx, rfl⟩
    change ‖Kprod (F x)‖ ^ 2 ≤ (1 - c) * ‖F x‖ ^ 2
    simpa only [hKprod, F.norm_map] using hhigh x hx
  have hGUprod := (Submodule.isCloseTo_map_iff F).mpr hGU
  have hUGprod := (Submodule.isCloseTo_map_iff F).mpr hUG
  have hrank : ∀ t ∈ U.map F.toLinearEquiv.toLinearMap, ∀ j < L - 1,
      Matrix.schmidtRank (WithLp.ofLp
        (Entropy.cutEnvVector (n := fun _ : interval L 0 L ↦ q)
          (intervalTrimCut L 0 L j) t)) ≤ D ^ 2 := by
    intro t ht j hj
    exact schmidtRank_cutEnvVector_interval_reference_le hD hU 0 L ht j (by simpa using hj)
  have hstep := Entropy.isCloseTo_prodExt_trimSubspace_after_filter
    (intervalTrimCut_mono L 0 L) hxi hc hc1 hdelta0 hdelta hepsilon b Kprod
    hSprod himage hKGprod hKGoprod hlowprod hhighprod hGUprod hUGprod hrank
    hepsilonBudget hxiBudget
  change Submodule.IsCloseTo ((1 - c / 4) * delta + c * eta / 8)
    (Submodule.prodExt (fullIntervalFilterTrimStep L q K xi S)
      (↥((interval L 0 L)ᶜ) → Fin q))
    (G.map F.toLinearEquiv.toLinearMap) at hstep
  rw [← map_nativeFullIntervalSpace_regionConfigurationSplit
    (fullIntervalFilterTrimStep L q K xi S)] at hstep
  exact (Submodule.isCloseTo_map_iff F).mp hstep

end TNLean.MPS.AreaLaw
