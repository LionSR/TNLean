/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.CanonicalIntervalRawHistory
import QICLean.Analysis.CanonicalHalfSamplingParentProbability
import QICLean.Entropy.RegionalViability

/-!
# Fixed-input probability for an actual interval history and terminal image

The candidate's actual orthogonal projection is put in the prescribed finite
coordinates. The fixed-K resampling theorem then bounds its literal original-target
history under the actual finite product Haar law. On that one event, the same
complete interval parent is viable for the original global target, and its same
last untrimmed image has the quantitative bound for every improving target.

This is a conditional analytic auxiliary to ALVV, arXiv:1602.08828v2,
lines 749–755 and 1801–1813. The family, targets, reference and numerical
certificates are explicit inputs. No successful sample or energy trial is assumed.

**Local fix (repeated sampling and terminal amplification):** This is the
corrected stopped-resampling parent with terminal image and trim; see
https://sirui-lu.com/QICLean/paper-gaps/alvv16_bootstrap_constants.pdf.
It is not a running-time or complete physical construction theorem.
-/

open MeasureTheory
open scoped Matrix.Norms.L2Operator ENNReal

namespace TNLean.MPS.AreaLaw

/-- The actual candidate and finite sequence have the literal original-target
history bound. The same history gives the same parent's viability and the
same untrimmed image's bound for all centers. Family and reference conditions
are explicit analytic certificates, not a supplied sampling-success event.
Supporting ALVV, arXiv:1602.08828v2, lines 749–755 and 1801–1813. -/
theorem canonicalHalfSampledIntervalHistory_probability
    {X : Type*} (D a K : ℕ) (hD : 2 ≤ D) (eta : ℝ) (hK : 1 ≤ K)
    (hThreshold : ∀ rho len Q : ℕ, K * (rho + 1) * (len + 2) ^ 2 ≤ Q →
      4 * D ^ 2 ≤ Q ∧ Submodule.bootstrapFailure D Q rho ≤ eta / ((len : ℝ) + 2) ^ a)
    (L q p endR nFamily rho rounds bRef : ℕ)
    (Delta epsilon epsilonRef xi : ℝ)
    (G R : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (x0 : X) (T : X → Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (F : Fin nFamily → EuclideanSpace ℂ (interval L p endR → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p endR → Fin q))
    (W : Submodule ℂ (EuclideanSpace ℂ (interval L p endR → Fin q)))
    (hN : nFamily ≤ D ^ 2)
    (hRawSoft : ∀ x, Submodule.IsCloseTo epsilon G (T x))
    (hSoftRaw : ∀ x, Submodule.IsCloseTo (1 / 200) (T x) G)
    (hA : ∀ x delta, delta < 1 →
      ∀ S : Submodule ℂ (EuclideanSpace ℂ (interval L p endR → Fin q)),
      Submodule.IsViable delta S
        ((T x).map
          (Entropy.regionTensorCoordinates q (interval L p endR)).toLinearEquiv.toLinearMap) →
      Submodule.IsViable (Delta / (1 - delta) ^ 2)
        (⨆ i, S.map (F i).toLinearMap)
        ((T x).map
          (Entropy.regionTensorCoordinates q (interval L p endR)).toLinearEquiv.toLinearMap))
    (hDelta : (D : ℝ) ^ 12 * Delta ≤ 1 / 100000)
    (hepsilon : epsilon ≤ ((3 / 100 : ℝ) / (D : ℝ) ^ 2) ^ 2 / 100)
    (hxi : 0 < xi) (hepsilonRef0 : 0 ≤ epsilonRef) (hepsilonRef : epsilonRef ≤ 1 / 100000)
    (hRawRef : Submodule.IsCloseTo epsilonRef G R)
    (hRefRaw : Submodule.IsCloseTo epsilonRef R G)
    (hRank : ∀ t ∈ R.map
        (Entropy.regionConfigurationSplit q (interval L p endR)).toLinearEquiv.toLinearMap,
      ∀ j < endR - p - 1,
      Matrix.schmidtRank (WithLp.ofLp
        (Entropy.cutEnvVector (n := fun _ : interval L p endR ↦ q)
          (intervalTrimCut L p endR j) t)) ≤ bRef)
    (hbudget : xi * Real.sqrt (((endR - p - 1 : ℕ) : ℝ) * (bRef : ℝ)) ≤ 1 / 1000)
    (hdim : Module.finrank ℂ G ≤ rho)
    (hrounds : Fintype.card (interval L p endR → Fin q) ≤ 2 ^ rounds)
    (hInitial : Submodule.IsViable 0.04 W
      (G.map (Entropy.regionTensorCoordinates q (interval L p endR)).toLinearEquiv.toLinearMap)) :
    let d := Fintype.card (interval L p endR → Fin q)
    let e := (Fintype.equivFin (interval L p endR → Fin q)).symm
    let P := ((Matrix.toEuclideanCLM (n := interval L p endR → Fin q) (𝕜 := ℂ)).symm
      W.starProjection).reindex e.symm e.symm
    let threshold := K * (rho + 1) * (L + 2) ^ 2
    let good := canonicalHalfSampledIntervalHistory L q p endR D threshold rounds F xi W G
    let state := fun (U : Fin rounds → Matrix.rankUnitaryProduct d) j ↦
      Entropy.canonicalHalfSampleTrimIterate e (intervalTrimCut L p endR) xi
        (endR - p - 1) D threshold (Entropy.nativeFamilyMatrix e F) P
        (Entropy.halfSamplingSeedSequence U) j
    let image := fun U ↦ (Matrix.toEuclideanLin (Matrix.familySupportProj
      (fun i ↦ Entropy.nativeFamilyMatrix e F i * state U rounds))).range
    let parent := fun U ↦ canonicalHalfSampledIntervalParent
      L q p endR D threshold rounds F xi W U
    let law := Measure.pi (fun _ : Fin rounds ↦ Matrix.rankUnitaryHaar d)
    MeasurableSet good ∧
    law goodᶜ ≤ (rounds : ℝ≥0∞) * ENNReal.ofReal (eta / ((L : ℝ) + 2) ^ a) ∧
    MeasurableSet {U | Submodule.IsViable (3 / 200) (parent U)
      (G.map (Entropy.regionTensorCoordinates q (interval L p endR)).toLinearEquiv.toLinearMap)} ∧
    law {U | ¬Submodule.IsViable (3 / 200) (parent U)
      (G.map (Entropy.regionTensorCoordinates q (interval L p endR)).toLinearEquiv.toLinearMap)} ≤
        (rounds : ℝ≥0∞) * ENNReal.ofReal (eta / ((L : ℝ) + 2) ^ a) ∧
    ∀ U ∈ good,
      (∀ x, Submodule.IsViable (Delta / (91 / 100 : ℝ) ^ 2) (image U)
        ((T x).map
          (Entropy.regionTensorCoordinates q (interval L p endR)).toLinearEquiv.toLinearMap)) ∧
      Submodule.IsViable (27 / 2500) (image U)
        (G.map (Entropy.regionTensorCoordinates q (interval L p endR)).toLinearEquiv.toLinearMap) ∧
      Submodule.IsViable (3 / 200) (parent U)
        (G.map
          (Entropy.regionTensorCoordinates q (interval L p endR)).toLinearEquiv.toLinearMap) := by
  classical
  intro d e P threshold good state image parent law
  let split := Entropy.regionConfigurationSplit q (interval L p endR)
  let Graw := G.map split.toLinearEquiv.toLinearMap
  let Rraw := R.map split.toLinearEquiv.toLinearMap
  let Traw := fun x ↦ (T x).map split.toLinearEquiv.toLinearMap
  have hRange : (Matrix.toEuclideanLin P).range.map
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap = W := by
    change (Matrix.toEuclideanLin
      (((Matrix.toEuclideanCLM (n := interval L p endR → Fin q) (𝕜 := ℂ)).symm
        W.starProjection).submatrix e e)).range.map
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap = W
    rw [Matrix.map_range_toEuclideanLin_submatrix]
    change ((Matrix.toEuclideanCLM (n := interval L p endR → Fin q) (𝕜 := ℂ))
      ((Matrix.toEuclideanCLM (n := interval L p endR → Fin q) (𝕜 := ℂ)).symm
        W.starProjection)).toLinearMap.range = W
    rw [StarAlgEquiv.apply_symm_apply, Submodule.range_starProjection]
  have hInitialRaw : Submodule.IsCloseTo 0.04
      (Submodule.prodExt ((Matrix.toEuclideanLin P).range.map
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap)
          (↥((interval L p endR)ᶜ) → Fin q)) Graw := by
    rw [hRange]
    exact (Entropy.isCloseTo_prodExt_region_iff_isViable (interval L p endR) W G).mpr hInitial
  have hdimRaw : Module.finrank ℂ Graw ≤ rho := by
    rw [split.toLinearEquiv.finrank_map_eq]
    exact hdim
  have hAraw : ∀ x delta, delta < 1 →
      ∀ S : Submodule ℂ (EuclideanSpace ℂ (interval L p endR → Fin q)),
      Submodule.IsCloseTo delta
        (Submodule.prodExt S (↥((interval L p endR)ᶜ) → Fin q)) (Traw x) →
      Submodule.IsCloseTo (Delta / (1 - delta) ^ 2)
        (Submodule.prodExt (⨆ i, S.map (F i).toLinearMap)
          (↥((interval L p endR)ᶜ) → Fin q)) (Traw x) := by
    intro x delta hdelta S hS
    exact (Entropy.isCloseTo_prodExt_region_iff_isViable (interval L p endR)
      (⨆ i, S.map (F i).toLinearMap) (T x)).mpr
        (hA x delta hdelta S
          ((Entropy.isCloseTo_prodExt_region_iff_isViable (interval L p endR) S (T x)).mp hS))
  obtain ⟨hGood, hFailure, hParentMeas, hParentFailure, hOnGood, _hRank, _hStop⟩ :=
    Entropy.canonicalHalfSamplingParent_joint_probability_of_threshold
      (n := fun _ : interval L p endR ↦ q)
      (β := ↥((interval L p endR)ᶜ) → Fin q) (ι := Fin nFamily)
      D a K hD eta hK hThreshold L rho d rounds e (endR - p - 1) bRef
      Delta epsilon epsilonRef xi Graw Rraw x0 Traw F P
      (by simpa only [Fintype.card_fin] using hN)
      (fun x ↦ (Submodule.isCloseTo_map_iff split).mpr (hRawSoft x))
      (fun x ↦ (Submodule.isCloseTo_map_iff split).mpr (hSoftRaw x))
      hAraw hDelta hepsilon (intervalTrimCut L p endR) (intervalTrimCut_mono L p endR)
      hxi hepsilonRef0 hepsilonRef
      ((Submodule.isCloseTo_map_iff split).mpr hRawRef)
      ((Submodule.isCloseTo_map_iff split).mpr hRefRaw)
      hRank hbudget hdimRaw hrounds hInitialRaw
  change MeasurableSet good at hGood
  change law goodᶜ ≤ (rounds : ℝ≥0∞) * ENNReal.ofReal (eta / ((L : ℝ) + 2) ^ a)
    at hFailure
  change MeasurableSet {U : Fin rounds → Matrix.rankUnitaryProduct d |
    Submodule.IsCloseTo (3 / 200)
      (Submodule.prodExt (parent U) (↥((interval L p endR)ᶜ) → Fin q)) Graw} at hParentMeas
  change law {U : Fin rounds → Matrix.rankUnitaryProduct d |
    ¬Submodule.IsCloseTo (3 / 200)
      (Submodule.prodExt (parent U) (↥((interval L p endR)ᶜ) → Fin q)) Graw} ≤
      (rounds : ℝ≥0∞) * ENNReal.ofReal (eta / ((L : ℝ) + 2) ^ a) at hParentFailure
  have hparentIff (U : Fin rounds → Matrix.rankUnitaryProduct d) :
      Submodule.IsCloseTo (3 / 200)
        (Submodule.prodExt (parent U) (↥((interval L p endR)ᶜ) → Fin q)) Graw ↔
      Submodule.IsViable (3 / 200) (parent U)
        (G.map (Entropy.regionTensorCoordinates q (interval L p endR)).toLinearEquiv.toLinearMap) :=
    Entropy.isCloseTo_prodExt_region_iff_isViable (interval L p endR) (parent U) G
  refine ⟨hGood, hFailure, ?_, ?_, ?_⟩
  · simpa only [hparentIff] using hParentMeas
  · simpa only [hparentIff] using hParentFailure
  · intro U hU
    obtain ⟨hTargets, hRawImage, hRawParent⟩ := hOnGood U hU
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact (Entropy.isCloseTo_prodExt_region_iff_isViable (interval L p endR)
        (image U) (T x)).mp (hTargets x)
    · exact (Entropy.isCloseTo_prodExt_region_iff_isViable (interval L p endR)
        (image U) G).mp hRawImage
    · exact (hparentIff U).mp hRawParent

end TNLean.MPS.AreaLaw
