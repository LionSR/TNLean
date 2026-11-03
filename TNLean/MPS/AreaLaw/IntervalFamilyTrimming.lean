/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.IntervalGenerators
import TNLean.MPS.AreaLaw.IntervalReferenceTrimming
import QICLean.Analysis.ViableSubspaceSharpTensorReduction

/-!
# One actual tensor-family application and collective interval trim

The retained-factor family acts on the current space, and the actual
collective trim is applied to an orthonormal basis of that image span.
The normalized filter error and the target-relative weighted reference
estimate control this actual output. No closeness between the whole
image span and its trim is assumed.

This is a supporting estimate for ALVV, arXiv:1602.08828v2,
Figure `fig:merge-prime`, lines 1668–1670, and the reference argument,
lines 1801–1805. Physical construction, numerical calibration and adaptive
sampling probability remain separate.

**Local fix (recursive assignment):** Each family application uses the
current space, rather than the unchanged initial sample printed in the
repeated assignment. See `docs/paper-gaps/alvv16_approximation_parameters.tex`.
-/

open scoped TensorProduct InnerProductSpace

namespace TNLean.MPS.AreaLaw

/-- Apply the actual retained-factor family to the current space and trim
its actual image basis. Supporting ALVV, arXiv:1602.08828v2,
Figure `fig:merge-prime`, lines 1668–1670, with the recursive assignment
correction documented in the module description. -/
noncomputable def intervalFamilyTrimStep (L q p r : ℕ) {N : ℕ}
    (F : Fin N → EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p r → Fin q)) (xi : ℝ)
    (S : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q))) :
    Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)) :=
  let V := ⨆ i, S.map (F i).toLinearMap
  intervalTrimSubspace L q p r xi
    (fun i ↦ ((stdOrthonormalBasis ℂ V) i : EuclideanSpace ℂ (interval L p r → Fin q)))

/-- One actual family application and collective trim multiplies dimension
by at most the number of retained factors. Supporting ALVV,
arXiv:1602.08828v2, Lemma `l:er`, lines 597–622, and
Figure `fig:merge-prime`, lines 1668–1670. -/
theorem finrank_intervalFamilyTrimStep_le {L q p r N : ℕ}
    (F : Fin N → EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p r → Fin q)) (xi : ℝ)
    (S : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q))) :
    Module.finrank ℂ (intervalFamilyTrimStep L q p r F xi S) ≤
      N * Module.finrank ℂ S := by
  apply (finrank_intervalTrimSubspace_le L q p r xi _).trans
  simpa only [Fintype.card_fin] using
    Submodule.finrank_iSup_map_le_card_mul S (fun i ↦ (F i).toLinearMap)

/-- The actual trim of the family image retains its recorded spanning
vectors and their weighted internal-cut ranks. Supporting ALVV,
arXiv:1602.08828v2, collective trimming, lines 660–697, and
Figure `fig:merge-prime`, lines 1668–1670. -/
theorem isIntervalSpanWithRankBound_intervalFamilyTrimStep
    {L q p r N count : ℕ} {xi : ℝ} (hxi : 0 < xi)
    (F : Fin N → EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p r → Fin q))
    (S : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)))
    (hS : Module.finrank ℂ S ≤ count) :
    IsIntervalSpanWithRankBound L q p r (N * count) xi
      (intervalFamilyTrimStep L q p r F xi S) := by
  apply isIntervalSpanWithRankBound_intervalTrimSubspace hxi
  have hdim := Submodule.finrank_iSup_map_le_card_mul S (fun i ↦ (F i).toLinearMap)
  simp only [Fintype.card_fin] at hdim
  exact hdim.trans (Nat.mul_le_mul_left N hS)

/-- The actual image-and-trim step has normalized viability, dimension and
recorded-rank bounds. The filter need only have minimum gain one on the
invariant target, not act as its identity. Both reference directions and
the filter decomposition are explicit premises of this auxiliary.
Supporting ALVV, arXiv:1602.08828v2, Lemma `l:er`, lines 597–622,
Figure `fig:merge-prime`, lines 1668–1670, and trimming, lines 660–697. -/
theorem isViable_intervalFamilyTrimStep_of_tensor_decomposition
    {L q p r N D : ℕ} (hD : 1 ≤ D)
    {T U : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))}
    {epsilon delta Delta xi theta : ℝ}
    (hepsilon : 0 ≤ epsilon) (hdelta0 : 0 ≤ delta) (hdelta : delta < 1)
    (hDelta : 0 ≤ Delta) (hxi : 0 < xi) (htheta : 0 < theta)
    (hTU : Submodule.IsCloseTo epsilon T U) (hUT : Submodule.IsCloseTo epsilon U T)
    (hU : ∀ v ∈ U, IsOpenMPS L q D (fun x ↦ v x))
    (F : Fin N → EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p r → Fin q))
    (Rop : Fin N → EuclideanSpace ℂ (↥((interval L p r)ᶜ) → Fin q) →L[ℂ]
      EuclideanSpace ℂ (↥((interval L p r)ᶜ) → Fin q)) :
    let Tcoord := T.map
      (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap
    ∀ (K : (EuclideanSpace ℂ (interval L p r → Fin q) ⊗[ℂ]
        EuclideanSpace ℂ (↥((interval L p r)ᶜ) → Fin q)) →L[ℂ]
      (EuclideanSpace ℂ (interval L p r → Fin q) ⊗[ℂ]
        EuclideanSpace ℂ (↥((interval L p r)ᶜ) → Fin q))),
    K = ∑ i, TensorProduct.mapL (F i) (Rop i) →
    (∀ t ∈ Tcoord, K t ∈ Tcoord) →
    (∀ z ∈ Tcoordᗮ, K z ∈ Tcoordᗮ) →
    (∀ t ∈ Tcoord, ‖t‖ ≤ ‖K t‖) →
    (∀ z ∈ Tcoordᗮ, ‖K z‖ ^ 2 ≤ Delta * ‖z‖ ^ 2) →
    ∀ S : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)),
    Submodule.IsViable delta S Tcoord →
    let alpha := Delta * delta / (1 - delta + Delta * delta)
    let error := (1 + theta) * ((1 + theta) * alpha + (1 + 1 / theta) * epsilon +
      2 * (xi * Real.sqrt (((r - p - 1 : ℕ) : ℝ) * (D ^ 2 : ℕ)))) +
      (1 + 1 / theta) * epsilon
    let output := intervalFamilyTrimStep L q p r F xi S
    Module.finrank ℂ output ≤ N * Module.finrank ℂ S ∧
      IsIntervalSpanWithRankBound L q p r (N * Module.finrank ℂ S) xi output ∧
      Submodule.IsViable error output Tcoord := by
  classical
  intro Tcoord K hdec hKT hKTo hlow hhigh S hS alpha error output
  let V := ⨆ i, S.map (F i).toLinearMap
  let basis := stdOrthonormalBasis ℂ V
  obtain ⟨hdimV, hviableV⟩ := hS.map_of_tensor_decomposition_sharp F Rop hdec
    hdelta0 hdelta hDelta hKT hKTo hlow hhigh
  have hdim : Module.finrank ℂ V ≤ N * Module.finrank ℂ S := by
    simpa only [Fintype.card_fin] using hdimV
  have halpha : 0 ≤ alpha := by
    dsimp only [alpha]
    exact div_nonneg (mul_nonneg hDelta hdelta0)
      (by nlinarith [mul_nonneg hDelta hdelta0])
  have hcloseV := (Entropy.isCloseTo_prodExt_region_iff_isViable
    (interval L p r) V T).mpr hviableV
  have htrim := isCloseTo_prodExt_intervalTrimSubspace_of_reference_weighted
    hD hepsilon halpha hxi htheta hTU hUT hU basis hcloseV
  refine ⟨(finrank_intervalTrimSubspace_le L q p r xi _).trans hdim,
    isIntervalSpanWithRankBound_intervalTrimSubspace hxi basis hdim, ?_⟩
  exact (Entropy.isCloseTo_prodExt_region_iff_isViable
    (interval L p r) output T).mp htrim

end TNLean.MPS.AreaLaw
