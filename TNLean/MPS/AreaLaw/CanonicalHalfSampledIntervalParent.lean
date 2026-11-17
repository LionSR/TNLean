/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.IntervalCollectiveTrimming
import QICLean.Analysis.CanonicalHalfSamplingParent
import QICLean.Analysis.StoppedHalfSamplingSeed

/-!
# The complete stopped half-sampling parent on an actual interval

The actual candidate projection is expressed in fixed finite coordinates.
A prescribed finite sequence supplies fresh samples for the stopped native
iteration. Its terminal full-family image and collective trim use the same
interval cuts and the same operator family. Supporting ALVV,
arXiv:1602.08828v2, the resampling description at lines 749–755 and
reference trimming at lines 1801–1813.

**Local fix (repeated sampling and terminal amplification):** This is the
corrected repeated-sampling parent, including its terminal full-family
image and trim, rather than the sample-once Figure `fig:merge-prime`.
The correction is recorded at
https://sirui-lu.com/QICLean/paper-gaps/alvv16_bootstrap_constants.pdf.
No running-time estimate is asserted.
-/

open MeasureTheory
open scoped Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- The literal native complete parent, using the candidate's actual
projection, the interval's internal cuts and the fixed finite sequence
extended by identity coordinates. Supporting ALVV, arXiv:1602.08828v2,
lines 749–755 and 1801–1813. -/
noncomputable def canonicalHalfSampledIntervalParent (L q p r D threshold rounds : ℕ)
    {N : ℕ} (F : Fin N →
      EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p r → Fin q)) (xi : ℝ)
    (W : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)))
    (U : Fin rounds → Matrix.rankUnitaryProduct
      (Fintype.card (interval L p r → Fin q))) :
    Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)) :=
  let e := (Fintype.equivFin (interval L p r → Fin q)).symm
  let P := ((Matrix.toEuclideanCLM (n := interval L p r → Fin q) (𝕜 := ℂ)).symm
    W.starProjection).reindex e.symm e.symm
  Entropy.canonicalHalfSamplingParent (n := fun _ : interval L p r ↦ q)
    e (intervalTrimCut L p r) xi (r - p - 1) D threshold rounds F P
    (Entropy.halfSamplingSeedSequence U)

/-- The literal finite-seed parent has measurable actual projection for
any candidate family with measurable projection. No successful-sampling
or measurable-basis hypothesis is supplied. Supporting ALVV,
arXiv:1602.08828v2, lines 749–755 and 1801–1813. -/
theorem measurable_projectionMatrix_canonicalHalfSampledIntervalParent
    {X : Type*} [MeasurableSpace X] {L q p r N : ℕ}
    (D threshold rounds : ℕ)
    (F : Fin N → EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p r → Fin q)) (xi : ℝ)
    (W : X → Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)))
    (hW : Measurable (fun x ↦ (Matrix.toEuclideanCLM
      (n := interval L p r → Fin q) (𝕜 := ℂ)).symm (W x).starProjection)) :
    Measurable (fun x : X × (Fin rounds → Matrix.rankUnitaryProduct
        (Fintype.card (interval L p r → Fin q))) ↦
      (Matrix.toEuclideanCLM (n := interval L p r → Fin q) (𝕜 := ℂ)).symm
        (canonicalHalfSampledIntervalParent L q p r D threshold rounds F xi
          (W x.1) x.2).starProjection) := by
  let e := (Fintype.equivFin (interval L p r → Fin q)).symm
  let P := fun x ↦ ((Matrix.toEuclideanCLM
    (n := interval L p r → Fin q) (𝕜 := ℂ)).symm (W x).starProjection).reindex e.symm e.symm
  let input := fun x : X × (Fin rounds → Matrix.rankUnitaryProduct
      (Fintype.card (interval L p r → Fin q))) ↦
    (P x.1, Entropy.halfSamplingSeedSequence x.2)
  have hP : Measurable P :=
    ((continuous_id : Continuous (fun M : Matrix (interval L p r → Fin q)
      (interval L p r → Fin q) ℂ ↦ M)).matrix_reindex e.symm e.symm).measurable.comp hW
  have hInput : Measurable input := (hP.comp measurable_fst).prodMk
    ((Entropy.measurable_halfSamplingSeedSequence _ rounds).comp measurable_snd)
  exact (Entropy.measurable_projectionMatrix_canonicalHalfSamplingParent
    (n := fun _ : interval L p r ↦ q) e (intervalTrimCut L p r) xi
    (r - p - 1) D threshold rounds F).comp (f := input) hInput

end TNLean.MPS.AreaLaw
