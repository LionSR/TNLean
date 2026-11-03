/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.CanonicalHalfSampledIntervalParent

/-!
# The last untrimmed image of an interval run

The candidate projection, finite sequence and stopped iteration are exactly
those of the complete interval parent. This names its last full-family
image before the terminal collective trim. It has no spectral target or
energy-center parameter. Supporting ALVV, arXiv:1602.08828v2,
lines 749–755 and 1801–1813.

**Local fix (repeated sampling and terminal amplification):** The image
belongs to the corrected repeated-sampling operation, including a terminal
full-family image even when the initial rank is below the threshold. See
https://sirui-lu.com/QICLean/paper-gaps/alvv16_bootstrap_constants.pdf.
-/

open scoped Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- The actual last full-family image of the prescribed stopped interval
run, before its final collective trim. All family, cut and sequence data
are the same as in the complete parent. Supporting ALVV,
arXiv:1602.08828v2, lines 749–755 and 1801–1813. -/
noncomputable def canonicalHalfSampledIntervalImage (L q p r D threshold rounds : ℕ)
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
  let Q := Entropy.canonicalHalfSampleTrimIterate (n := fun _ : interval L p r ↦ q)
    e (intervalTrimCut L p r) xi (r - p - 1) D threshold (Entropy.nativeFamilyMatrix e F) P
    (Entropy.halfSamplingSeedSequence U) rounds
  (Matrix.toEuclideanLin (Matrix.familySupportProj
    (fun i ↦ Entropy.nativeFamilyMatrix e F i * Q))).range

end TNLean.MPS.AreaLaw
