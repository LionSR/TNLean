/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.IntervalFamilyTrimmingIteration
import QICLean.Analysis.FiniteFamilyImageProjection
import QICLean.Analysis.CanonicalSamplingTrimmingMeasurable
import QICLean.Analysis.ViableSubspaceTensorProjectionMeasurable

/-!
# Borel projections of the literal interleaved interval iteration

The original implementation applies the fixed operator family to the
current space and collectively trims an internally chosen orthonormal
basis of that actual image. Basis invariance identifies this literal step
with the canonical Borel range trim. Thus every finite iterate has a
Borel actual orthogonal projection and a Borel true viability event.

Source: ALVV, arXiv:1602.08828v2, Figure `fig:merge-prime`, lines 1668–1670.
The current-space assignment is retained at every round, as corrected in
`docs/paper-gaps/alvv16_approximation_parameters.tex`. No final-only trim
or adaptive probability conclusion is substituted.
-/

open scoped Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- The existing orthonormal-basis interval step is exactly the canonical
range trim of the actual family-image projection in any fixed coordinates. -/
theorem intervalFamilyTrimStep_eq_trimMatrixRange
    {L q p r N d : ℕ}
    (e : Fin d ≃ (interval L p r → Fin q))
    (F : Fin N → EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p r → Fin q)) (xi : ℝ)
    (S : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q))) :
    intervalFamilyTrimStep L q p r F xi S =
      Entropy.trimMatrixRange e (intervalTrimCut L p r) xi (r - p - 1)
        ((Matrix.toEuclideanCLM (n := interval L p r → Fin q) (𝕜 := ℂ)).symm
          (⨆ i, S.map (F i).toLinearMap).starProjection) := by
  let V := ⨆ i, S.map (F i).toLinearMap
  let P := (Matrix.toEuclideanCLM (n := interval L p r → Fin q) (𝕜 := ℂ)).symm V.starProjection
  have hrange : (Matrix.toEuclideanLin P).range = V := by
    change LinearMap.range
      ((Matrix.toEuclideanCLM (n := interval L p r → Fin q) (𝕜 := ℂ)) P).toLinearMap = V
    rw [StarAlgEquiv.apply_symm_apply]
    exact Submodule.range_starProjection V
  let b := (stdOrthonormalBasis ℂ V).map
    (LinearIsometryEquiv.ofEq V (Matrix.toEuclideanLin P).range hrange.symm)
  have h := Entropy.trimMatrixRange_eq_of_orthonormalBasis e (intervalTrimCut L p r)
    xi (r - p - 1) P b
  change Entropy.trimSubspace (intervalTrimCut L p r) xi
      (fun i ↦ ((stdOrthonormalBasis ℂ V) i : EuclideanSpace ℂ (interval L p r → Fin q)))
      (r - p - 1) = Entropy.trimMatrixRange e (intervalTrimCut L p r) xi (r - p - 1) P
  simpa only [b, OrthonormalBasis.map_apply, LinearIsometryEquiv.coe_ofEq_apply] using h.symm

/-- The actual existing family step has a Borel orthogonal projection
for every constructed current space with Borel actual projection. -/
theorem measurable_projectionMatrix_intervalFamilyTrimStep
    {X : Type*} [MeasurableSpace X] {L q p r N : ℕ}
    (F : Fin N → EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p r → Fin q)) (xi : ℝ)
    (S : X → Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)))
    (hS : Measurable (fun x ↦ (Matrix.toEuclideanCLM
      (n := interval L p r → Fin q) (𝕜 := ℂ)).symm (S x).starProjection)) :
    Measurable (fun x ↦ (Matrix.toEuclideanCLM
      (n := interval L p r → Fin q) (𝕜 := ℂ)).symm
      (intervalFamilyTrimStep L q p r F xi (S x)).starProjection) := by
  let e := (Fintype.equivFin (interval L p r → Fin q)).symm
  have h := (Entropy.measurable_projectionMatrix_trimMatrixRange e
    (intervalTrimCut L p r) xi (r - p - 1)).comp
      (Matrix.measurable_projectionMatrix_iSup_map F S hS)
  simpa only [intervalFamilyTrimStep_eq_trimMatrixRange e, Function.comp_def] using h

/-- Every finite literal interleaved iterate has a Borel actual projection.
Each successor acts on the preceding space and performs its own trim. -/
theorem measurable_projectionMatrix_intervalFamilyTrimIterate
    {X : Type*} [MeasurableSpace X] {L q p r N : ℕ}
    (F : Fin N → EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p r → Fin q)) (xi : ℝ)
    (S : X → Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)))
    (hS : Measurable (fun x ↦ (Matrix.toEuclideanCLM
      (n := interval L p r → Fin q) (𝕜 := ℂ)).symm (S x).starProjection)) (j : ℕ) :
    Measurable (fun x ↦ (Matrix.toEuclideanCLM
      (n := interval L p r → Fin q) (𝕜 := ℂ)).symm
      (intervalFamilyTrimIterate L q p r F xi (S x) j).starProjection) := by
  induction j with
  | zero => exact hS
  | succ j ih =>
    exact measurable_projectionMatrix_intervalFamilyTrimStep F xi
      (fun x ↦ intervalFamilyTrimIterate L q p r F xi (S x) j) ih

/-- The original viability event for the literal finite iterate is Borel
for the same fixed global target, with the whole interval exterior retained. -/
theorem measurableSet_isViable_intervalFamilyTrimIterate
    {X : Type*} [MeasurableSpace X] {L q p r N : ℕ}
    (F : Fin N → EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p r → Fin q)) (xi : ℝ)
    (S : X → Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)))
    (hS : Measurable (fun x ↦ (Matrix.toEuclideanCLM
      (n := interval L p r → Fin q) (𝕜 := ℂ)).symm (S x).starProjection))
    (j : ℕ) (delta : ℝ) (G : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) :
    MeasurableSet {x : X | Submodule.IsViable delta
      (intervalFamilyTrimIterate L q p r F xi (S x) j)
      (G.map (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap)} :=
  Submodule.measurableSet_isViable_of_measurable_projectionMatrix
    (fun x ↦ intervalFamilyTrimIterate L q p r F xi (S x) j)
    (measurable_projectionMatrix_intervalFamilyTrimIterate F xi S hS j) delta _

end TNLean.MPS.AreaLaw
