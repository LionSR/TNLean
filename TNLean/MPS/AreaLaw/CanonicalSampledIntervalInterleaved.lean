/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.IntervalFamilyTrimmingMeasurable

/-!
# A Borel canonical sample followed by the literal interleaved iteration

The canonical range-basis sample is transported back to the original
interval coordinates. Every subsequent round is the existing interval
family application followed by its actual collective trim. A fixed finite
product of unitary groups provides the random coordinates for all possible
candidate ranks. No joint measurability of an arbitrary chosen basis is
assumed. Source: ALVV, arXiv:1602.08828v2, Lemma `l:rs`, lines 530–558,
and Figure `fig:merge-prime`, lines 1668–1670. This is a measurable
realization of the parent operation, not an adaptive success theorem.

**Local fix (assignment and integer rounds):** Each round acts on the
current space with the larger integer count recorded in
`docs/paper-gaps/alvv16_approximation_parameters.tex`.
-/

open MeasureTheory
open scoped Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- Sample the actual candidate range through its canonical orthonormal
coordinates, then apply the existing literal family-and-trim iterate.
The unitary product is fixed before the candidate rank is known. -/
noncomputable def canonicalSampledIntervalInterleavedTrim (L q p r D s : ℕ) {N : ℕ}
    (F : Fin N → EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p r → Fin q)) (xi : ℝ)
    (W : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)))
    (U : Matrix.rankUnitaryProduct (Fintype.card (interval L p r → Fin q))) :
    Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)) :=
  let e := (Fintype.equivFin (interval L p r → Fin q)).symm
  let P := (Matrix.toEuclideanCLM (n := interval L p r → Fin q) (𝕜 := ℂ)).symm W.starProjection
  let sample := (Matrix.randomRangeSubspace (P.reindex e.symm e.symm) s U).map
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap
  intervalFamilyTrimIterate L q p r F xi sample (Nat.clog D (D ^ 2 * s))

/-- The actual canonical sampled parent has a jointly Borel orthogonal
projection whenever the constructed candidate's actual projection is Borel. -/
theorem measurable_projectionMatrix_canonicalSampledIntervalInterleavedTrim
    {X : Type*} [MeasurableSpace X] {L q p r N : ℕ} (D s : ℕ)
    (F : Fin N → EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p r → Fin q)) (xi : ℝ)
    (W : X → Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)))
    (hW : Measurable (fun x ↦ (Matrix.toEuclideanCLM
      (n := interval L p r → Fin q) (𝕜 := ℂ)).symm (W x).starProjection)) :
    Measurable (fun x : X × Matrix.rankUnitaryProduct (Fintype.card (interval L p r → Fin q)) ↦
      (Matrix.toEuclideanCLM (n := interval L p r → Fin q) (𝕜 := ℂ)).symm
        (canonicalSampledIntervalInterleavedTrim L q p r D s F xi (W x.1) x.2).starProjection) := by
  let e := (Fintype.equivFin (interval L p r → Fin q)).symm
  let P := fun x ↦ ((Matrix.toEuclideanCLM (n := interval L p r → Fin q) (𝕜 := ℂ)).symm
    (W x).starProjection).reindex e.symm e.symm
  have hP : Measurable P := by
    have hc : Continuous (fun M : Matrix (interval L p r → Fin q)
        (interval L p r → Fin q) ℂ ↦ M.reindex e.symm e.symm) := by
      change Continuous (fun M : Matrix (interval L p r → Fin q)
        (interval L p r → Fin q) ℂ ↦ fun i j ↦ M (e i) (e j))
      fun_prop
    exact hc.measurable.comp hW
  let sample := fun x : X × Matrix.rankUnitaryProduct (Fintype.card (interval L p r → Fin q)) ↦
    (Matrix.randomRangeSubspace (P x.1) s x.2).map
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap
  have hsample0 := (Matrix.measurable_randomRangeSubspace_projection s).comp
    ((hP.comp measurable_fst).prodMk measurable_snd)
  have hsample := Submodule.measurable_projectionMatrix_map_piLpCongrLeft e
    (fun x : X × Matrix.rankUnitaryProduct (Fintype.card (interval L p r → Fin q)) ↦
      Matrix.randomRangeSubspace (P x.1) s x.2) hsample0
  exact measurable_projectionMatrix_intervalFamilyTrimIterate F xi sample hsample
    (Nat.clog D (D ^ 2 * s))

/-- The exact sampled interleaved parent has a Borel original viability
event for the same fixed global target and whole parent exterior. -/
theorem measurableSet_isViable_canonicalSampledIntervalInterleavedTrim
    {X : Type*} [MeasurableSpace X] {L q p r N : ℕ} (D s : ℕ)
    (F : Fin N → EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p r → Fin q)) (xi : ℝ)
    (W : X → Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)))
    (hW : Measurable (fun x ↦ (Matrix.toEuclideanCLM
      (n := interval L p r → Fin q) (𝕜 := ℂ)).symm (W x).starProjection))
    (delta : ℝ) (G : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) :
    MeasurableSet {x : X × Matrix.rankUnitaryProduct (Fintype.card (interval L p r → Fin q)) |
      Submodule.IsViable delta
        (canonicalSampledIntervalInterleavedTrim L q p r D s F xi (W x.1) x.2)
        (G.map (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap)} :=
  Submodule.measurableSet_isViable_of_measurable_projectionMatrix
    (σ := interval L p r → Fin q) (β := ↥((interval L p r)ᶜ) → Fin q)
    (X := X × Matrix.rankUnitaryProduct (Fintype.card (interval L p r → Fin q)))
    (fun x ↦ canonicalSampledIntervalInterleavedTrim L q p r D s F xi (W x.1) x.2)
    (measurable_projectionMatrix_canonicalSampledIntervalInterleavedTrim D s F xi W hW) delta _

end TNLean.MPS.AreaLaw
