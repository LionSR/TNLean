/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTrimming.IntervalFamilyTrimmingMeasurable
import QICLean.Analysis.Parameter.ViableNodeParameters
import QICLean.Probability.Measurable.VariableRankSampleProjection

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

## Unconditional dimensions and recorded ranks of the canonical parent

The sampled dimension is at most its nominal bound for every seed.
Applying the fixed family and collective trimming at the existing integer
count therefore gives the same recorded dimension and rank bounds on all
histories, regardless of viability. Source: ALVV, arXiv:1602.08828v2,
Figure `fig:merge-prime`, lines 1668–1670.

**Local fix (assignment and integer rounds):** The literal current-space
iteration and larger integer count are those documented in
`docs/paper-gaps/alvv16_approximation_parameters.tex`. These are recorded
spanning-vector bounds, not an all-span Schmidt-rank or runtime assertion.
-/

section

open ManyBody (interval)

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
    (σ := interval L p r → Fin q) (β := {v // v ∉ interval L p r} → Fin q)
    (X := X × Matrix.rankUnitaryProduct (Fintype.card (interval L p r → Fin q)))
    (fun x ↦ canonicalSampledIntervalInterleavedTrim L q p r D s F xi (W x.1) x.2)
    (measurable_projectionMatrix_canonicalSampledIntervalInterleavedTrim D s F xi W hW) delta _

end TNLean.MPS.AreaLaw

end

section

open ManyBody (interval)

open scoped Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- Every seed gives the dimension and recorded-generator rank bounds,
without a viability hypothesis on the input or the sampled space. -/
theorem canonicalSampledIntervalInterleavedTrim_profile
    {L q p r N D s : ℕ} (hD : 2 ≤ D) (hs : 1 ≤ s) (hN : N ≤ D ^ 2)
    (F : Fin N → EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p r → Fin q)) {xi : ℝ} (hxi : 0 < xi)
    (W : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)))
    (U : Matrix.rankUnitaryProduct (Fintype.card (interval L p r → Fin q))) :
    Module.finrank ℂ (canonicalSampledIntervalInterleavedTrim L q p r D s F xi W U) ≤
        D ^ 6 * s ^ 3 ∧
      IsIntervalSpanWithRankBound L q p r (D ^ 6 * s ^ 3) xi
        (canonicalSampledIntervalInterleavedTrim L q p r D s F xi W U) := by
  let e := (Fintype.equivFin (interval L p r → Fin q)).symm
  let P := ((Matrix.toEuclideanCLM (n := interval L p r → Fin q) (𝕜 := ℂ)).symm
    W.starProjection).reindex e.symm e.symm
  let sample := (Matrix.randomRangeSubspace P s U).map
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap
  let power := Nat.clog D (D ^ 2 * s)
  have hsampleDim : Module.finrank ℂ sample ≤ s :=
    Matrix.finrank_map_randomRangeSubspace_le P s U
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap
  have hcount : N ^ power * Module.finrank ℂ sample ≤ D ^ 6 * s ^ 3 := by
    calc
      _ ≤ (D ^ 2) ^ power * s := Nat.mul_le_mul (Nat.pow_le_pow_left hN power) hsampleDim
      _ = (D ^ power) ^ 2 * s := congrArg (fun x : ℕ ↦ x * s) (pow_right_comm D 2 power)
      _ ≤ _ := (Nat.viable_node_power_bounds hD hs).2.2.2
  have hpower : 1 ≤ power := (by omega : 2 ≤ power → 1 ≤ power)
    (Nat.viable_node_power_bounds hD hs).1
  have hpk : power - 1 + 1 = power := Nat.sub_add_cancel hpower
  have hranks := isIntervalSpanWithRankBound_intervalFamilyTrimIterate_succ hxi F sample (power - 1)
  rw [hpk] at hranks
  obtain ⟨n, hn, vectors, hspan, hrank⟩ := hranks
  refine ⟨(finrank_intervalFamilyTrimIterate_le F xi sample power).trans hcount, n,
    hn.trans hcount, vectors, hspan, ?_⟩
  intro j hj i
  exact (hrank j hj i).trans (by exact_mod_cast hcount)

end TNLean.MPS.AreaLaw

end
