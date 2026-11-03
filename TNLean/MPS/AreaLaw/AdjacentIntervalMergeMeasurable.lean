/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AdjacentIntervalMerge
import QICLean.Analysis.RegionalTensorMergeMeasurable

/-!
# Borel projections of actual adjacent-interval merges

The existing tensor merge of two adjacent interval spaces has a Borel
actual orthogonal projection when the child projections are Borel. The
true viability event retains the same fixed global target and the whole
exterior of the parent interval. Source: ALVV, arXiv:1602.08828v2,
Lemma `l:t`, lines 500–523. No adaptive probability conclusion is asserted.
-/

open scoped Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- The actual adjacent-interval tensor merge has a Borel ambient
projection as a function of child spaces with Borel actual projections. -/
theorem measurable_projectionMatrix_adjacentIntervalMerge
    {X : Type*} [MeasurableSpace X] {L q p k r : ℕ} (hpk : p ≤ k) (hkr : k ≤ r)
    (S1 : X → Submodule ℂ (EuclideanSpace ℂ (interval L p k → Fin q)))
    (S2 : X → Submodule ℂ (EuclideanSpace ℂ (interval L k r → Fin q)))
    (h1 : Measurable (fun x ↦ (Matrix.toEuclideanCLM
      (n := interval L p k → Fin q) (𝕜 := ℂ)).symm (S1 x).starProjection))
    (h2 : Measurable (fun x ↦ (Matrix.toEuclideanCLM
      (n := interval L k r → Fin q) (𝕜 := ℂ)).symm (S2 x).starProjection)) :
    Measurable (fun x ↦ (Matrix.toEuclideanCLM
      (n := interval L p r → Fin q) (𝕜 := ℂ)).symm
      (adjacentIntervalMerge L q p k r hpk hkr (S1 x) (S2 x)).starProjection) := by
  exact Submodule.measurable_projectionMatrix_map_piLpCongrLeft
    (FiniteProduct.configurationCongr (fun _ : Fin L ↦ Fin q)
      (interval_union_interval hpk hkr))
    (fun x ↦ Entropy.regionTensorMerge q (interval L p k) (interval L k r)
      (disjoint_interval_interval p k r) (S1 x) (S2 x))
    (Entropy.measurable_projectionMatrix_regionTensorMerge q _ _ _ S1 S2 h1 h2)

/-- The true parent viability event for the actual adjacent merge is
Borel for the same fixed original global target, whose environment is
the whole complement of the parent interval. -/
theorem measurableSet_isViable_adjacentIntervalMerge
    {X : Type*} [MeasurableSpace X] {L q p k r : ℕ} (hpk : p ≤ k) (hkr : k ≤ r)
    (G : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (S1 : X → Submodule ℂ (EuclideanSpace ℂ (interval L p k → Fin q)))
    (S2 : X → Submodule ℂ (EuclideanSpace ℂ (interval L k r → Fin q)))
    (h1 : Measurable (fun x ↦ (Matrix.toEuclideanCLM
      (n := interval L p k → Fin q) (𝕜 := ℂ)).symm (S1 x).starProjection))
    (h2 : Measurable (fun x ↦ (Matrix.toEuclideanCLM
      (n := interval L k r → Fin q) (𝕜 := ℂ)).symm (S2 x).starProjection)) (delta : ℝ) :
    MeasurableSet {x : X | Submodule.IsViable delta
      (adjacentIntervalMerge L q p k r hpk hkr (S1 x) (S2 x))
      (G.map (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap)} :=
  Submodule.measurableSet_isViable_of_measurable_projectionMatrix
    (fun x ↦ adjacentIntervalMerge L q p k r hpk hkr (S1 x) (S2 x))
    (measurable_projectionMatrix_adjacentIntervalMerge hpk hkr S1 S2 h1 h2) delta _

end TNLean.MPS.AreaLaw
