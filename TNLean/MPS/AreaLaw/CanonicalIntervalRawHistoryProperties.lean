/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.CanonicalIntervalRawHistory

/-!
# Initial viability recorded by the actual interval history

The original-target history tests the initial state as well as every later
state. Its initial projection is the candidate's actual orthogonal
projection, so membership in this history gives initial viability directly.
Supporting ALVV, arXiv:1602.08828v2, lines 749–755 and 1777–1817.
-/

open scoped Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- The literal original-target history records viability of the actual
initial candidate. This follows from its zeroth-state test and the exact
transported range of the candidate projection. Supporting ALVV,
arXiv:1602.08828v2, lines 749–755 and 1777–1817. -/
theorem isViable_of_mem_canonicalHalfSampledIntervalHistory
    (L q p r D threshold rounds : ℕ) {N : ℕ}
    (F : Fin N → EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p r → Fin q)) (xi : ℝ)
    (W : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)))
    (G : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (U : Fin rounds → Matrix.rankUnitaryProduct
      (Fintype.card (interval L p r → Fin q)))
    (hU : U ∈ canonicalHalfSampledIntervalHistory L q p r D threshold rounds F xi W G) :
    Submodule.IsViable 0.04 W
      (G.map (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap) := by
  let e := (Fintype.equivFin (interval L p r → Fin q)).symm
  let P := ((Matrix.toEuclideanCLM (n := interval L p r → Fin q) (𝕜 := ℂ)).symm
    W.starProjection).reindex e.symm e.symm
  let Graw := G.map
    (Entropy.regionConfigurationSplit q (interval L p r)).toLinearEquiv.toLinearMap
  have h0 : Submodule.IsCloseTo 0.04
      (Submodule.prodExt ((Matrix.toEuclideanLin P).range.map
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap)
          (↥((interval L p r)ᶜ) → Fin q)) Graw :=
    hU.1 ⟨0, Nat.zero_lt_succ rounds⟩
  have hRange : (Matrix.toEuclideanLin P).range.map
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap = W := by
    change (Matrix.toEuclideanLin
      (((Matrix.toEuclideanCLM (n := interval L p r → Fin q) (𝕜 := ℂ)).symm
        W.starProjection).submatrix e e)).range.map
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap = W
    rw [Matrix.map_range_toEuclideanLin_submatrix]
    change ((Matrix.toEuclideanCLM (n := interval L p r → Fin q) (𝕜 := ℂ))
      ((Matrix.toEuclideanCLM (n := interval L p r → Fin q) (𝕜 := ℂ)).symm
        W.starProjection)).toLinearMap.range = W
    rw [StarAlgEquiv.apply_symm_apply, Submodule.range_starProjection]
  rw [hRange] at h0
  exact (Entropy.isCloseTo_prodExt_region_iff_isViable (interval L p r) W G).mp h0

end TNLean.MPS.AreaLaw
