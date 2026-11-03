/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.CanonicalSampledIntervalInterleaved
import QICLean.Analysis.ViableNodeParameters
import QICLean.Analysis.RandomRangeSubspaceDimension

/-!
# Unconditional dimensions and recorded ranks of the canonical parent

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
