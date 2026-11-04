/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.IntervalUnion
import QICLean.Entropy.RegionalTensorMerge

/-!
# Merging viable spaces on adjacent physical intervals

The two input spaces and the actual parent candidate all refer to the same
global target in the original chain. Their environment factors include the
whole complement of the corresponding interval. The target may be entangled
across the children and exterior. This specializes ALVV, arXiv:1602.08828v2,
Lemma `l:t`, lines 500–523, to the actual chain coordinates.
No recursively selected viable family or sampling step is asserted.
-/

namespace TNLean.MPS.AreaLaw

/-- The actual tensor product candidate on the parent interval, transported
by the union configuration equivalence. Supporting ALVV,
arXiv:1602.08828v2, Lemma `l:t`, lines 500–523. -/
noncomputable def adjacentIntervalMerge (L q p k r : ℕ) (hpk : p ≤ k) (hkr : k ≤ r)
    (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L p k → Fin q)))
    (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k r → Fin q))) :
    Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)) :=
  (Entropy.regionTensorMerge q (interval L p k) (interval L k r)
    (disjoint_interval_interval p k r) S1 S2).map
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (FiniteProduct.configurationCongr (fun _ : Fin L ↦ Fin q)
          (interval_union_interval hpk hkr))).toLinearEquiv.toLinearMap

/-- Viable spaces on actual adjacent intervals merge with the sum of their
errors for the same original global target. This is ALVV,
arXiv:1602.08828v2, Lemma `l:t`, lines 500–523, in chain coordinates. -/
theorem isViable_adjacentIntervalMerge {L q p k r : ℕ} (hpk : p ≤ k) (hkr : k ≤ r)
    {delta1 delta2 : ℝ}
    (G : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L p k → Fin q)))
    (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k r → Fin q)))
    (h1 : Submodule.IsViable delta1 S1
      (G.map (Entropy.regionTensorCoordinates q (interval L p k)).toLinearEquiv.toLinearMap))
    (h2 : Submodule.IsViable delta2 S2
      (G.map (Entropy.regionTensorCoordinates q (interval L k r)).toLinearEquiv.toLinearMap)) :
    Submodule.IsViable (delta1 + delta2) (adjacentIntervalMerge L q p k r hpk hkr S1 S2)
      (G.map (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap) :=
  Entropy.isViable_region_congr (interval_union_interval hpk hkr) G _
    (Entropy.isViable_regionTensorMerge (interval L p k) (interval L k r)
      (disjoint_interval_interval p k r) G S1 S2 h1 h2)

/-- The actual parent candidate has dimension at most the product of the
child dimensions. Supporting ALVV, arXiv:1602.08828v2, Lemma `l:t`, lines 500–523. -/
theorem finrank_adjacentIntervalMerge_le {L q p k r : ℕ} (hpk : p ≤ k) (hkr : k ≤ r)
    (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L p k → Fin q)))
    (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k r → Fin q))) :
    Module.finrank ℂ (adjacentIntervalMerge L q p k r hpk hkr S1 S2) ≤
      Module.finrank ℂ S1 * Module.finrank ℂ S2 :=
  (Submodule.finrank_map_le _ _).trans
    (Entropy.finrank_regionTensorMerge_le q _ _ (disjoint_interval_interval p k r) S1 S2)

end TNLean.MPS.AreaLaw
