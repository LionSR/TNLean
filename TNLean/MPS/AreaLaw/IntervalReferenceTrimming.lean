/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.IntervalCollectiveTrimming
import QICLean.Analysis.ViableSubspaceReferenceTrimming

/-!
# Weighted reference bounds for interval trimming

A common whole-chain MPS reference bounds the actual collective trim on
an arbitrary interval, retaining its entire exterior. The reference rank
is the square of its whole-chain bond bound. The robustness weight is
free, so the coefficient of the incoming viability error can be chosen
arbitrarily close to one.

This supports the reference argument in ALVV, arXiv:1602.08828v2,
proof of `t:alg1`, lines 1801–1813.

**Local fix (collective trimming constant):** The increment is the proved
`2 ξ √(m b)`; see
https://sirui-lu.com/QICLean/paper-gaps/alvv16_trimming_constant.pdf.
-/

open scoped InnerProductSpace

namespace TNLean.MPS.AreaLaw

/-- Transport one actual reference vector into interval/exterior
coordinates without discarding the exterior. Its internal-cut rank is
bounded by the squared whole-chain bond. Supporting ALVV,
arXiv:1602.08828v2, collective trimming, lines 660–697, and the reference
argument, lines 1801–1805. -/
theorem schmidtRank_cutEnvVector_interval_reference_le
    {L q D : ℕ} (hD : 1 ≤ D)
    {U : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))}
    (hU : ∀ v ∈ U, IsOpenMPS L q D (fun x ↦ v x)) (p r : ℕ)
    {t : EuclideanSpace ℂ
      ((interval L p r → Fin q) × (↥((interval L p r)ᶜ) → Fin q))}
    (ht : t ∈ U.map
      (Entropy.regionConfigurationSplit q (interval L p r)).toLinearEquiv.toLinearMap)
    (j : ℕ) (hj : j < r - p - 1) :
    Matrix.schmidtRank (WithLp.ofLp
      (Entropy.cutEnvVector (n := fun _ : interval L p r ↦ q)
        (intervalTrimCut L p r j) t)) ≤ D ^ 2 := by
  obtain ⟨v, hv, rfl⟩ := ht
  change Matrix.schmidtRank (WithLp.ofLp
    (Entropy.cutEnvVector (n := fun _ : interval L p r ↦ q)
      (intervalTrimCut L p r j)
      (Entropy.regionConfigurationSplit q (interval L p r) v))) ≤ D ^ 2
  simpa only [max_eq_right hD] using
    schmidtRank_cutEnvVector_interval_le (hU v hv) p r j (by omega)

/-- The actual collective interval trim has a target-relative bound with
a free positive robustness weight. The one reference controls the whole
exterior at every internal cut. Supporting ALVV, arXiv:1602.08828v2,
proof of `t:alg1`, lines 1801–1813. -/
theorem isCloseTo_prodExt_intervalTrimSubspace_of_reference_weighted
    {L q p r s D : ℕ} (hD : 1 ≤ D)
    {G U : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))}
    {epsilon delta xi theta : ℝ} (hepsilon : 0 ≤ epsilon)
    (hdelta : 0 ≤ delta) (hxi : 0 < xi) (htheta : 0 < theta)
    (hGU : Submodule.IsCloseTo epsilon G U) (hUG : Submodule.IsCloseTo epsilon U G)
    (hU : ∀ v ∈ U, IsOpenMPS L q D (fun x ↦ v x))
    {S : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q))}
    (u : OrthonormalBasis (Fin s) ℂ S)
    (hS : Submodule.IsCloseTo delta
      (Submodule.prodExt S (↥((interval L p r)ᶜ) → Fin q))
      (G.map (Entropy.regionConfigurationSplit q (interval L p r)).toLinearEquiv.toLinearMap)) :
    Submodule.IsCloseTo
      ((1 + theta) * ((1 + theta) * delta + (1 + 1 / theta) * epsilon +
        2 * (xi * Real.sqrt (((r - p - 1 : ℕ) : ℝ) * (D ^ 2 : ℕ)))) +
        (1 + 1 / theta) * epsilon)
      (Submodule.prodExt (intervalTrimSubspace L q p r xi (fun k ↦ (u k : _)))
        (↥((interval L p r)ᶜ) → Fin q))
      (G.map (Entropy.regionConfigurationSplit q (interval L p r)).toLinearEquiv.toLinearMap) := by
  let F := Entropy.regionConfigurationSplit q (interval L p r)
  have hGUmap := (Submodule.isCloseTo_map_iff F).mpr hGU
  have hUGmap := (Submodule.isCloseTo_map_iff F).mpr hUG
  have hrank : ∀ t ∈ U.map F.toLinearEquiv.toLinearMap, ∀ j < r - p - 1,
      Matrix.schmidtRank (WithLp.ofLp
        (Entropy.cutEnvVector (n := fun _ : interval L p r ↦ q)
          (intervalTrimCut L p r j) t)) ≤ D ^ 2 := by
    intro t ht j hj
    exact schmidtRank_cutEnvVector_interval_reference_le hD hU p r ht j hj
  exact Entropy.isCloseTo_prodExt_trimSubspace_of_reference_weighted
    (intervalTrimCut_mono L p r) hxi hdelta hepsilon htheta u hS hGUmap hUGmap hrank

end TNLean.MPS.AreaLaw
