/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.IntervalFamilyTrimmingIteration
import QICLean.Analysis.InterleavedTrimmingParameters

/-!
# Reference budgets for actual interleaved family trims

A target-relative reference error quadratic in a guaranteed overlap and
a threshold error linear in that overlap control every actual trimming
round. The target is the same throughout this auxiliary. If that target
is a clipped physical low-energy space, comparison with the original
ground space remains a separate accuracy budget.

This supports ALVV, arXiv:1602.08828v2, Figure `fig:merge-prime`,
lines 1668–1670, and the reference argument, lines 1801–1805.
It neither chooses physical cutoff parameters nor asserts an adaptive
sampling probability.

**Local fix (recursive assignment):** Each round uses its current space;
see `docs/paper-gaps/alvv16_approximation_parameters.tex`.
-/

open scoped TensorProduct InnerProductSpace

namespace TNLean.MPS.AreaLaw

/-- Explicit quadratic reference and linear threshold budgets control all
actual interleaved iterates through the normalized scalar recurrence.
The invariant spectral target need not be an eigenspace on which the
filter is scalar. The physical target/reference construction and choice
of a successful initial sample remain separate. Supporting ALVV,
arXiv:1602.08828v2, Figure `fig:merge-prime`, lines 1668–1670,
and the reference argument, lines 1801–1805. -/
theorem isViable_intervalFamilyTrimIterate_of_reference_budgets
    {L q p r N D : ℕ} (hD : 1 ≤ D)
    {T U : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))}
    {a epsilon Delta xi : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1)
    (hepsilon : 0 ≤ epsilon) (hDelta : 0 ≤ Delta) (hxi : 0 < xi)
    (hepsilonBudget : epsilon ≤ a ^ 2 / 16384)
    (hxiBudget : xi * Real.sqrt (((r - p - 1 : ℕ) : ℝ) * (D ^ 2 : ℕ)) ≤ a / 256)
    (hTU : Submodule.IsCloseTo epsilon T U) (hUT : Submodule.IsCloseTo epsilon U T)
    (hU : ∀ v ∈ U, IsOpenMPS L q D (fun x ↦ v x))
    (F : Fin N → EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p r → Fin q))
    (Rop : Fin N → EuclideanSpace ℂ (↥((interval L p r)ᶜ) → Fin q) →L[ℂ]
      EuclideanSpace ℂ (↥((interval L p r)ᶜ) → Fin q)) :
    let Tcoord := T.map
      (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap
    ∀ (K : (EuclideanSpace ℂ (interval L p r → Fin q) ⊗[ℂ]
        EuclideanSpace ℂ (↥((interval L p r)ᶜ) → Fin q)) →L[ℂ]
      (EuclideanSpace ℂ (interval L p r → Fin q) ⊗[ℂ]
        EuclideanSpace ℂ (↥((interval L p r)ᶜ) → Fin q))),
    K = ∑ i, TensorProduct.mapL (F i) (Rop i) →
    (∀ t ∈ Tcoord, K t ∈ Tcoord) →
    (∀ z ∈ Tcoordᗮ, K z ∈ Tcoordᗮ) →
    (∀ t ∈ Tcoord, ‖t‖ ≤ ‖K t‖) →
    (∀ z ∈ Tcoordᗮ, ‖K z‖ ^ 2 ≤ Delta * ‖z‖ ^ 2) →
    ∀ delta : ℕ → ℝ, (∀ j, 0 ≤ delta j) → (∀ j, delta j < 1) →
    (∀ j, Delta * delta j / (1 - delta j + Delta * delta j) + a / 16 ≤ delta (j + 1)) →
    ∀ S : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)),
    Submodule.IsViable (delta 0) S Tcoord →
    ∀ j, Submodule.IsViable (delta j) (intervalFamilyTrimIterate L q p r F xi S j) Tcoord := by
  intro Tcoord K hdec hKT hKTo hlow hhigh delta hdelta0 hdelta herror S hS j
  have htheta : 0 < a / 64 := by positivity
  apply isViable_intervalFamilyTrimIterate_of_tensor_decomposition
    hD hepsilon hDelta hxi htheta hTU hUT hU F Rop
    K hdec hKT hKTo hlow hhigh delta hdelta0 hdelta ?_ S hS j
  intro i
  have hden : 0 < 1 - delta i + Delta * delta i := by
    nlinarith [mul_nonneg hDelta (hdelta0 i), hdelta i]
  have hf0 : 0 ≤ Delta * delta i / (1 - delta i + Delta * delta i) :=
    div_nonneg (mul_nonneg hDelta (hdelta0 i)) hden.le
  have hf1 : Delta * delta i / (1 - delta i + Delta * delta i) ≤ 1 := by
    apply (div_le_one hden).mpr
    linarith [hdelta i]
  have hbudget := Real.weighted_reference_trim_error_le_filter_add ha ha1 hf0 hf1
    hepsilon hepsilonBudget (mul_nonneg hxi.le (Real.sqrt_nonneg _)) hxiBudget
  exact hbudget.trans (herror i)

end TNLean.MPS.AreaLaw
