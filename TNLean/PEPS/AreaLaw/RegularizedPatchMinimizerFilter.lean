/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RegularizedPatchMinimizerClipping
import QICLean.Analysis.ShiftedFilterClipping

/-!
# Clipped inverse-power filters at a regularized patch minimum

At a feasible minimum of the ordered patch objective, each regional inverse-power
filter commutes with the marginal of the same normalized output. Their common
unitary eigenbasis gives positive filter eigenvalues and a logarithmic estimate
with coefficient one half of the regional exponent. The estimate compares only
positive marginal coordinates. Repeated and empty regions are admitted.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states*, Proposition 4.1, `03-patches.tex`, `eq:patch-variational-problem`,
`eq:patch-clipped-eigenvalues`, and `eq:patch-log-ratio`; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {n : V → ℕ} {m : ℕ}

open Classical in
/-- At a feasible minimum of the ordered patch objective, each inverse-power
filter commutes with the corresponding regional state of the actual normalized
output. In a common unitary basis, its positive eigenvalues satisfy the
logarithmic bound with coefficient `a j / 2` on positive marginal coordinates.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states*, Proposition 4.1, `03-patches.tex`, `eq:patch-variational-problem`,
`eq:patch-clipped-eigenvalues`, and `eq:patch-log-ratio`; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem exists_clipped_filter_of_isMinOn_regularizedPatchObjective
    (regions : Fin m → Finset V) (hnested : Monotone regions)
    (a : Fin m → ℝ) (ha : ∀ j, 0 < a j) {b : ℝ} (hb : 0 < b)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Fin (n v.1)))
    (hΩ : ‖Ω‖ = 1)
    (x : ∀ j, Matrix (Entropy.RegionConfig n (regions j))
      (Entropy.RegionConfig n (regions j)) ℂ)
    (hx : x ∈ regularizedPatchDomain (Out := fun v ↦ Fin (n v)) regions)
    (hmin : IsMinOn
      (regularizedPatchObjective (Out := fun v ↦ Fin (n v)) regions a b Ω)
      (regularizedPatchDomain (Out := fun v ↦ Fin (n v)) regions) x) :
    let K : ∀ j : Fin m, Matrix (Entropy.RegionConfig n (regions j))
        (Entropy.RegionConfig n (regions j)) ℂ :=
      fun j ↦ (x j + b • 1) ^ (-(a j) / 2)
    let φ : EuclideanSpace ℂ (Entropy.SiteConfig n) :=
      dependentGlobalConfigIsometry
        (normalizedRegularizedPatchOutput (Out := fun v ↦ Fin (n v))
          regions a b Ω x)
    ∀ j : Fin m,
      K j * Entropy.regionState (regions j) φ =
          Entropy.regionState (regions j) φ * K j ∧
        ∃ (W : Matrix (Entropy.RegionConfig n (regions j))
            (Entropy.RegionConfig n (regions j)) ℂ)
          (l p : Entropy.RegionConfig n (regions j) → ℝ),
          Wᴴ * W = 1 ∧ (∀ i, 0 < l i) ∧
          K j = W * diagonal (fun i ↦ (l i : ℂ)) * Wᴴ ∧
          Entropy.regionState (regions j) φ =
            W * diagonal (fun i ↦ (p i : ℂ)) * Wᴴ ∧
          ∀ i k, 0 < p i → 0 < p k →
            |Real.log (l i) - Real.log (l k)| ≤
              a j / 2 * |Real.log (p i) - Real.log (p k)| := by
  intro K φ j
  obtain ⟨U, s, p, lam, hU, _, hxdiag, hρdiag, hlam, _, hclip⟩ :=
    exists_unitary_diagonal_clipped_of_isMinOn_regularizedPatchObjective
      regions hnested a ha hb Ω hΩ x hx hmin j
  simpa only [K, φ, dependentGlobalConfigIsometry_normalizedRegularizedPatchOutput,
    normalizedRegularizedPatchMarginal_eq_regionState_patchState] using
    Matrix.exists_clipped_rpow_add_smul_one_of_diagonal_max
      hU hxdiag hρdiag hb hlam (ha j).le hclip

end TNLean.PEPS
