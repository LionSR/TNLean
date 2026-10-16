/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.ShiftedDensityClipping
import QICLean.Entropy.PatchNormalizedFirstVariation
import TNLean.PEPS.AreaLaw.RegularizedPatchListCoordinates

/-!
# Common eigenbases at regularized patch minima

At every feasible minimum of the ordered patch objective, each regional density
and the corresponding marginal of the normalized output have a common unitary
eigenbasis. Their eigenvalues satisfy the clipped formula with a positive
multiplier at most one. Regions are nested in increasing index order; repeated
regions retain separate density variables.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states*, Proposition 4.1, `03-patches.tex`, lines 68–99 and 115–200,
`eq:patch-stationarity-commutation` and `eq:patch-clipped-eigenvalues`;
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {n : V → ℕ} {m : ℕ}

/-- Every density in a feasible minimizing tuple has a common unitary eigenbasis
with its normalized regional marginal. In that basis the eigenvalues satisfy
`s_i + b = max (p_i / λ) b`, with `0 < λ ≤ 1`.
The input is a unit vector, the weights and shift are positive, and the regions
are nested. No full-rank condition on the densities or their marginals is imposed.

Source: polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 68–99 and
115–200, `eq:patch-stationarity-commutation`, `eq:patch-kkt`, and
`eq:patch-clipped-eigenvalues`. -/
theorem exists_unitary_diagonal_clipped_of_isMinOn_regularizedPatchObjective
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
    ∀ j : Fin m,
      ∃ (U : Matrix (Entropy.RegionConfig n (regions j))
          (Entropy.RegionConfig n (regions j)) ℂ)
        (s p : Entropy.RegionConfig n (regions j) → ℝ) (lam : ℝ),
        Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
        x j = U * diagonal (fun i ↦ (s i : ℂ)) * Uᴴ ∧
        normalizedRegularizedPatchMarginal (Out := fun v ↦ Fin (n v))
            regions a b Ω x (regions j) =
          U * diagonal (fun i ↦ (p i : ℂ)) * Uᴴ ∧
        0 < lam ∧ lam ≤ 1 ∧ ∀ i, s i + b = max (p i / lam) b := by
  classical
  let l := regularizedPatchFactorList regions a x
  have hexp : ∀ f ∈ l, 0 < f.exponent := by
    simpa only [l, regularizedPatchFactorList, List.mem_reverse,
      List.forall_mem_ofFn_iff] using ha
  have hden : ∀ f ∈ l, f.density.PosSemidef ∧ f.density.trace = 1 := by
    simpa only [l, regularizedPatchFactorList, List.mem_reverse,
      List.forall_mem_ofFn_iff] using
      (show ∀ j, (x j).PosSemidef ∧ (x j).trace = 1 from hx)
  have hnest : l.Pairwise (fun g g' ↦ g'.region ⊆ g.region) :=
    List.pairwise_reverse.mpr
      (List.pairwise_ofFn.mpr fun i j hij ↦ hnested hij.le)
  have hminList := isPatchMinimizer_regularizedPatchFactorList regions a b Ω x hmin
  intro j
  have hf : (⟨regions j, a j, x j⟩ : Entropy.PatchFactor n) ∈ l :=
    List.mem_reverse.mpr (List.mem_ofFn.mpr ⟨j, rfl⟩)
  let ρ : Matrix (Entropy.RegionConfig n (regions j))
      (Entropy.RegionConfig n (regions j)) ℂ :=
    normalizedRegularizedPatchMarginal (Out := fun v ↦ Fin (n v)) regions a b Ω x (regions j)
  have hρ : ρ.PosSemidef :=
    normalizedRegularizedPatchMarginal_posSemidef (Out := fun v ↦ Fin (n v))
      regions a b Ω x (regions j)
  have hρt : ρ.trace = 1 :=
    trace_normalizedRegularizedPatchMarginal (Out := fun v ↦ Fin (n v))
      regions a (fun k ↦ (ha k).le) hb Ω hΩ hx (regions j)
  have hρeq : ρ = Entropy.regionState (regions j)
      (Entropy.patchState b l (dependentGlobalConfigIsometry Ω)) :=
    normalizedRegularizedPatchMarginal_eq_regionState_patchState regions a b Ω x (regions j)
  have hcomm : Commute (x j) ρ := by
    simpa only [hρeq] using (Entropy.patch_stationarity hb hexp hden hnest hminList _ hf).1
  have hvar : ∀ y : Matrix (Entropy.RegionConfig n (regions j))
      (Entropy.RegionConfig n (regions j)) ℂ,
      y.PosSemidef → y.trace = 1 → Commute (x j) y →
      (ρ * (x j + b • 1) ^ (-1 : ℝ) * y).trace.re ≤
        (ρ * (x j + b • 1) ^ (-1 : ℝ) * x j).trace.re := by
    simpa only [hρeq] using
      Entropy.re_trace_variation_le_of_isPatchMinimizer hb hexp hden hnest hminList _ hf
  exact Matrix.PosSemidef.exists_unitary_diagonal_clipped_of_forall_density
    (x := x j) (ρ := ρ) (hx j).1 hρ (hx j).2 hρt hcomm hb hvar

end TNLean.PEPS
