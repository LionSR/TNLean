/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RegularizedPatchListCoordinates
import QICLean.Analysis.ShiftedDensityCommutation

/-!
# Stationarity of the original indexed patch minimum

At a feasible minimum of the original ordered norm objective, each defining
density commutes with the corresponding marginal of the same normalized final
output. That marginal is bounded above by the density plus the positive scalar
shift. The regularized inverse-power filter therefore also commutes with it.

The result uses the existing stationarity theorem after the canonical
identification with an ordered list. Every region occurrence is retained,
including repeated regions. The input vector is arbitrary and may vanish.
Local coordinates are `Fin (n v)`; transport to other finite coordinate types
is a separate use of the sitewise coordinate isometries.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states*, September 24, 2026, Proposition 4.1, `03-patches.tex`, lines 68–99
and 130–205, `eq:patch-stationarity-commutation` and `eq:patch-kkt`; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {n : V → ℕ} {m : ℕ}

/-- Stationarity of the actual indexed norm minimum gives commutation and
density order for the marginal of the same normalized output.
Source: polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 130–205. -/
theorem normalizedRegularizedPatchMarginal_stationarity_of_isMinOn
    (regions : Fin m → Finset V) (hnested : Monotone regions)
    (a : Fin m → ℝ) (ha : ∀ j, 0 < a j) {b : ℝ} (hb : 0 < b)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Fin (n v.1)))
    (x : ∀ j, Matrix (Entropy.RegionConfig n (regions j))
      (Entropy.RegionConfig n (regions j)) ℂ)
    (hx : x ∈ regularizedPatchDomain (Out := fun v ↦ Fin (n v)) regions)
    (hmin : IsMinOn
      (regularizedPatchObjective (Out := fun v ↦ Fin (n v)) regions a b Ω)
      (regularizedPatchDomain (Out := fun v ↦ Fin (n v)) regions) x) :
    ∀ j : Fin m,
      Commute (x j)
          (normalizedRegularizedPatchMarginal (Out := fun v ↦ Fin (n v))
            regions a b Ω x (regions j)) ∧
        normalizedRegularizedPatchMarginal (Out := fun v ↦ Fin (n v))
          regions a b Ω x (regions j) ≤ x j + b • 1 := by
  let f : Fin m → Entropy.PatchFactor n := fun j ↦ ⟨regions j, a j, x j⟩
  let l := regularizedPatchFactorList regions a x
  have hindex {g : Entropy.PatchFactor n} (hg : g ∈ l) : ∃ j, f j = g :=
    List.mem_ofFn.mp (List.mem_reverse.mp hg)
  have hmem (j : Fin m) : f j ∈ l :=
    List.mem_reverse.mpr (List.mem_ofFn.mpr ⟨j, rfl⟩)
  have hexp : ∀ g ∈ l, 0 < g.exponent := by
    intro g hg
    obtain ⟨j, rfl⟩ := hindex hg
    exact ha j
  have hden : ∀ g ∈ l, g.density.PosSemidef ∧ g.density.trace = 1 := by
    intro g hg
    obtain ⟨j, rfl⟩ := hindex hg
    exact hx j
  have hnest : l.Pairwise (fun g g' ↦ g'.region ⊆ g.region) := by
    change ((List.ofFn f).reverse).Pairwise _
    exact List.pairwise_reverse.mpr
      (List.pairwise_ofFn.mpr fun i j hij ↦ hnested hij.le)
  have hminList := isPatchMinimizer_regularizedPatchFactorList regions a b Ω x hmin
  intro j
  simpa only [f, normalizedRegularizedPatchMarginal_eq_regionState_patchState] using
    Entropy.patch_stationarity hb hexp hden hnest hminList (f j) (hmem j)

/-- Every original inverse-power filter commutes with its marginal at the
same feasible minimum, without a nonvanishing-input assumption.
Source: polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 130–168. -/
theorem commute_filter_normalizedRegularizedPatchMarginal_of_isMinOn
    (regions : Fin m → Finset V) (hnested : Monotone regions)
    (a : Fin m → ℝ) (ha : ∀ j, 0 < a j) {b : ℝ} (hb : 0 < b)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Fin (n v.1)))
    (x : ∀ j, Matrix (Entropy.RegionConfig n (regions j))
      (Entropy.RegionConfig n (regions j)) ℂ)
    (hx : x ∈ regularizedPatchDomain (Out := fun v ↦ Fin (n v)) regions)
    (hmin : IsMinOn
      (regularizedPatchObjective (Out := fun v ↦ Fin (n v)) regions a b Ω)
      (regularizedPatchDomain (Out := fun v ↦ Fin (n v)) regions) x) :
    ∀ j : Fin m,
      Commute ((x j + b • 1) ^ (-(a j) / 2))
        (normalizedRegularizedPatchMarginal (Out := fun v ↦ Fin (n v))
          regions a b Ω x (regions j)) := by
  intro j
  exact ((hx j).1.commute_add_smul_one_rpow_iff hb
    (div_ne_zero (neg_ne_zero.mpr (ha j).ne') (by norm_num))).mpr
    (normalizedRegularizedPatchMarginal_stationarity_of_isMinOn
      regions hnested a ha hb Ω x hx hmin j).1

end TNLean.PEPS
