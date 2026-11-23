/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RegionalStates.RegionalFilters.RegularizedPatchMarginal
import QICLean.ManyBody.Entropy.Filter.PatchStationarity
import QICLean.Spectral.Eigenvalue.ShiftedDensityClipping
import QICLean.Spectral.Eigenvalue.ShiftedFilterClipping

/-!
# Ordered patch outputs in canonical coordinates

The indexed regional filters give the same ordered output as the corresponding
list of patch factors after the canonical identification of full-region and
global configurations. The list places the outermost factor first and retains
every occurrence of a region. The identity holds for arbitrary regional matrices,
real exponents and real shifts, with the same convention for real matrix powers.
It includes empty lists, empty regions and zero local dimensions. The two objective
norms therefore agree, and a minimum over indexed densities gives a minimum
over all lists with the same positional regions and exponents. Normalizing the
outputs preserves this identification, including when the output vanishes.
Every regional marginal is therefore the regional state of that same normalized
patch-list output.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
Proposition 4.1, `03-patches.tex`, `eq:patch-variational-problem`, lines 68–99,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

## Common eigenbases at regularized patch minima

At every feasible minimum of the ordered patch objective, each regional density
and the corresponding marginal of the normalized output have a common unitary
eigenbasis. Their eigenvalues satisfy the clipped formula with a positive
multiplier at most one. Regions are nested in increasing index order; repeated
regions retain separate density variables.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states*, Proposition 4.1, `03-patches.tex`, lines 68–99 and 115–200,
`eq:patch-stationarity-commutation` and `eq:patch-clipped-eigenvalues`;
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

## Clipped inverse-power filters at a regularized patch minimum

At a feasible minimum of the ordered patch objective, each regional inverse-power
filter commutes with the marginal of the same normalized output. Their common
unitary eigenbasis gives positive filter eigenvalues and a logarithmic estimate
with coefficient one half of the regional exponent. The estimate compares only
positive marginal coordinates. Repeated and empty regions are admitted.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states*, Proposition 4.1, `03-patches.tex`, `eq:patch-variational-problem`,
`eq:patch-clipped-eigenvalues`, and `eq:patch-log-ratio`; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean text is reused.
-/

section

open Complex Matrix
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {n : V → ℕ} {m : ℕ}

/-- The factors in the order in which their matrices occur in the patch
operator, with the outermost factor first.
Source: polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 68–99,
`eq:patch-variational-problem`. -/
def regularizedPatchFactorList (regions : Fin m → Finset V) (a : Fin m → ℝ)
    (x : ∀ j, Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j))
      (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j)) ℂ) : List (Entropy.PatchFactor n) :=
  (List.ofFn fun j ↦ ⟨regions j, a j, x j⟩).reverse

/-- The ordered regularized output is the ordered patch-list output.
Source: polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 68–99. -/
theorem regularizedPatchOutput_eq_patchOutput
    (regions : Fin m → Finset V) (a : Fin m → ℝ) (b : ℝ)
    (Ω : EuclideanSpace ℂ ((v : V) → Fin (n v)))
    (x : ∀ j, Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j))
      (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j)) ℂ) :
    regularizedPatchOutput (Out := fun v ↦ Fin (n v)) regions a b Ω x =
      Entropy.patchOutput b (regularizedPatchFactorList regions a x) Ω := by
  classical
  have hL (j : Fin m) :
      regularizedPatchFilter (Out := fun v ↦ Fin (n v)) regions a b x j =
        ManyBody.place (regions j)
          (Entropy.PatchFactor.filter b ⟨regions j, a j, x j⟩).2 := by
    unfold regularizedPatchFilter Entropy.PatchFactor.filter
    have hp (d₁ d₂ : DecidableEq (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j))) :
        (letI := d₁; (x j + b • 1) ^ (-(a j) / 2)) =
          (letI := d₂; (x j + b • 1) ^ (-(a j) / 2)) := by
      exact congrArg
        (fun d : DecidableEq (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j)) ↦
          letI := d; (x j + b • 1) ^ (-(a j) / 2)) (Subsingleton.elim d₁ d₂)
    exact congrArg (ManyBody.place (X := fun v ↦ Fin (n v)) (regions j)) (hp _ _)
  have hprod :
      regularizedPatchOperator (Out := fun v ↦ Fin (n v)) regions a b x =
        Entropy.liftProd ((regularizedPatchFactorList regions a x).map
          (Entropy.PatchFactor.filter b)) := by
    simp only [regularizedPatchOperator, Entropy.liftProd, regularizedPatchFactorList,
      List.map_reverse, List.map_ofFn, Function.comp_def, hL, Entropy.PatchFactor.filter]
  rw [regularizedPatchOutput, Entropy.patchOutput, hprod]
  rfl

/-- The two ordered patch objectives have the same value.
Source: polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 68–99,
`eq:patch-variational-problem`. -/
theorem regularizedPatchObjective_eq_norm_patchOutput
    (regions : Fin m → Finset V) (a : Fin m → ℝ) (b : ℝ)
    (Ω : EuclideanSpace ℂ ((v : V) → Fin (n v)))
    (x : ∀ j, Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j))
      (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j)) ℂ) :
    regularizedPatchObjective (Out := fun v ↦ Fin (n v)) regions a b Ω x =
      ‖Entropy.patchOutput b (regularizedPatchFactorList regions a x)
        (Ω)‖ := by
  simpa only [regularizedPatchObjective, LinearIsometryEquiv.norm_map] using
    congrArg norm (regularizedPatchOutput_eq_patchOutput regions a b Ω x)

/-- A minimum of the ordered patch objective over independent regional density
matrices also minimizes the norm among all patch lists with the same positional
regions and exponents. Repeated regions retain independent density matrices.
The comparison applies to arbitrary distinguished matrices and arbitrary inputs.
Source: polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 68–99,
`eq:patch-variational-problem`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem isPatchMinimizer_regularizedPatchFactorList
    (regions : Fin m → Finset V) (a : Fin m → ℝ) (b : ℝ)
    (Ω : EuclideanSpace ℂ ((v : V) → Fin (n v)))
    (x : ∀ j, Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j))
      (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j)) ℂ)
    (hmin : IsMinOn
      (regularizedPatchObjective (Out := fun v ↦ Fin (n v)) regions a b Ω)
      (regularizedPatchDomain (Out := fun v ↦ Fin (n v)) regions) x) :
    Entropy.IsPatchMinimizer b (regularizedPatchFactorList regions a x)
      (Ω) := by
  intro l' hregions hexponents hfeasible
  obtain ⟨⟨r, g⟩, hg⟩ := List.equivSigmaTuple.symm.surjective l'.reverse
  change List.ofFn g = l'.reverse at hg
  have hl : (List.ofFn g).reverse = l' := by
    simpa only [List.reverse_reverse] using congrArg List.reverse hg
  subst l'
  have hr : r = m := by
    simpa only [regularizedPatchFactorList, List.length_map, List.length_reverse,
      List.length_ofFn] using congrArg List.length hregions
  subst r
  have hR : (fun j ↦ (g j).region) = regions := List.ofFn_injective <| by
    simpa only [regularizedPatchFactorList, List.map_reverse, List.reverse_reverse,
      List.map_ofFn, Function.comp_def] using congrArg List.reverse hregions
  have ha : (fun j ↦ (g j).exponent) = a := List.ofFn_injective <| by
    simpa only [regularizedPatchFactorList, List.map_reverse, List.reverse_reverse,
      List.map_ofFn, Function.comp_def] using congrArg List.reverse hexponents
  subst regions
  subst a
  have hf : regularizedPatchFactorList (fun j ↦ (g j).region)
      (fun j ↦ (g j).exponent) (fun j ↦ (g j).density) = (List.ofFn g).reverse := rfl
  rw [← hf, ← regularizedPatchObjective_eq_norm_patchOutput,
    ← regularizedPatchObjective_eq_norm_patchOutput]
  apply hmin
  intro j
  exact hfeasible (g j) (List.mem_reverse.mpr (List.mem_ofFn.mpr ⟨j, rfl⟩))

/-- The normalized outputs agree under the same configuration identification,
including when the ordered output is zero.
Source: polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 68–99 and
130–205. -/
theorem normalizedRegularizedPatchOutput_eq_patchState
    (regions : Fin m → Finset V) (a : Fin m → ℝ) (b : ℝ)
    (Ω : EuclideanSpace ℂ ((v : V) → Fin (n v)))
    (x : ∀ j, Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j))
      (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j)) ℂ) :
    normalizedRegularizedPatchOutput (Out := fun v ↦ Fin (n v)) regions a b Ω x =
      Entropy.patchState b (regularizedPatchFactorList regions a x) Ω := by
  simp only [normalizedRegularizedPatchOutput, Entropy.patchState,
    RCLike.real_smul_eq_coe_smul (K := ℂ),
    regularizedPatchObjective_eq_norm_patchOutput,
    regularizedPatchOutput_eq_patchOutput]
  rfl

/-- Every canonical marginal is the regional state of the same normalized
patch-list output, including on an empty region.
Source: polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 68–99 and
130–205. -/
theorem normalizedRegularizedPatchMarginal_eq_regionState_patchState
    (regions : Fin m → Finset V) (a : Fin m → ℝ) (b : ℝ)
    (Ω : EuclideanSpace ℂ ((v : V) → Fin (n v)))
    (x : ∀ j, Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j))
      (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j)) ℂ) (R : Finset V) :
    normalizedRegularizedPatchMarginal (Out := fun v ↦ Fin (n v))
        regions a b Ω x R =
      ManyBody.regionState (Entropy.patchState b (regularizedPatchFactorList regions a x)
          (Ω))
        R := by
  exact (reindex_normalizedRegularizedPatchMarginal regions
    (fun v ↦ Equiv.refl (Fin (n v))) a b Ω x R).trans
    (congrArg (fun φ : EuclideanSpace ℂ ((v : V) → Fin (n v)) ↦ ManyBody.regionState φ R)
      (normalizedRegularizedPatchOutput_eq_patchState regions a b Ω x))

end TNLean.PEPS

namespace TNLean.PEPS

variable {V : Type*} [DecidableEq V]
variable {n : V → ℕ} {m : ℕ}

/-- Mapping the indexed patch factors to their inverse-power filters gives
exactly the chain list in decreasing index order. Every occurrence of a region
is retained. The identity holds for arbitrary regional matrices, exponents and
shifts, including the empty list.

Source: polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 68–99,
`eq:patch-variational-problem`; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem map_filter_regularizedPatchFactorList_eq_chainList
    (D : ℕ → Finset V) (a : Fin m → ℝ) (b : ℝ)
    (x : (j : Fin m) → Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (D j))
      (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (D j)) ℂ) :
    (regularizedPatchFactorList (fun j : Fin m ↦ D j) a x).map
        (Entropy.PatchFactor.filter b) =
      Entropy.chainList D
        (fun j : Fin m ↦
          (x j + b • (1 : Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (D j))
            (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (D j)) ℂ)) ^ (-(a j) / 2))
        (fun _ ↦ True) := by
  simp [regularizedPatchFactorList, Entropy.chainList, Entropy.PatchFactor.filter,
    List.ofFn_eq_map, List.map_reverse, List.map_map, Function.comp_def]

end TNLean.PEPS

end

section

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
    (Ω : EuclideanSpace ℂ ((v : V) → Fin (n v)))
    (hΩ : ‖Ω‖ = 1)
    (x : ∀ j, Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j))
      (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j)) ℂ)
    (hx : x ∈ regularizedPatchDomain (Out := fun v ↦ Fin (n v)) regions)
    (hmin : IsMinOn
      (regularizedPatchObjective (Out := fun v ↦ Fin (n v)) regions a b Ω)
      (regularizedPatchDomain (Out := fun v ↦ Fin (n v)) regions) x) :
    ∀ j : Fin m,
      ∃ (U : Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j))
          (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j)) ℂ)
        (s p : (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j)) → ℝ) (lam : ℝ),
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
  let ρ : Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j))
      (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j)) ℂ :=
    normalizedRegularizedPatchMarginal (Out := fun v ↦ Fin (n v)) regions a b Ω x (regions j)
  have hρ : ρ.PosSemidef :=
    normalizedRegularizedPatchMarginal_posSemidef (Out := fun v ↦ Fin (n v))
      regions a b Ω x (regions j)
  have hρt : ρ.trace = 1 :=
    trace_normalizedRegularizedPatchMarginal (Out := fun v ↦ Fin (n v))
      regions a (fun k ↦ (ha k).le) hb Ω hΩ hx (regions j)
  have hρeq : ρ = ManyBody.regionState (Entropy.patchState b l (Ω))
      (regions j) :=
    normalizedRegularizedPatchMarginal_eq_regionState_patchState regions a b Ω x (regions j)
  have hcomm : Commute (x j) ρ := by
    simpa only [hρeq] using (Entropy.patch_stationarity hb hexp hden hnest hminList _ hf).1
  have hvar : ∀ y : Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j))
      (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j)) ℂ,
      y.PosSemidef → y.trace = 1 → Commute (x j) y →
      (ρ * (x j + b • 1) ^ (-1 : ℝ) * y).trace.re ≤
        (ρ * (x j + b • 1) ^ (-1 : ℝ) * x j).trace.re := by
    simpa only [hρeq] using
      Entropy.re_trace_variation_le_of_isPatchMinimizer hb hexp hden hnest hminList _ hf
  exact Matrix.PosSemidef.exists_unitary_diagonal_clipped_of_forall_density
    (x := x j) (ρ := ρ) (hx j).1 hρ (hx j).2 hρt hcomm hb hvar

end TNLean.PEPS

end

section

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
    (Ω : EuclideanSpace ℂ ((v : V) → Fin (n v)))
    (hΩ : ‖Ω‖ = 1)
    (x : ∀ j, Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j))
      (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j)) ℂ)
    (hx : x ∈ regularizedPatchDomain (Out := fun v ↦ Fin (n v)) regions)
    (hmin : IsMinOn
      (regularizedPatchObjective (Out := fun v ↦ Fin (n v)) regions a b Ω)
      (regularizedPatchDomain (Out := fun v ↦ Fin (n v)) regions) x) :
    let K : ∀ j : Fin m, Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j))
        (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j)) ℂ :=
      fun j ↦ (x j + b • 1) ^ (-(a j) / 2)
    let φ : EuclideanSpace ℂ (∀ v, Fin (n v)) :=
      (normalizedRegularizedPatchOutput (Out := fun v ↦ Fin (n v))
          regions a b Ω x)
    ∀ j : Fin m,
      K j * ManyBody.regionState φ (regions j) =
          ManyBody.regionState φ (regions j) * K j ∧
        ∃ (W : Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j))
            (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j)) ℂ)
          (l p : (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (regions j)) → ℝ),
          Wᴴ * W = 1 ∧ (∀ i, 0 < l i) ∧
          K j = W * diagonal (fun i ↦ (l i : ℂ)) * Wᴴ ∧
          ManyBody.regionState φ (regions j) =
            W * diagonal (fun i ↦ (p i : ℂ)) * Wᴴ ∧
          ∀ i k, 0 < p i → 0 < p k →
            |Real.log (l i) - Real.log (l k)| ≤
              a j / 2 * |Real.log (p i) - Real.log (p k)| := by
  intro K φ j
  obtain ⟨U, s, p, lam, hU, _, hxdiag, hρdiag, hlam, _, hclip⟩ :=
    exists_unitary_diagonal_clipped_of_isMinOn_regularizedPatchObjective
      regions hnested a ha hb Ω hΩ x hx hmin j
  simpa only [K, φ, normalizedRegularizedPatchOutput_eq_patchState,
    normalizedRegularizedPatchMarginal_eq_regionState_patchState] using
    Matrix.exists_clipped_rpow_add_smul_one_of_diagonal_max
      hU hxdiag hρdiag hb hlam (ha j).le hclip

end TNLean.PEPS

end
