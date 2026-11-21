/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RegularizedPatchMarginal
import QICLean.Entropy.PatchStationarity

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
-/

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
