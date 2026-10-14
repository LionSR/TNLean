/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RegularizedPatchMinimum
import TNLean.PEPS.ParentHamiltonian.DependentRegionCoordinates
import QICLean.Entropy.PatchStationarity

/-!
# Ordered patch outputs in canonical coordinates

The indexed regional filters give the same ordered output as the corresponding
list of patch factors after the canonical identification of full-region and
global configurations. The list places the outermost factor first and retains
every occurrence of a region. The identity holds for arbitrary regional matrices,
real exponents and real shifts, with the same convention for real matrix powers.
It includes empty lists, empty regions and zero local dimensions. The two objective
norms therefore agree.

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
    (x : ∀ j, Matrix (Entropy.RegionConfig n (regions j))
      (Entropy.RegionConfig n (regions j)) ℂ) : List (Entropy.PatchFactor n) :=
  (List.ofFn fun j ↦ ⟨regions j, a j, x j⟩).reverse

/-- The canonical configuration identification takes the ordered native output
to the ordered patch-list output.
Source: polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 68–99. -/
theorem dependentGlobalConfigIsometry_regularizedPatchOutput
    (regions : Fin m → Finset V) (a : Fin m → ℝ) (b : ℝ)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Fin (n v.1)))
    (x : ∀ j, Matrix (Entropy.RegionConfig n (regions j))
      (Entropy.RegionConfig n (regions j)) ℂ) :
    dependentGlobalConfigIsometry
        (regularizedPatchOutput (Out := fun v ↦ Fin (n v)) regions a b Ω x) =
      Entropy.patchOutput b (regularizedPatchFactorList regions a x)
        (dependentGlobalConfigIsometry Ω) := by
  classical
  have hL (j : Fin m) :
      Matrix.reindex (dependentGlobalConfigEquiv (Out := fun v ↦ Fin (n v)))
          (dependentGlobalConfigEquiv (Out := fun v ↦ Fin (n v)))
          (regularizedPatchFilter (Out := fun v ↦ Fin (n v)) regions a b x j) =
        Entropy.localLift (regions j)
          (Entropy.PatchFactor.filter b ⟨regions j, a j, x j⟩).2 := by
    unfold regularizedPatchFilter Entropy.PatchFactor.filter
    convert! reindex_dependentRegionOperatorLift (fun v ↦ Equiv.refl (Fin (n v)))
      (regions j) ((x j + b • 1) ^ (-(a j) / 2)) using 1
    have hp (d₁ d₂ : DecidableEq (Entropy.RegionConfig n (regions j))) :
        (letI := d₁; (x j + b • 1) ^ (-(a j) / 2)) =
          (letI := d₂; (x j + b • 1) ^ (-(a j) / 2)) := by
      exact congrArg
        (fun d : DecidableEq (Entropy.RegionConfig n (regions j)) ↦
          letI := d; (x j + b • 1) ^ (-(a j) / 2)) (Subsingleton.elim d₁ d₂)
    apply congrArg (fun K : Matrix (Entropy.RegionConfig n (regions j))
        (Entropy.RegionConfig n (regions j)) ℂ ↦
      Matrix.reindex (dependentGlobalConfigEquiv (Out := fun v ↦ Fin (n v)))
        (dependentGlobalConfigEquiv (Out := fun v ↦ Fin (n v)))
        (dependentRegionOperatorLift (Out := fun v ↦ Fin (n v)) (regions j) K))
    exact hp _ _
  have hprod :
      Matrix.reindexAlgEquiv ℂ ℂ (dependentGlobalConfigEquiv (Out := fun v ↦ Fin (n v)))
          (regularizedPatchOperator (Out := fun v ↦ Fin (n v)) regions a b x) =
        Entropy.liftProd ((regularizedPatchFactorList regions a x).map
          (Entropy.PatchFactor.filter b)) := by
    let : DecidableEq ((v : (Finset.univ : Finset V)) → Fin (n v.1)) :=
      @Fintype.decidablePiFintype (Finset.univ : Finset V)
        (fun v ↦ Fin (n v.1))
        (fun _ u w ↦ Classical.propDecidable (u = w)) inferInstance
    simpa only [regularizedPatchOperator, Entropy.liftProd, regularizedPatchFactorList,
      List.map_reverse, List.map_ofFn, Function.comp_def, Matrix.coe_reindexAlgEquiv, hL,
      Entropy.PatchFactor.filter] using
      map_list_prod (Matrix.reindexAlgEquiv ℂ ℂ
        (dependentGlobalConfigEquiv (Out := fun v ↦ Fin (n v))))
        ((List.ofFn fun j ↦ regularizedPatchFilter (Out := fun v ↦ Fin (n v))
          regions a b x j).reverse)
  rw [regularizedPatchOutput, Entropy.patchOutput, ← hprod]
  ext σ
  change (regularizedPatchOperator (Out := fun v ↦ Fin (n v)) regions a b x *ᵥ Ω)
      ((dependentGlobalConfigEquiv (Out := fun v ↦ Fin (n v))).symm σ) =
    ((regularizedPatchOperator (Out := fun v ↦ Fin (n v)) regions a b x).submatrix
        (dependentGlobalConfigEquiv (Out := fun v ↦ Fin (n v))).symm
        (dependentGlobalConfigEquiv (Out := fun v ↦ Fin (n v))).symm *ᵥ
      (fun τ ↦ Ω ((dependentGlobalConfigEquiv (Out := fun v ↦ Fin (n v))).symm τ))) σ
  simpa only [Function.comp_def, Equiv.symm_symm, Equiv.symm_apply_apply] using
    (congrFun (Matrix.submatrix_mulVec_equiv
      (regularizedPatchOperator (Out := fun v ↦ Fin (n v)) regions a b x)
      (fun τ ↦ Ω ((dependentGlobalConfigEquiv (Out := fun v ↦ Fin (n v))).symm τ))
      (dependentGlobalConfigEquiv (Out := fun v ↦ Fin (n v))).symm
      (dependentGlobalConfigEquiv (Out := fun v ↦ Fin (n v))).symm) σ).symm

/-- The two ordered patch objectives have the same value.
Source: polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 68–99,
`eq:patch-variational-problem`. -/
theorem regularizedPatchObjective_eq_norm_patchOutput
    (regions : Fin m → Finset V) (a : Fin m → ℝ) (b : ℝ)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Fin (n v.1)))
    (x : ∀ j, Matrix (Entropy.RegionConfig n (regions j))
      (Entropy.RegionConfig n (regions j)) ℂ) :
    regularizedPatchObjective (Out := fun v ↦ Fin (n v)) regions a b Ω x =
      ‖Entropy.patchOutput b (regularizedPatchFactorList regions a x)
        (dependentGlobalConfigIsometry Ω)‖ := by
  simpa only [regularizedPatchObjective, LinearIsometryEquiv.norm_map] using
    congrArg norm (dependentGlobalConfigIsometry_regularizedPatchOutput regions a b Ω x)

end TNLean.PEPS
