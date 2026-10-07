/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RegularizedPatchMinimum
import QICLean.Analysis.CfcConjugation

/-!
# A unitary change of one regularized density

An index selects one occurrence of a region, even when regions repeat. Unitary
conjugation preserves the actual density domain, and its shifted real power
conjugates exactly. The insertion map replaces that one factor in the actual
reverse ordered product, leaving all other factors fixed.

Source: OpenAI `03-patches.tex`, lines 134–146, commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

/-!
## Original proof provenance

Source: September 24, 2026,
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/03-patches.tex
sec:patches, prop:patch, and eq:patch-variational-problem.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: regularizedpatchstationarity8767-tnlean.peps.regularizedpatchcoordinateupdate
Downstream declaration: TNLean.PEPS.regularizedPatchCoordinateUpdate

Provenance-ID: regularizedpatchstationarity8767-tnlean.peps.regularizedpatchcoordinateupdate_mem
Downstream declaration: TNLean.PEPS.regularizedPatchCoordinateUpdate_mem

Provenance-ID: regularizedpatchstationarity8767-tnlean.peps.regularizedpatchcoordinateupdate_rpow
Downstream declaration: TNLean.PEPS.regularizedPatchCoordinateUpdate_rpow

Provenance-ID: regularizedpatchstationarity8767-tnlean.peps.regularizedpatchinsertion
Downstream declaration: TNLean.PEPS.regularizedPatchInsertion

Provenance-ID: regularizedpatchstationarity8767-tnlean.peps.regularizedpatchinsertion_apply
Downstream declaration: TNLean.PEPS.regularizedPatchInsertion_apply

Provenance-ID: regularizedpatchstationarity8767-tnlean.peps.regularizedpatchoutput_coordinateupdate
Downstream declaration: TNLean.PEPS.regularizedPatchOutput_coordinateUpdate

Provenance-ID: regularizedpatchstationarity8767-tnlean.peps.regularizedpatchinsertion_self
Downstream declaration: TNLean.PEPS.regularizedPatchInsertion_self
-/

open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Out : V → Type*} [∀ v, Fintype (Out v)]
variable {m : ℕ} (regions : Fin m → Finset V)

open Classical in
/-- Conjugate exactly one indexed density, including when regions repeat. -/
noncomputable def regularizedPatchCoordinateUpdate
    (x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ)
    (j : Fin m) (U : Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ) :=
  Function.update x j (U * x j * star U)

private theorem density_conjugate {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosSemidef ∧ A.trace = 1)
    (U : unitary (Matrix n n ℂ)) :
    ((U : Matrix n n ℂ) * A * star (U : Matrix n n ℂ)).PosSemidef ∧
      ((U : Matrix n n ℂ) * A * star (U : Matrix n n ℂ)).trace = 1 := by
  constructor
  · exact hA.1.mul_mul_conjTranspose_same (U : Matrix n n ℂ)
  · rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul, hA.2]

omit [Fintype V] in
open Classical in
/-- A unitary change of one density remains in the same feasible set. -/
theorem regularizedPatchCoordinateUpdate_mem
    {x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ}
    (hx : x ∈ regularizedPatchDomain regions) (j : Fin m)
    (U : unitary (Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ)) :
    regularizedPatchCoordinateUpdate regions x j U ∈ regularizedPatchDomain regions := by
  classical
  intro k
  by_cases h : k = j
  · subst k
    simp only [regularizedPatchCoordinateUpdate, Function.update_self]
    exact density_conjugate (hx j) U
  · simpa only [regularizedPatchCoordinateUpdate, Function.update_of_ne h] using hx k

omit [Fintype V] in
open Classical in
/-- The shifted real power conjugates exactly, with no nonsingularity requirement
on the density. -/
theorem regularizedPatchCoordinateUpdate_rpow (a : Fin m → ℝ) {b : ℝ} (hb : 0 < b)
    {x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ}
    (hx : x ∈ regularizedPatchDomain regions) (j : Fin m)
    (U : unitary (Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ)) :
    (regularizedPatchCoordinateUpdate regions x j U j + b • 1) ^ (-(a j) / 2) =
      (U : Matrix _ _ ℂ) * (x j + b • 1) ^ (-(a j) / 2) * star (U : Matrix _ _ ℂ) := by
  classical
  have hs : (U : Matrix _ _ ℂ) * (x j + b • 1) * star (U : Matrix _ _ ℂ) =
      (U : Matrix _ _ ℂ) * x j * star (U : Matrix _ _ ℂ) + b • 1 := by
    simp [mul_add, add_mul]
  simp only [regularizedPatchCoordinateUpdate, Function.update_self]
  rw [← hs]
  exact Matrix.rpow_conj_unitary ((hx j).1.add_smul_one_posDef hb).posSemidef _ U

private noncomputable def reverseProductInsertion {n : Type*} [Fintype n] [DecidableEq n]
    (f : Fin m → Matrix n n ℂ) (j : Fin m) : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ := by
  classical
  have hj : (List.finRange m).reverse.idxOf j < m := by
    simpa using List.idxOf_lt_length_of_mem (show j ∈ (List.finRange m).reverse by simp)
  exact
    { toFun := fun K ↦ ((List.finRange m).reverse.map (Function.update f j K)).prod
      map_add' := fun K L ↦ by
        simp [(List.nodup_reverse.mpr (List.nodup_finRange m)).map_update,
          List.prod_set, hj, add_mul, mul_add]
      map_smul' := fun c K ↦ by
        simp [(List.nodup_reverse.mpr (List.nodup_finRange m)).map_update, List.prod_set, hj] }

private noncomputable def dependentRegionLiftLinear (R : Finset V) :
    Matrix ((v : R) → Out v.1) ((v : R) → Out v.1) ℂ →ₗ[ℂ]
      Matrix ((v : (Finset.univ : Finset V)) → Out v.1)
        ((v : (Finset.univ : Finset V)) → Out v.1) ℂ where
  toFun := dependentRegionOperatorLift R
  map_add' K L := by
    classical
    ext α β
    simp [dependentRegionOperatorLift, Matrix.reindex_apply, add_mul]
  map_smul' c K := by
    classical
    ext α β
    simp [dependentRegionOperatorLift, Matrix.reindex_apply, mul_assoc]

open Classical in
/-- Insert a local matrix in the selected factor of the actual reverse ordered
product and apply it to the original vector. -/
noncomputable def regularizedPatchInsertion (a : Fin m → ℝ) (b : ℝ)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1))
    (x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ)
    (j : Fin m) : Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ →ₗ[ℂ]
      EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1) :=
  ((LinearMap.applyₗ Ω).comp Matrix.toEuclideanLin.toLinearMap).comp
    ((reverseProductInsertion (regularizedPatchFilter regions a b x) j).comp
      (dependentRegionLiftLinear (regions j)))

open Classical in
/-- The insertion formula explicitly uses the original reverse ordered product. -/
theorem regularizedPatchInsertion_apply (a : Fin m → ℝ) (b : ℝ)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1))
    (x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ)
    (j : Fin m) (K : Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ) :
    regularizedPatchInsertion regions a b Ω x j K = WithLp.toLp 2
      (((List.ofFn (Function.update (regularizedPatchFilter regions a b x) j
        (dependentRegionOperatorLift (regions j) K))).reverse).prod *ᵥ Ω) := by
  classical
  simp [regularizedPatchInsertion, reverseProductInsertion, dependentRegionLiftLinear,
    Matrix.toEuclideanLin, Matrix.toLpLin_apply, List.ofFn_eq_map, List.map_reverse]


open Classical in
/-- Changing a density changes only the corresponding factor in the actual output. -/
theorem regularizedPatchOutput_coordinateUpdate (a : Fin m → ℝ) {b : ℝ} (hb : 0 < b)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1))
    {x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ}
    (hx : x ∈ regularizedPatchDomain regions) (j : Fin m)
    (U : unitary (Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ)) :
    regularizedPatchOutput regions a b Ω (regularizedPatchCoordinateUpdate regions x j U) =
      regularizedPatchInsertion regions a b Ω x j
        ((U : Matrix _ _ ℂ) * (x j + b • 1) ^ (-(a j) / 2) * star (U : Matrix _ _ ℂ)) := by
  classical
  rw [regularizedPatchInsertion_apply]
  unfold regularizedPatchOutput regularizedPatchOperator
  congr 5
  funext k
  by_cases h : k = j
  · subst k
    simp only [Function.update_self, regularizedPatchFilter,
      regularizedPatchCoordinateUpdate_rpow regions a hb hx j U]
  · simp only [regularizedPatchFilter, regularizedPatchCoordinateUpdate,
      Function.update_of_ne h]

open Classical in
/-- Inserting the unchanged local power recovers the actual filtered output. -/
theorem regularizedPatchInsertion_self (a : Fin m → ℝ) (b : ℝ)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1))
    (x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ)
    (j : Fin m) :
    regularizedPatchInsertion regions a b Ω x j ((x j + b • 1) ^ (-(a j) / 2)) =
      regularizedPatchOutput regions a b Ω x := by
  classical
  rw [regularizedPatchInsertion_apply]
  change WithLp.toLp 2 (((List.ofFn (Function.update
    (regularizedPatchFilter regions a b x) j
      (regularizedPatchFilter regions a b x j))).reverse).prod
      *ᵥ Ω) = _
  rw [Function.update_eq_self]
  rfl

end TNLean.PEPS
