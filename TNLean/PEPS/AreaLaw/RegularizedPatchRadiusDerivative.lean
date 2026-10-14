/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RegularizedPatchInsertionTrace
import QICLean.Analysis.ShiftedPowerDerivative
import QICLean.Analysis.OperatorMean.MatrixPowers
import QICLean.Kraus.Word
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Radius derivative of the ordered regularized patch output

Differentiating the positive scalar shift inserts its derivative at each
original position of the ordered filter product. The input vector and real
weights are arbitrary, and the local matrices need only be positive semidefinite.
Repeated regions and the empty product are retained.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states*, September 24, 2026, `03-patches.tex`, lines 425–437; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Out : V → Type*} [∀ v, Fintype (Out v)]
variable {m : ℕ} (regions : Fin m → Finset V)

open Classical in
/-- Differentiating the regulator in the actual ordered output inserts the
scalar-shift derivative at each original occurrence of a regional factor.
The densities need only be positive semidefinite; weights and input vectors
are arbitrary. Repeated regions and the empty product are retained.
Source: polynomial-PEPS manuscript, 03-patches.tex, lines 425–437. -/
theorem hasDerivAt_regularizedPatchOutput_exp_neg
    (a : Fin m → ℝ)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1))
    (x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ)
    (hx : ∀ j, (x j).PosSemidef) (R : ℝ) :
    HasDerivAt
      (fun r : ℝ ↦ regularizedPatchOutput regions a (Real.exp (-r)) Ω x)
      (∑ j, regularizedPatchInsertion regions a (Real.exp (-R)) Ω x j
        ((a j / 2 * Real.exp (-R)) •
          (x j + Real.exp (-R) • 1) ^ (-(a j) / 2 - 1))) R := by
  have hlocal (j : Fin m) :=
    (hx j).hasDerivAt_add_exp_neg_smul_one_rpow R (-(a j) / 2)
  let liftR (S : Finset V) :
      Matrix ((v : S) → Out v.1) ((v : S) → Out v.1) ℂ →L[ℝ]
        Matrix ((v : (Finset.univ : Finset V)) → Out v.1)
          ((v : (Finset.univ : Finset V)) → Out v.1) ℂ :=
    let e := dependentRegionConfigEquiv (Out := Out) S
    ((Matrix.reindexLinearEquiv ℝ ℂ e.symm e.symm).toLinearMap.comp
      ((Matrix.kroneckerBilinear (R := ℝ) (α := ℂ)).flip 1)).toContinuousLinearMap
  have hfilter (j : Fin m) :=
    (liftR (regions j)).hasFDerivAt.comp_hasDerivAt R (hlocal j)
  let P := (ContinuousMultilinearMap.mkPiAlgebraFin ℝ m
    (Matrix ((v : (Finset.univ : Finset V)) → Out v.1)
      ((v : (Finset.univ : Finset V)) → Out v.1) ℂ)).domDomCongr Fin.revPerm
  have hprod := (P.hasFDerivAt _).comp_hasDerivAt R (hasDerivAt_pi.mpr hfilter)
  let evalΩ :
      Matrix ((v : (Finset.univ : Finset V)) → Out v.1)
        ((v : (Finset.univ : Finset V)) → Out v.1) ℂ →L[ℝ]
      EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1) :=
    LinearMap.toContinuousLinearMap
      (((LinearMap.applyₗ Ω).comp Matrix.toEuclideanLin.toLinearMap).restrictScalars ℝ)
  have houtput := evalΩ.hasFDerivAt.comp_hasDerivAt R hprod
  have hP (F : Fin m → Matrix ((v : (Finset.univ : Finset V)) → Out v.1)
      ((v : (Finset.univ : Finset V)) → Out v.1) ℂ) :
      P F = ((List.ofFn F).reverse).prod := by
    simp [P, List.ofFn_reverse, Function.comp_def]
  have heval (K : Matrix ((v : (Finset.univ : Finset V)) → Out v.1)
      ((v : (Finset.univ : Finset V)) → Out v.1) ℂ) :
      evalΩ K = WithLp.toLp 2 (K *ᵥ Ω) := rfl
  have hlift (S : Finset V)
      (K : Matrix ((v : S) → Out v.1) ((v : S) → Out v.1) ℂ) :
      liftR S K = dependentRegionOperatorLift S K := rfl
  simp only [ContinuousMultilinearMap.linearDeriv_apply, map_sum] at houtput
  convert! houtput using 1
  · simp only [Function.comp_def, hP, heval, hlift, regularizedPatchOutput,
      regularizedPatchOperator, regularizedPatchFilter]
  · simp only [Function.comp_def, hP, heval, hlift, regularizedPatchInsertion_apply,
      neg_div', neg_neg]
    rfl

end TNLean.PEPS
