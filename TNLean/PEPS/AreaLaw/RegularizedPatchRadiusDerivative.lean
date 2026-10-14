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

open Classical in
/-- For a fixed feasible tuple, outer commutations at the specified radius give
the canonical marginal formula for the logarithmic norm derivative. This is an
auxiliary trace identity: a later minimizer application must derive the displayed
commutations. No differentiable choice of minimizing tuples is assumed.
Source: polynomial-PEPS manuscript, 03-patches.tex, lines 453–466. -/
theorem hasDerivAt_log_regularizedPatchObjective_exp_neg_of_outer_commute
    (hnested : Monotone regions) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1))
    (hΩ : ‖Ω‖ = 1)
    (x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ)
    (hx : x ∈ regularizedPatchDomain (Out := Out) regions) (R : ℝ)
    (houter : ∀ j k : Fin m, j < k →
      Commute ((x k + Real.exp (-R) • 1) ^ (-(a k) / 2))
        (normalizedRegularizedPatchMarginal regions a (Real.exp (-R)) Ω x (regions k))) :
    HasDerivAt
      (fun r : ℝ ↦ Real.log (regularizedPatchObjective regions a (Real.exp (-r)) Ω x))
      (∑ j, (a j / 2) *
        (Matrix.trace
          (normalizedRegularizedPatchMarginal regions a (Real.exp (-R)) Ω x (regions j) *
            (Real.exp (-R) • (x j + Real.exp (-R) • 1) ^ (-1 : ℝ)))).re) R := by
  let := InnerProductSpace.rclikeToReal ℂ
    (EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1))
  have hb : 0 < Real.exp (-R) := Real.exp_pos _
  have hxpsd (j : Fin m) : (x j).PosSemidef := (hx j).1
  have hp := regularizedPatchObjective_pos regions a ha hb Ω hΩ hx
  have hvec := hasDerivAt_regularizedPatchOutput_exp_neg regions a Ω x hxpsd R
  have hlog := (hvec.norm_sq.log (pow_ne_zero 2 hp.ne')).div_const 2
  simp only [Real.log_pow, Nat.cast_ofNat,
    mul_div_cancel_left₀ _ (two_ne_zero : (2 : ℝ) ≠ 0)] at hlog
  convert! hlog using 1
  simp only [real_inner_eq_re_inner, inner_sum]
  simp_rw [inner_regularizedPatchInsertion_eq_trace_of_outer_commute
    regions hnested a hb Ω x hxpsd _ (houter _)]
  simp_rw [smul_mul_assoc, Matrix.inv_eq_left_inv
    (((hxpsd _).add_smul_one_posDef hb).rpow_neg_mul_rpow _),
    ((hxpsd _).add_smul_one_posDef hb).rpow_mul_rpow]
  simp only [sub_add_eq_add_sub, add_neg_cancel, zero_sub, Matrix.mul_smul,
    Matrix.trace_smul, ← Complex.ofReal_pow, RCLike.re_to_complex, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.smul_re,
    smul_eq_mul, mul_assoc, ← Finset.mul_sum, regularizedPatchObjective]
  field_simp [show ‖regularizedPatchOutput regions a (Real.exp (-R)) Ω x‖ ≠ 0 from hp.ne']
  simp only [mul_comm (Real.exp (-R))]

end TNLean.PEPS
