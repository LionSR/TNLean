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

open Classical in
/-- The logarithmic norm derivatives of all feasible tuples admit the same bound
on a bounded regulator interval. The bound depends on the sum of the weights,
not on the number of factors or Hilbert-space dimensions. No nesting or
commutation assumption is needed.
Source: polynomial-PEPS manuscript, 03-patches.tex, lines 433–451,
eq:patch-uniform-local-lipschitz. -/
theorem exists_hasDerivAt_log_regularizedPatchObjective_exp_neg_uniform
    (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1))
    (hΩ : ‖Ω‖ = 1) (T : ℝ) (hT : 0 ≤ T) :
    let κ : ℝ := ∑ j, a j
    ∀ x ∈ regularizedPatchDomain (Out := Out) regions,
      ∀ R ∈ Set.Icc 0 T, ∃ f' : ℝ,
        HasDerivAt
          (fun r : ℝ ↦ Real.log (regularizedPatchObjective regions a (Real.exp (-r)) Ω x))
          f' R ∧
        |f'| ≤ κ / 2 * (2 : ℝ) ^ (κ / 2) * Real.exp (κ * T / 2) := by
  intro κ x hx R hR
  let b := Real.exp (-R)
  have hb : 0 < b := Real.exp_pos _
  have hpow (j : Fin m) := (hx j).1.l2_opNorm_add_smul_one_rpow_le_of_nonpos
    (r := -(a j) / 2 - 1) (hx j).2 hb (by linarith [ha j])
  have hc (j : Fin m) : 0 ≤ a j / 2 * b :=
    mul_nonneg (div_nonneg (ha j) (by norm_num)) hb.le
  have hD (j : Fin m) :
      ‖(a j / 2 * b) • (x j + b • 1) ^ (-(a j) / 2 - 1)‖ ≤
        (a j / 2 * b) * b ^ (-(a j) / 2 - 1) := by
    simpa only [norm_smul, Real.norm_of_nonneg (hc j)] using
      mul_le_mul_of_nonneg_left (hpow j) (hc j)
  simp_rw [Real.rpow_sub_one hb.ne', mul_assoc, mul_div_cancel₀ _ hb.ne'] at hD
  have hlift (S : Finset V)
      (K : Matrix ((v : S) → Out v.1) ((v : S) → Out v.1) ℂ) :
      ‖dependentRegionOperatorLift S K‖ ≤ ‖K‖ :=
    Matrix.l2_opNorm_le_of_forall (norm_nonneg K)
      (fun v ↦ norm_dependentRegionOperatorLift_mulVec_le S K (WithLp.toLp 2 v))
  have hF (j : Fin m) : ‖regularizedPatchFilter regions a b x j‖ ≤ b ^ (-(a j) / 2) :=
    Matrix.l2_opNorm_le_of_forall (Real.rpow_nonneg hb.le _)
      (fun v ↦ (regularizedPatchFilter_norm_bounds regions a ha hb hx j
        (WithLp.toLp 2 v)).2)
  let D (j : Fin m) := (a j / 2 * b) • (x j + b • 1) ^ (-(a j) / 2 - 1)
  have hU (j : Fin m) :
      (norm ∘ Function.update (regularizedPatchFilter regions a b x) j
        (dependentRegionOperatorLift (regions j) (D j))) ≤
        Function.update (fun i ↦ b ^ (-(a i) / 2)) j (a j / 2 * b ^ (-(a j) / 2)) := by
    simpa only [Function.comp_update] using
      (update_le_update_iff.mpr ⟨(hlift _ _).trans (hD j), fun i _ ↦ hF i⟩ :
        Function.update (norm ∘ regularizedPatchFilter regions a b x) j
          ‖dependentRegionOperatorLift (regions j) (D j)‖ ≤
          Function.update (fun i ↦ b ^ (-(a i) / 2)) j (a j / 2 * b ^ (-(a j) / 2)))
  have hprod (j : Fin m)
      (F : Fin m → Matrix ((v : (Finset.univ : Finset V)) → Out v.1)
        ((v : (Finset.univ : Finset V)) → Out v.1) ℂ) :
      ‖((List.ofFn F).reverse).prod‖ ≤ ∏ i, ‖F i‖ := by
    simpa only [List.map_reverse, List.prod_reverse, List.map_ofFn, List.prod_ofFn,
      Function.comp_apply] using (List.norm_prod_le' (l := (List.ofFn F).reverse) (by
        simpa only [List.ne_nil_iff_length_pos, List.length_reverse, List.length_ofFn]
          using (Nat.zero_lt_of_lt j.isLt)))
  have hI (j : Fin m) : ‖regularizedPatchInsertion regions a b Ω x j (D j)‖ ≤
      ∏ i, Function.update (fun i ↦ b ^ (-(a i) / 2)) j (a j / 2 * b ^ (-(a j) / 2)) i := by
    simpa only [regularizedPatchInsertion_apply, hΩ, mul_one,
      PiLp.coe_symm_continuousLinearEquiv] using
      (Matrix.l2_opNorm_mulVec
        ((List.ofFn (Function.update (regularizedPatchFilter regions a b x) j
          (dependentRegionOperatorLift (regions j) (D j)))).reverse).prod Ω).trans
        (mul_le_mul_of_nonneg_right ((hprod j _).trans
          (Finset.prod_le_prod₀ (fun i _ ↦ norm_nonneg _) (fun i _ ↦ hU j i))) (norm_nonneg Ω))
  have huprod (r : Fin m → ℝ) (c : ℝ) (j : Fin m) :
      (∏ i, Function.update r j (c * r j) i) = c * ∏ i, r i := by
    rw [Finset.prod_update_of_mem (Finset.mem_univ j) r (c * r j),
      Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ j) r, mul_assoc]
  simp_rw [huprod, ← Real.rpow_sum_of_pos hb, ← Finset.sum_div,
    Finset.sum_neg_distrib] at hI
  have hsum : ‖∑ j, regularizedPatchInsertion regions a b Ω x j (D j)‖ ≤
      κ / 2 * b ^ (-κ / 2) := by
    simpa only [← Finset.sum_mul, ← Finset.sum_div] using
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ ↦ hI j))
  let := InnerProductSpace.rclikeToReal ℂ
    (EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1))
  have hp := regularizedPatchObjective_pos regions a ha hb Ω hΩ hx
  have hlog := ((hasDerivAt_regularizedPatchOutput_exp_neg regions a Ω x
    (fun j ↦ (hx j).1) R).norm_sq.log (pow_ne_zero 2 hp.ne')).div_const 2
  simp only [Real.log_pow, Nat.cast_ofNat,
    mul_div_cancel_left₀ _ (two_ne_zero : (2 : ℝ) ≠ 0)] at hlog
  rw [div_right_comm, mul_div_cancel_left₀ _ (two_ne_zero : (2 : ℝ) ≠ 0)] at hlog
  have hcs := (abs_real_inner_le_norm (regularizedPatchOutput regions a b Ω x)
    (∑ j, regularizedPatchInsertion regions a b Ω x j (D j))).trans
      (mul_le_mul_of_nonneg_left hsum (norm_nonneg _))
  have hratio :
      |inner ℝ (regularizedPatchOutput regions a b Ω x)
          (∑ j, regularizedPatchInsertion regions a b Ω x j (D j)) /
        ‖regularizedPatchOutput regions a b Ω x‖ ^ 2| ≤
      (κ / 2 * b ^ (-κ / 2)) / ‖regularizedPatchOutput regions a b Ω x‖ := by
    simpa only [abs_div, pow_two, abs_mul, abs_norm,
      mul_div_mul_left _ _ (show ‖regularizedPatchOutput regions a b Ω x‖ ≠ 0 from hp.ne')] using
      div_le_div_of_nonneg_right hcs (sq_nonneg ‖regularizedPatchOutput regions a b Ω x‖)
  have hκ : 0 ≤ κ / 2 := div_nonneg (Finset.sum_nonneg (fun j _ ↦ ha j)) (by norm_num)
  have hlower := div_le_div₀ (mul_nonneg hκ (Real.rpow_nonneg hb.le (-κ / 2))) le_rfl
    (Real.rpow_pos_of_pos (by linarith : 0 < 1 + b) (-κ / 2))
    (regularizedPatchObjective_bounds regions a ha hb Ω hΩ hx).1
  have hbase : (1 + b) / b = 1 + Real.exp R := by
    rw [add_div, div_self hb.ne', one_div, show b = Real.exp (-R) from rfl,
      Real.exp_neg, inv_inv, add_comm]
  have hrpow : b ^ (-κ / 2) / (1 + b) ^ (-κ / 2) = (1 + Real.exp R) ^ (κ / 2) := by
    rw [neg_div, Real.rpow_neg hb.le, Real.rpow_neg (by linarith : 0 ≤ 1 + b),
      inv_div_inv, ← Real.div_rpow (by linarith : 0 ≤ 1 + b) hb.le, hbase]
  have hbase_le : 1 + Real.exp R ≤ 2 * Real.exp T := by
    linarith [Real.one_le_exp_iff.mpr hT, Real.exp_le_exp.mpr hR.2]
  have hscalar : (1 + Real.exp R) ^ (κ / 2) ≤
      (2 : ℝ) ^ (κ / 2) * Real.exp (κ * T / 2) := by
    simpa only [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.exp_pos T).le,
      ← Real.exp_mul, show T * (κ / 2) = κ * T / 2 by ring] using
      Real.rpow_le_rpow (by positivity) hbase_le hκ
  refine ⟨_, hlog, (hratio.trans hlower).trans ?_⟩
  simpa only [mul_div_assoc, hrpow, mul_assoc] using mul_le_mul_of_nonneg_left hscalar hκ

end TNLean.PEPS
