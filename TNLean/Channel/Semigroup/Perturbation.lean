/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Algebra.MatrixOperatorSpace
import TNLean.Channel.Semigroup.Basic

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Perturbation bound for dynamical semigroups — Wolf Lemma 7.1 and Corollary 7.1

## Main results

* `duhamel_formula` — **Lemma 7.1** (Duhamel/perturbation integral formula)
* `perturbation_bound` — **Corollary 7.1** (perturbation of generators)

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, §7.1][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder BigOperators NNReal TNOperatorSpace
open Matrix Finset NormedSpace MeasureTheory TNLean

noncomputable section

variable {D : ℕ}

/-! ## Derivative of the semigroup product -/

set_option maxHeartbeats 800000 in
-- The product-derivative proof combines semigroup differentiation, a translated parameter,
-- and CLM multiplication; 4.29 elaboration needs a higher heartbeat budget here.
/-- HasDerivAt for `s ↦ exp((t-s)•L) * exp(s•L')` with derivative
`exp((t-s)•L) * (L' - L) * exp(s•L')`. -/
private theorem hasDerivAt_semigroup_product
    (L L' : MatrixCLM (Fin D)) (t s : ℝ) :
    HasDerivAt (fun u => expSemigroupCLM L (t - u) * expSemigroupCLM L' u)
      (expSemigroupCLM L (t - s) * (L' - L) * expSemigroupCLM L' s) s := by
  have hg :
      HasDerivAt (fun u => expSemigroupCLM L (t - u))
        (-(expSemigroupCLM L (t - s) * L)) s := by
    have hbase :
        HasDerivAt (fun u : ℝ => expSemigroupCLM L u)
          (expSemigroupCLM L (t - s) * L) (t - s) :=
      hasDerivAt_expSemigroupCLM L (t - s)
    simpa [neg_one_smul] using
      (HasDerivAt.comp_const_sub
        (𝕜 := ℝ)
        (f := fun u : ℝ => expSemigroupCLM L u)
        (a := t) (x := s) hbase)
  have hh :
      HasDerivAt (fun u => expSemigroupCLM L' u)
        (expSemigroupCLM L' s * L') s :=
    hasDerivAt_expSemigroupCLM L' s
  let c : ℝ → MatrixCLM (Fin D) := fun u => expSemigroupCLM L (t - u)
  let d : ℝ → MatrixCLM (Fin D) := fun u => expSemigroupCLM L' u
  have hc : HasDerivAt c (-(expSemigroupCLM L (t - s) * L)) s := hg
  have hd : HasDerivAt d (expSemigroupCLM L' s * L') s := hh
  have hprod : HasDerivAt
      (fun u => expSemigroupCLM L (t - u) * expSemigroupCLM L' u)
      (-(expSemigroupCLM L (t - s) * L) * expSemigroupCLM L' s +
        expSemigroupCLM L (t - s) * (expSemigroupCLM L' s * L')) s := by
    simpa [c, d, mul_assoc] using
      (HasDerivAt.mul (𝕜 := ℝ) (𝔸 := MatrixCLM (Fin D)) hc hd)
  -- The derivative from product rule is: -(exp(...)* L) * exp(...) + exp(...) * (exp(...) * L')
  -- We need: exp(...) * (L' - L) * exp(...)
  suffices heq :
      -(expSemigroupCLM L (t - s) * L) * expSemigroupCLM L' s +
      expSemigroupCLM L (t - s) * (expSemigroupCLM L' s * L') =
      expSemigroupCLM L (t - s) * (L' - L) * expSemigroupCLM L' s by
    rwa [heq] at hprod
  -- Commutativity: L' * exp(s•L') = exp(s•L') * L'
  have hcomm : L' * expSemigroupCLM L' s =
      expSemigroupCLM L' s * L' :=
    by
      have hcomm_smul : Commute ((s : ℂ) • L') L' := by
        ext v
        simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, map_smul]
      simpa [expSemigroupCLM] using hcomm_smul.exp_left.eq.symm
  -- Prove the algebra at the pointwise level (avoids CLM instance diamonds with neg_mul)
  apply ContinuousLinearMap.ext; intro v
  -- Expand both sides using CLM operations
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, map_sub]
  -- Use hcomm: L'(exp v) = exp(L' v), rearranged to exp(L' v) = L'(exp v)
  have hcomm_v : expSemigroupCLM L' s (L' v) =
      L' (expSemigroupCLM L' s v) :=
    (DFunLike.congr_fun hcomm v).symm
  rw [hcomm_v]
  -- Goal: -(A(L(Cv))) + A(L'(Cv)) = A(L'(Cv)) - A(L(Cv))
  -- This is -a + b = b - a in the additive group of matrices
  abel

/-- **Lemma 7.1** (Duhamel formula for matrix semigroups). -/
theorem duhamel_formula
    (L L' : MatrixCLM (Fin D)) (t : ℝ) (ht : 0 ≤ t) :
    expSemigroupCLM L' t - expSemigroupCLM L t =
      ∫ s in Set.Icc 0 t,
        expSemigroupCLM L (t - s) * (L' - L) * expSemigroupCLM L' s := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht]
  -- Step 1: derivative
  have hderiv : ∀ s ∈ Set.uIcc 0 t,
      HasDerivAt (fun u => expSemigroupCLM L (t - u) * expSemigroupCLM L' u)
        (expSemigroupCLM L (t - s) * (L' - L) * expSemigroupCLM L' s) s :=
    fun s _ => hasDerivAt_semigroup_product L L' t s
  have hcont :
      Continuous (fun s => expSemigroupCLM L (t - s) * (L' - L) * expSemigroupCLM L' s) := by
    apply Continuous.mul
    · apply Continuous.mul
      · exact (expSemigroupCLM_continuous L).comp (continuous_const.sub continuous_id)
      · exact continuous_const
    · exact expSemigroupCLM_continuous L'
  -- Step 2: Integrability of the derivative (continuous → integrable)
  have hintble : IntervalIntegrable
      (fun s => expSemigroupCLM L (t - s) * (L' - L) * expSemigroupCLM L' s)
      MeasureTheory.volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht]
    exact hcont.continuousOn.integrableOn_Icc
  -- Step 3: Apply FTC-2: ∫₀ᵗ f'(s) ds = f(t) - f(0)
  -- where f(s) = expSemigroupCLM L (t - s) * expSemigroupCLM L' s
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hintble]
  -- Simplify f(t) - f(0):
  -- f(t) = expSemigroupCLM L (t - t) * expSemigroupCLM L' t = 1 * T' t = T' t
  -- f(0) = expSemigroupCLM L (t - 0) * expSemigroupCLM L' 0 = T t * 1 = T t
  simpa [sub_self, sub_zero, expSemigroupCLM_zero, one_mul, mul_one]

/-! ## Helper for biSup bounds -/

private lemma norm_expSemigroup_le_biSup (L : MatrixCLM (Fin D)) {t : ℝ} (ht : 0 ≤ t)
    {x : ℝ} (hx : x ∈ Set.Icc 0 t) :
    ‖expSemigroupCLM L x‖ ≤ ⨆ s ∈ Set.Icc 0 t, ‖expSemigroupCLM L s‖ := by
  have hbdd : BddAbove ((fun s => ‖expSemigroupCLM L s‖) '' Set.Icc 0 t) :=
    isCompact_Icc.bddAbove_image
      (continuous_norm.comp (expSemigroupCLM_continuous L)).continuousOn
  obtain ⟨C, hC⟩ := hbdd
  have hC_nonneg : 0 ≤ C :=
    le_trans (norm_nonneg _) (hC ⟨0, Set.left_mem_Icc.mpr ht, rfl⟩)
  -- BddAbove for the outer iSup
  have hbdd_outer : BddAbove (Set.range
      (fun s => ⨆ (_ : s ∈ Set.Icc 0 t), ‖expSemigroupCLM L s‖)) := by
    refine ⟨C, fun a ⟨s, hs⟩ => ?_⟩
    subst hs
    change (⨆ (_ : s ∈ Set.Icc 0 t), ‖expSemigroupCLM L s‖) ≤ C
    by_cases hsm : s ∈ Set.Icc 0 t
    · rw [ciSup_pos hsm]; exact hC ⟨s, hsm, rfl⟩
    · rw [ciSup_neg hsm, Real.sSup_empty]; exact hC_nonneg
  -- Main bound
  have h1 : ‖expSemigroupCLM L x‖ =
      ⨆ (_ : x ∈ Set.Icc 0 t), ‖expSemigroupCLM L x‖ :=
    (ciSup_pos (f := fun _ => ‖expSemigroupCLM L x‖) hx).symm
  rw [h1]
  exact le_ciSup hbdd_outer x

/-! ## Corollary 7.1: Perturbation bound -/

/-- **Corollary 7.1** (perturbation of generators). -/
theorem perturbation_bound
    (L L' : MatrixCLM (Fin D)) (t : ℝ) (ht : 0 ≤ t) :
    ‖expSemigroupCLM L' t - expSemigroupCLM L t‖ ≤
      t * ‖L' - L‖ *
        (⨆ s ∈ Set.Icc 0 t, ‖expSemigroupCLM L s‖) *
        (⨆ s ∈ Set.Icc 0 t, ‖expSemigroupCLM L' s‖) := by
  rw [duhamel_formula L L' t ht]
  set Δ := L' - L
  set M := ⨆ s ∈ Set.Icc 0 t, ‖expSemigroupCLM L s‖
  set M' := ⨆ s ∈ Set.Icc 0 t, ‖expSemigroupCLM L' s‖
  have hmeas : volume (Set.Icc (0 : ℝ) t) < ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  have hpointwise : ∀ s ∈ Set.Icc 0 t,
      ‖expSemigroupCLM L (t - s) * Δ * expSemigroupCLM L' s‖ ≤ M * ‖Δ‖ * M' := by
    intro s hs
    calc ‖expSemigroupCLM L (t - s) * Δ * expSemigroupCLM L' s‖
        ≤ ‖expSemigroupCLM L (t - s) * Δ‖ * ‖expSemigroupCLM L' s‖ := norm_mul_le _ _
      _ ≤ ‖expSemigroupCLM L (t - s)‖ * ‖Δ‖ * ‖expSemigroupCLM L' s‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ M * ‖Δ‖ * M' := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)) ?_
            (norm_nonneg _) (mul_nonneg ?_ (norm_nonneg _))
          · exact norm_expSemigroup_le_biSup L ht
              ⟨sub_nonneg.mpr hs.2, sub_le_self t hs.1⟩
          · exact norm_expSemigroup_le_biSup L' ht hs
          · exact le_trans (norm_nonneg _)
              (norm_expSemigroup_le_biSup L ht (Set.left_mem_Icc.mpr ht))
  calc ‖∫ s in Set.Icc 0 t, expSemigroupCLM L (t - s) * Δ * expSemigroupCLM L' s‖
      ≤ M * ‖Δ‖ * M' * (volume (Set.Icc (0 : ℝ) t)).toReal :=
        norm_setIntegral_le_of_norm_le_const hmeas hpointwise
    _ = t * ‖Δ‖ * M * M' := by
        rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ t - 0)]
        ring

/-- Simplified perturbation bound for quantum channels (where ‖T_s‖ ≤ 1):
`‖T'_t - T_t‖ ≤ t · ‖Δ‖`. -/
theorem perturbation_bound_unit_norm
    (L L' : MatrixCLM (Fin D)) (t : ℝ) (ht : 0 ≤ t)
    (hT : ∀ s ∈ Set.Icc 0 t, ‖expSemigroupCLM L s‖ ≤ 1)
    (hT' : ∀ s ∈ Set.Icc 0 t, ‖expSemigroupCLM L' s‖ ≤ 1) :
    ‖expSemigroupCLM L' t - expSemigroupCLM L t‖ ≤ t * ‖L' - L‖ := by
  rw [duhamel_formula L L' t ht]
  set Δ := L' - L
  have hmeas : volume (Set.Icc (0 : ℝ) t) < ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  have hpointwise : ∀ s ∈ Set.Icc 0 t,
      ‖expSemigroupCLM L (t - s) * Δ * expSemigroupCLM L' s‖ ≤ ‖Δ‖ := by
    intro s hs
    calc ‖expSemigroupCLM L (t - s) * Δ * expSemigroupCLM L' s‖
        ≤ ‖expSemigroupCLM L (t - s) * Δ‖ * ‖expSemigroupCLM L' s‖ := norm_mul_le _ _
      _ ≤ ‖expSemigroupCLM L (t - s)‖ * ‖Δ‖ * ‖expSemigroupCLM L' s‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ 1 * ‖Δ‖ * 1 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)) ?_
            (norm_nonneg _) (by positivity)
          · exact hT _ ⟨sub_nonneg.mpr hs.2, sub_le_self t hs.1⟩
          · exact hT' _ hs
      _ = ‖Δ‖ := by ring
  calc ‖∫ s in Set.Icc 0 t, expSemigroupCLM L (t - s) * Δ * expSemigroupCLM L' s‖
      ≤ ‖Δ‖ * (volume (Set.Icc (0 : ℝ) t)).toReal :=
        norm_setIntegral_le_of_norm_le_const hmeas hpointwise
    _ = t * ‖Δ‖ := by
        rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ t - 0)]
        ring

/-! ## Dyson-Phillips iterates -/

/-- Recursive Dyson-Phillips terms built from the unperturbed semigroup `L`
and perturbation `L' - L`. -/
noncomputable def dysonTerm
    (L L' : MatrixCLM (Fin D)) (t : ℝ) : ℕ → MatrixCLM (Fin D)
  | 0 => expSemigroupCLM L t
  | n + 1 =>
      ∫ s in Set.Icc 0 t,
        expSemigroupCLM L (t - s) * (L' - L) * dysonTerm L L' s n

@[simp] lemma dysonTerm_zero (L L' : MatrixCLM (Fin D)) (t : ℝ) :
    dysonTerm L L' t 0 = expSemigroupCLM L t := rfl

@[simp] lemma dysonTerm_succ (L L' : MatrixCLM (Fin D)) (t : ℝ) (n : ℕ) :
    dysonTerm L L' t (n + 1) =
      ∫ s in Set.Icc 0 t,
        expSemigroupCLM L (t - s) * (L' - L) * dysonTerm L L' s n := rfl

/-- Zeroth Dyson term is controlled by the same compact-interval `iSup` used above. -/
lemma norm_dysonTerm_zero_le
    (L L' : MatrixCLM (Fin D)) {t : ℝ} (ht : 0 ≤ t) :
    ‖dysonTerm L L' t 0‖ ≤ ⨆ s ∈ Set.Icc 0 t, ‖expSemigroupCLM L s‖ := by
  simpa [dysonTerm] using
    (norm_expSemigroup_le_biSup (L := L) (t := t) ht (x := t) (Set.right_mem_Icc.mpr ht))

/-- One-step norm estimate for the Dyson recursion.
This is the inductive estimate used to bootstrap higher-order bounds. -/
lemma norm_dysonTerm_succ_le
    (L L' : MatrixCLM (Fin D)) {t K : ℝ} (ht : 0 ≤ t) (n : ℕ)
    (hK : ∀ s ∈ Set.Icc 0 t, ‖dysonTerm L L' s n‖ ≤ K) :
    ‖dysonTerm L L' t (n + 1)‖ ≤
      t *
        (⨆ s ∈ Set.Icc 0 t, ‖expSemigroupCLM L s‖) * ‖L' - L‖ * K := by
  rw [dysonTerm_succ]
  set M : ℝ := ⨆ s ∈ Set.Icc 0 t, ‖expSemigroupCLM L s‖
  have hmeas : volume (Set.Icc (0 : ℝ) t) < ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hpointwise : ∀ s ∈ Set.Icc 0 t,
      ‖expSemigroupCLM L (t - s) * (L' - L) * dysonTerm L L' s n‖ ≤ M * ‖L' - L‖ * K := by
    intro s hs
    calc ‖expSemigroupCLM L (t - s) * (L' - L) * dysonTerm L L' s n‖
        ≤ ‖expSemigroupCLM L (t - s) * (L' - L)‖ * ‖dysonTerm L L' s n‖ := norm_mul_le _ _
      _ ≤ ‖expSemigroupCLM L (t - s)‖ * ‖L' - L‖ * ‖dysonTerm L L' s n‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ M * ‖L' - L‖ * K := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)) ?_
            (norm_nonneg _) (mul_nonneg ?_ (norm_nonneg _))
          · exact norm_expSemigroup_le_biSup L ht
              ⟨sub_nonneg.mpr hs.2, sub_le_self t hs.1⟩
          · exact hK s hs
          · exact le_trans (norm_nonneg _)
              (norm_expSemigroup_le_biSup L ht (Set.left_mem_Icc.mpr ht))
  calc ‖∫ s in Set.Icc 0 t, expSemigroupCLM L (t - s) * (L' - L) * dysonTerm L L' s n‖
      ≤ M * ‖L' - L‖ * K * (volume (Set.Icc (0 : ℝ) t)).toReal :=
        norm_setIntegral_le_of_norm_le_const hmeas hpointwise
    _ = t * M * ‖L' - L‖ * K := by
        rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ t - 0)]
        ring
    _ = t * (⨆ s ∈ Set.Icc 0 t, ‖expSemigroupCLM L s‖) * ‖L' - L‖ * K := by
        simp [M, mul_left_comm, mul_comm]

/-- Summability criterion for Dyson terms from a factorial majorant.
This packages the M-test step independently of the inductive norm proof. -/
lemma summable_dysonTerm_of_factorial_bound
    (L L' : MatrixCLM (Fin D)) {t M : ℝ}
    (hbound : ∀ n, ‖dysonTerm L L' t n‖ ≤ M * ((t * ‖L' - L‖ * M) ^ n / ↑(n.factorial))) :
    Summable (fun n => dysonTerm L L' t n) := by
  refine Summable.of_norm_bounded ?_ hbound
  simpa [mul_div_assoc, mul_comm, mul_left_comm, mul_assoc] using
    (Real.summable_pow_div_factorial (t * ‖L' - L‖ * M)).mul_left M

-- TODO(#14): combine `norm_dysonTerm_zero_le`/`norm_dysonTerm_succ_le` into a factorial
-- majorant theorem and apply `summable_dysonTerm_of_factorial_bound` in the final
-- Dyson-series convergence/identity statement.

end -- noncomputable section
