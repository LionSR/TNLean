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
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Perturbation theory for dynamical semigroups — Wolf §7.1

## Main results

* `duhamel_formula` — **Lemma 7.1** (Duhamel/perturbation integral formula)
* `perturbation_bound` — **Corollary 7.1** (perturbation of generators)
* `dysonTerm_continuous` — continuity of each Dyson iterate in the time parameter
* `norm_dysonRemainder_le` — factorial norm bound on the Dyson partial-sum remainder
* `dyson_series_eq` — **Eq. 7.13** (Dyson–Phillips series = perturbed semigroup)
* `tsum_dysonTerm_eq` — tsum form of the Dyson series identity

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

/-- Summability criterion for Dyson terms from a factorial majorant.
This packages the M-test step independently of the inductive norm proof. -/
lemma summable_dysonTerm_of_factorial_bound
    (L L' : MatrixCLM (Fin D)) {t M : ℝ}
    (hbound : ∀ n, ‖dysonTerm L L' t n‖ ≤ M * ((t * ‖L' - L‖ * M) ^ n / ↑(n.factorial))) :
    Summable (fun n => dysonTerm L L' t n) := by
  refine Summable.of_norm_bounded ?_ hbound
  simpa [mul_div_assoc, mul_comm, mul_left_comm, mul_assoc] using
    (Real.summable_pow_div_factorial (t * ‖L' - L‖ * M)).mul_left M

/-- Factorial norm bound for Dyson–Phillips iterates (Wolf Eq. 7.13 estimate).
For `s ∈ [0, t]` and `M = sup_{u ∈ [0,t]} ‖exp(uL)‖`:
`‖T̃ⁿ(s)‖ ≤ M · (s · ‖Δ‖ · M)ⁿ / n!`. -/
theorem norm_dysonTerm_le (L L' : MatrixCLM (Fin D)) {t : ℝ} (ht : 0 ≤ t) (n : ℕ)
    {s : ℝ} (hs : s ∈ Set.Icc 0 t) :
    ‖dysonTerm L L' s n‖ ≤
      (⨆ u ∈ Set.Icc 0 t, ‖expSemigroupCLM L u‖) *
      ((s * ‖L' - L‖ * (⨆ u ∈ Set.Icc 0 t, ‖expSemigroupCLM L u‖)) ^ n /
        ↑(n.factorial)) := by
  induction n generalizing s with
  | zero =>
    simp only [dysonTerm_zero, pow_zero, Nat.factorial_zero,
      Nat.cast_one, div_one, mul_one]
    exact norm_expSemigroup_le_biSup L ht hs
  | succ n ih =>
    rw [dysonTerm_succ]
    set M := ⨆ u ∈ Set.Icc 0 t, ‖expSemigroupCLM L u‖ with hM_def
    have hs0 : (0 : ℝ) ≤ s := hs.1
    have hst : s ≤ t := hs.2
    have hM_nn : 0 ≤ M :=
      le_trans (norm_nonneg _)
        (norm_expSemigroup_le_biSup L ht (Set.left_mem_Icc.mpr ht))
    -- Constant factor in the pointwise bound
    set C : ℝ := M * ‖L' - L‖ * M * (‖L' - L‖ * M) ^ n / ↑(n.factorial)
      with hC_def
    -- Pointwise bound: ‖integrand(u)‖ ≤ C · uⁿ for u ∈ [0, s]
    have hpw : ∀ u ∈ Set.Icc 0 s,
        ‖expSemigroupCLM L (s - u) * (L' - L) * dysonTerm L L' u n‖ ≤
          C * u ^ n := by
      intro u hu
      have hu_t : u ∈ Set.Icc 0 t := ⟨hu.1, le_trans hu.2 hst⟩
      have hsu_t : s - u ∈ Set.Icc 0 t :=
        ⟨sub_nonneg.mpr hu.2, le_trans (sub_le_self s hu.1) hst⟩
      calc ‖expSemigroupCLM L (s - u) * (L' - L) * dysonTerm L L' u n‖
          ≤ ‖expSemigroupCLM L (s - u)‖ * ‖L' - L‖ *
              ‖dysonTerm L L' u n‖ := by
            calc _ ≤ ‖expSemigroupCLM L (s - u) * (L' - L)‖ *
                      ‖dysonTerm L L' u n‖ := norm_mul_le _ _
              _ ≤ _ := mul_le_mul_of_nonneg_right
                    (norm_mul_le _ _) (norm_nonneg _)
        _ ≤ M * ‖L' - L‖ *
              (M * ((u * ‖L' - L‖ * M) ^ n / ↑(n.factorial))) := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_right
                (norm_expSemigroup_le_biSup L ht hsu_t) (norm_nonneg _)
            · exact ih hu_t
            · exact norm_nonneg _
            · exact mul_nonneg hM_nn (norm_nonneg _)
        _ = C * u ^ n := by simp only [hC_def, mul_pow]; ring
    -- Convert set integral to interval integral
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs0]
    -- Integrability of the bound function
    have hCu_int : IntervalIntegrable (fun u => C * u ^ n) volume 0 s :=
      (continuous_const.mul (continuous_pow n)).intervalIntegrable 0 s
    -- Bound norm of interval integral, then compute
    calc ‖∫ u in (0 : ℝ)..s, expSemigroupCLM L (s - u) * (L' - L) *
            dysonTerm L L' u n‖
        ≤ ∫ u in (0 : ℝ)..s, C * u ^ n :=
          intervalIntegral.norm_integral_le_of_norm_le hs0
            (ae_of_all _ fun u hu =>
              hpw u (Set.Ioc_subset_Icc_self hu)) hCu_int
      _ = C * (s ^ (n + 1) / ((n : ℝ) + 1)) := by
          rw [intervalIntegral.integral_const_mul, integral_pow,
              zero_pow (Nat.succ_ne_zero n), sub_zero]
      _ = M * ((s * ‖L' - L‖ * M) ^ (n + 1) /
            ↑((n + 1).factorial)) := by
          rw [hC_def, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
          have : (↑(n.factorial) : ℝ) ≠ 0 :=
            Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
          have : (↑n : ℝ) + 1 ≠ 0 := by positivity
          field_simp
          ring

/-- Factorial norm bound specialised to `s = t`. -/
theorem norm_dysonTerm_le_at (L L' : MatrixCLM (Fin D)) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    ‖dysonTerm L L' t n‖ ≤
      (⨆ u ∈ Set.Icc 0 t, ‖expSemigroupCLM L u‖) *
      ((t * ‖L' - L‖ * (⨆ u ∈ Set.Icc 0 t, ‖expSemigroupCLM L u‖)) ^ n /
        ↑(n.factorial)) :=
  norm_dysonTerm_le L L' ht n (Set.right_mem_Icc.mpr ht)

/-- The Dyson–Phillips series `∑ₙ T̃ⁿ(t)` converges in operator norm. -/
theorem summable_dysonTerm (L L' : MatrixCLM (Fin D)) {t : ℝ} (ht : 0 ≤ t) :
    Summable (fun n => dysonTerm L L' t n) :=
  summable_dysonTerm_of_factorial_bound L L'
    (fun n => norm_dysonTerm_le_at L L' ht n)

/-! ## Continuity of Dyson iterates -/

/-- The `(n+1)`-th Dyson term vanishes for non-positive time. -/
private lemma dysonTerm_succ_nonpos (L L' : MatrixCLM (Fin D)) (n : ℕ) {t : ℝ}
    (ht : t ≤ 0) : dysonTerm L L' t (n + 1) = 0 := by
  rw [dysonTerm_succ]
  apply setIntegral_measure_zero
  rw [Real.volume_Icc, ENNReal.ofReal_eq_zero]
  linarith

/-- For `t ≥ 0`, the set integral `∫ s in Icc 0 t` equals the interval integral `∫ s in 0..t`. -/
private lemma setIntegral_Icc_eq_intervalIntegral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} {t : ℝ} (ht : 0 ≤ t) :
    ∫ s in Set.Icc 0 t, f s = ∫ s in (0 : ℝ)..t, f s := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht]

/-- Each Dyson iterate `t ↦ T̃ⁿ(t)` is continuous in the time parameter. -/
theorem dysonTerm_continuous (L L' : MatrixCLM (Fin D)) (n : ℕ) :
    Continuous (fun t => dysonTerm L L' t n) := by
  induction n with
  | zero => exact expSemigroupCLM_continuous L
  | succ n ih =>
    -- The interval integral version G(t) = ∫₀ᵗ T_{t-s} Δ T̃ⁿ(s) ds is globally continuous.
    set g : ℝ → ℝ → MatrixCLM (Fin D) :=
      fun t s => expSemigroupCLM L (t - s) * (L' - L) * dysonTerm L L' s n
    have hg_cont : Continuous g.uncurry := by
      apply Continuous.mul
      · apply Continuous.mul
        · exact (expSemigroupCLM_continuous L).comp (continuous_fst.sub continuous_snd)
        · exact continuous_const
      · exact ih.comp continuous_snd
    have hG_cont : Continuous (fun t : ℝ => ∫ s in (0 : ℝ)..t, g t s) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hg_cont continuous_id
    -- On Ici 0: dysonTerm agrees with the interval integral (hence continuous there).
    have h_Ici : ContinuousOn (fun t => dysonTerm L L' t (n + 1)) (Set.Ici 0) := by
      apply ContinuousOn.congr hG_cont.continuousOn
      intro t ht
      dsimp only
      rw [dysonTerm_succ, setIntegral_Icc_eq_intervalIntegral ht]
    -- On Iic 0: dysonTerm is 0 (hence continuous there).
    have h_Iic : ContinuousOn (fun t => dysonTerm L L' t (n + 1)) (Set.Iic 0) := by
      apply ContinuousOn.congr continuousOn_const
      intro t ht
      exact dysonTerm_succ_nonpos L L' n ht
    -- Paste: Ici 0 ∪ Iic 0 = univ, both are closed.
    rw [← continuousOn_univ, ← Set.Ici_union_Iic (a := (0 : ℝ))]
    exact h_Ici.union_of_isClosed h_Iic isClosed_Ici isClosed_Iic

/-! ## Integrability of Dyson integrands -/

/-- The integrand `s ↦ T_{t−s} Δ T̃ⁿ(s)` is integrable on `[0, t]`. -/
private lemma integrableOn_dyson_integrand (L L' : MatrixCLM (Fin D)) (n : ℕ) {t : ℝ}
    (ht : 0 ≤ t) :
    IntegrableOn
      (fun s => expSemigroupCLM L (t - s) * (L' - L) * dysonTerm L L' s n)
      (Set.Icc 0 t) := by
  apply ContinuousOn.integrableOn_Icc
  apply ContinuousOn.mul
  · apply ContinuousOn.mul
    · exact ((expSemigroupCLM_continuous L).comp
        (continuous_const.sub continuous_id)).continuousOn
    · exact continuousOn_const
  · exact (dysonTerm_continuous L L' n).continuousOn

/-- The integrand for the remainder is integrable on `[0, t]`. -/
private lemma integrableOn_remainder_integrand (L L' : MatrixCLM (Fin D)) (N : ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn
      (fun s => expSemigroupCLM L (t - s) * (L' - L) *
        (expSemigroupCLM L' s - ∑ n ∈ Finset.range N, dysonTerm L L' s n))
      (Set.Icc 0 t) := by
  apply ContinuousOn.integrableOn_Icc
  apply ContinuousOn.mul
  · apply ContinuousOn.mul
    · exact ((expSemigroupCLM_continuous L).comp
        (continuous_const.sub continuous_id)).continuousOn
    · exact continuousOn_const
  · exact ((expSemigroupCLM_continuous L').sub
      (continuous_finset_sum _ fun n _ => dysonTerm_continuous L L' n)).continuousOn

/-! ## Dyson series identity (Wolf Eq. 7.13) -/

/-- Integral representation of the Dyson series remainder:
`T'_t − ∑_{n<N+1} T̃ⁿ(t) = ∫₀ᵗ T_{t−s} Δ (T'_s − ∑_{n<N} T̃ⁿ(s)) ds`. -/
private theorem dysonRemainder_integral_eq (L L' : MatrixCLM (Fin D))
    {t : ℝ} (ht : 0 ≤ t) (N : ℕ) :
    expSemigroupCLM L' t - ∑ n ∈ Finset.range (N + 1), dysonTerm L L' t n =
      ∫ s in Set.Icc 0 t, expSemigroupCLM L (t - s) * (L' - L) *
        (expSemigroupCLM L' s - ∑ n ∈ Finset.range N, dysonTerm L L' s n) := by
  induction N with
  | zero =>
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      dysonTerm_zero, sub_zero]
    exact duhamel_formula L L' t ht
  | succ N ihN =>
    -- Expand the partial sum: range(N+2) = range(N+1) ∪ {N+1}
    rw [Finset.sum_range_succ]
    -- T'_t - (∑_{n<N+1} + T̃^{N+1}) = (T'_t - ∑_{n<N+1}) - T̃^{N+1}
    have hkey : expSemigroupCLM L' t -
        (∑ n ∈ Finset.range (N + 1), dysonTerm L L' t n + dysonTerm L L' t (N + 1)) =
        (expSemigroupCLM L' t - ∑ n ∈ Finset.range (N + 1), dysonTerm L L' t n) -
        dysonTerm L L' t (N + 1) := by abel
    rw [hkey, ihN]
    -- RHS of IH is ∫ T Δ R_N, and T̃^{N+1} = ∫ T Δ T̃ᴺ
    rw [dysonTerm_succ]
    -- Need: ∫ T Δ R_N - ∫ T Δ T̃ᴺ = ∫ T Δ (R_N - T̃ᴺ)
    -- where R_N(s) = T'_s - ∑_{n<N} T̃ⁿ(s)
    -- and R_{N+1}(s) = T'_s - ∑_{n<N+1} T̃ⁿ(s) = R_N(s) - T̃ᴺ(s)
    rw [← MeasureTheory.integral_sub
      (integrableOn_remainder_integrand L L' N ht)
      (integrableOn_dyson_integrand L L' N ht)]
    congr 1; ext s
    simp only [Finset.sum_range_succ, mul_sub, mul_add, sub_sub]

/-- **Factorial norm bound on the Dyson series remainder.**
For `s ∈ [0,t]`, `M = sup_{u ∈ [0,t]} ‖T_u‖`, `M' = sup_{u ∈ [0,t]} ‖T'_u‖`:
`‖T'_s − ∑_{n<N} T̃ⁿ(s)‖ ≤ M' · (s · ‖Δ‖ · M)^N / N!`. -/
theorem norm_dysonRemainder_le (L L' : MatrixCLM (Fin D)) {t : ℝ} (ht : 0 ≤ t) (N : ℕ)
    {s : ℝ} (hs : s ∈ Set.Icc 0 t) :
    ‖expSemigroupCLM L' s - ∑ n ∈ Finset.range N, dysonTerm L L' s n‖ ≤
      (⨆ u ∈ Set.Icc 0 t, ‖expSemigroupCLM L' u‖) *
      ((s * ‖L' - L‖ * (⨆ u ∈ Set.Icc 0 t, ‖expSemigroupCLM L u‖)) ^ N /
        ↑(N.factorial)) := by
  induction N generalizing s with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero,
      Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
    exact norm_expSemigroup_le_biSup L' ht hs
  | succ N ihN =>
    have hrep := dysonRemainder_integral_eq L L' hs.1 N
    rw [hrep]
    set M := ⨆ u ∈ Set.Icc 0 t, ‖expSemigroupCLM L u‖
    set M' := ⨆ u ∈ Set.Icc 0 t, ‖expSemigroupCLM L' u‖
    have hs0 : (0 : ℝ) ≤ s := hs.1
    have hst : s ≤ t := hs.2
    have hM_nn : 0 ≤ M :=
      le_trans (norm_nonneg _)
        (norm_expSemigroup_le_biSup L ht (Set.left_mem_Icc.mpr ht))
    have hM'_nn : 0 ≤ M' :=
      le_trans (norm_nonneg _)
        (norm_expSemigroup_le_biSup L' ht (Set.left_mem_Icc.mpr ht))
    -- Pointwise bound on the integrand
    set C : ℝ := M * ‖L' - L‖ * M' * (‖L' - L‖ * M) ^ N / ↑(N.factorial) with hC_def
    have hpw : ∀ u ∈ Set.Icc 0 s,
        ‖expSemigroupCLM L (s - u) * (L' - L) *
          (expSemigroupCLM L' u - ∑ n ∈ Finset.range N, dysonTerm L L' u n)‖ ≤
          C * u ^ N := by
      intro u hu
      have hu_t : u ∈ Set.Icc 0 t := ⟨hu.1, le_trans hu.2 hst⟩
      have hsu_t : s - u ∈ Set.Icc 0 t :=
        ⟨sub_nonneg.mpr hu.2, le_trans (sub_le_self s hu.1) hst⟩
      calc ‖expSemigroupCLM L (s - u) * (L' - L) *
              (expSemigroupCLM L' u - ∑ n ∈ Finset.range N, dysonTerm L L' u n)‖
          ≤ ‖expSemigroupCLM L (s - u)‖ * ‖L' - L‖ *
              ‖expSemigroupCLM L' u - ∑ n ∈ Finset.range N, dysonTerm L L' u n‖ := by
            calc _ ≤ ‖expSemigroupCLM L (s - u) * (L' - L)‖ * ‖_‖ := norm_mul_le _ _
              _ ≤ _ := mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
        _ ≤ M * ‖L' - L‖ *
              (M' * ((u * ‖L' - L‖ * M) ^ N / ↑(N.factorial))) := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_right
                (norm_expSemigroup_le_biSup L ht hsu_t) (norm_nonneg _)
            · exact ihN hu_t
            · exact norm_nonneg _
            · exact mul_nonneg hM_nn (norm_nonneg _)
        _ = C * u ^ N := by simp only [hC_def, mul_pow]; ring
    -- Convert set integral to interval integral
    rw [setIntegral_Icc_eq_intervalIntegral hs0]
    -- Integrability of the bound function
    have hCu_int : IntervalIntegrable (fun u => C * u ^ N) volume 0 s :=
      (continuous_const.mul (continuous_pow N)).intervalIntegrable 0 s
    -- Bound the norm of the integral
    calc ‖∫ u in (0 : ℝ)..s, expSemigroupCLM L (s - u) * (L' - L) *
            (expSemigroupCLM L' u - ∑ n ∈ Finset.range N, dysonTerm L L' u n)‖
        ≤ ∫ u in (0 : ℝ)..s, C * u ^ N :=
          intervalIntegral.norm_integral_le_of_norm_le hs0
            (ae_of_all _ fun u hu =>
              hpw u (Set.Ioc_subset_Icc_self hu)) hCu_int
      _ = C * (s ^ (N + 1) / ((N : ℝ) + 1)) := by
          rw [intervalIntegral.integral_const_mul, integral_pow,
              zero_pow (Nat.succ_ne_zero N), sub_zero]
      _ = M' * ((s * ‖L' - L‖ * M) ^ (N + 1) / ↑((N + 1).factorial)) := by
          rw [hC_def, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
          have : (↑(N.factorial) : ℝ) ≠ 0 :=
            Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
          have : (↑N : ℝ) + 1 ≠ 0 := by positivity
          field_simp
          ring

/-- **Dyson series identity** (Wolf Eq. 7.13):
the Dyson–Phillips series `∑ₙ T̃⁽ⁿ⁾(t)` equals the perturbed semigroup `T'_t`.
This completes the Dyson–Phillips expansion for matrix semigroups. -/
theorem dyson_series_eq (L L' : MatrixCLM (Fin D)) {t : ℝ} (ht : 0 ≤ t) :
    HasSum (fun n => dysonTerm L L' t n) (expSemigroupCLM L' t) := by
  -- The partial sums converge to the tsum (by summability).
  -- We show they also converge to T'_t, then use uniqueness of limits.
  -- Summable norms (for hasSum_iff_tendsto_nat)
  have hSn : Summable (fun n => ‖dysonTerm L L' t n‖) :=
    .of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => norm_dysonTerm_le_at L L' ht n)
      ((Real.summable_pow_div_factorial
        (t * ‖L' - L‖ * (⨆ u ∈ Set.Icc 0 t, ‖expSemigroupCLM L u‖))).mul_left
        (⨆ u ∈ Set.Icc 0 t, ‖expSemigroupCLM L u‖))
  rw [hasSum_iff_tendsto_nat_of_summable_norm hSn]
  -- Show partial sums converge to T'_t:
  -- ‖T'_t - ∑_{n<N} T̃ⁿ(t)‖ ≤ M' · (t·‖Δ‖·M)^N / N! → 0
  rw [Metric.tendsto_atTop]
  intro ε hε
  set c := t * ‖L' - L‖ * (⨆ u ∈ Set.Icc 0 t, ‖expSemigroupCLM L u‖)
  set M' := ⨆ u ∈ Set.Icc 0 t, ‖expSemigroupCLM L' u‖
  -- c^N / N! → 0
  have h_tend : Filter.Tendsto (fun N => M' * (c ^ N / ↑(N.factorial)))
      Filter.atTop (nhds 0) := by
    rw [show (0 : ℝ) = M' * 0 from (mul_zero _).symm]
    exact Filter.Tendsto.mul tendsto_const_nhds
      (FloorSemiring.tendsto_pow_div_factorial_atTop c)
  rw [Metric.tendsto_atTop] at h_tend
  obtain ⟨N₀, hN₀⟩ := h_tend ε hε
  refine ⟨N₀, fun N hN => ?_⟩
  rw [dist_comm, dist_eq_norm]
  calc ‖expSemigroupCLM L' t - ∑ n ∈ Finset.range N, dysonTerm L L' t n‖
      ≤ M' * (c ^ N / ↑(N.factorial)) :=
        norm_dysonRemainder_le L L' ht N (Set.right_mem_Icc.mpr ht)
    _ = |M' * (c ^ N / ↑(N.factorial)) - 0| := by
        rw [sub_zero, abs_of_nonneg]
        have hc_nn : 0 ≤ c := mul_nonneg (mul_nonneg ht (norm_nonneg _))
          (le_trans (norm_nonneg _)
            (norm_expSemigroup_le_biSup L ht (Set.left_mem_Icc.mpr ht)))
        exact mul_nonneg
          (le_trans (norm_nonneg _)
            (norm_expSemigroup_le_biSup L' ht (Set.left_mem_Icc.mpr ht)))
          (div_nonneg (pow_nonneg hc_nn _) (Nat.cast_nonneg' _))
    _ = dist (M' * (c ^ N / ↑(N.factorial))) 0 := (Real.dist_eq _ _).symm
    _ < ε := hN₀ N hN

/-- The tsum of the Dyson–Phillips series equals the perturbed semigroup. -/
theorem tsum_dysonTerm_eq (L L' : MatrixCLM (Fin D)) {t : ℝ} (ht : 0 ≤ t) :
    ∑' n, dysonTerm L L' t n = expSemigroupCLM L' t :=
  (dyson_series_eq L L' ht).tsum_eq

end -- noncomputable section
