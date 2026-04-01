/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Semigroup.Basic

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.ODE.Gronwall

/-!
# Perturbation bound for dynamical semigroups — Wolf Lemma 7.1 and Corollary 7.1

## Main results

* `duhamel_formula` — **Lemma 7.1** (Duhamel/perturbation integral formula)
* `perturbation_bound` — **Corollary 7.1** (perturbation of generators)

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, §7.1][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder BigOperators NNReal
open Matrix Finset NormedSpace MeasureTheory

noncomputable section

variable {D : ℕ}

attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

private abbrev CLM (D : ℕ) :=
  Matrix (Fin D) (Fin D) ℂ →L[ℂ] Matrix (Fin D) (Fin D) ℂ

/-! ## Derivative of the semigroup product -/

/-- HasDerivAt for `s ↦ exp((t-s)•L) * exp(s•L')` with derivative
`exp((t-s)•L) * (L' - L) * exp(s•L')`. Both derivatives go through ℂ
to ensure instance consistency. -/
private theorem hasDerivAt_semigroup_product
    (L L' : CLM D) (t s : ℝ) :
    HasDerivAt (fun u => expSemigroupCLM L (t - u) * expSemigroupCLM L' u)
      (expSemigroupCLM L (t - s) * (L' - L) * expSemigroupCLM L' s) s := by
  simp only [expSemigroupCLM]
  -- Cast lemma
  have hcast : ∀ u : ℝ, ((t - u : ℝ) : ℂ) = (t : ℂ) - (u : ℂ) := by
    intro u; push_cast; ring
  -- Inner maps ℝ → ℂ
  have h_ofReal : HasDerivAt (fun u : ℝ => (u : ℂ)) (1 : ℂ) s :=
    Complex.ofRealCLM.hasDerivAt
  have h_tsub : HasDerivAt (fun u : ℝ => (t : ℂ) - (u : ℂ)) (-1 : ℂ) s :=
    h_ofReal.const_sub (t : ℂ)
  -- Outer maps ℂ → CLM
  have hexp_L := hasDerivAt_exp_smul_const (𝕂 := ℂ) L ((t : ℂ) - (s : ℂ))
  have hexp_L' := hasDerivAt_exp_smul_const (𝕂 := ℂ) L' (s : ℂ)
  -- Chain rule: compose ℝ → ℂ → CLM
  have hg := hexp_L.scomp s h_tsub
  have hh := hexp_L'.scomp s h_ofReal
  simp only [Function.comp_def, neg_smul, one_smul] at hg hh
  -- Rewrite cast
  simp_rw [hcast] at hg ⊢
  -- Product rule (both hg and hh now use consistent instances)
  have hprod := hg.mul hh
  -- The derivative from product rule is: -(exp(...)* L) * exp(...) + exp(...) * (exp(...) * L')
  -- We need: exp(...) * (L' - L) * exp(...)
  suffices heq :
      -(NormedSpace.exp (((t : ℂ) - (s : ℂ)) • L) * L) * NormedSpace.exp ((s : ℂ) • L') +
      NormedSpace.exp (((t : ℂ) - (s : ℂ)) • L) * (NormedSpace.exp ((s : ℂ) • L') * L') =
      NormedSpace.exp (((t : ℂ) - (s : ℂ)) • L) * (L' - L) * NormedSpace.exp ((s : ℂ) • L') by
    rwa [heq] at hprod
  -- Commutativity: L' * exp(s•L') = exp(s•L') * L'
  have hcomm_smul : Commute L' ((s : ℂ) • L') := by
    ext v
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, map_smul]
  have hcomm : L' * NormedSpace.exp ((s : ℂ) • L') =
      NormedSpace.exp ((s : ℂ) • L') * L' :=
    hcomm_smul.exp_right.eq
  -- Prove the algebra at the pointwise level (avoids CLM instance diamonds with neg_mul)
  apply ContinuousLinearMap.ext; intro v
  -- Expand both sides using CLM operations
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, map_sub]
  -- Use hcomm: L'(exp v) = exp(L' v), rearranged to exp(L' v) = L'(exp v)
  have hcomm_v : NormedSpace.exp ((s : ℂ) • L') (L' v) =
      L' (NormedSpace.exp ((s : ℂ) • L') v) :=
    (DFunLike.congr_fun hcomm v).symm
  rw [hcomm_v]
  -- Goal: -(A(L(Cv))) + A(L'(Cv)) = A(L'(Cv)) - A(L(Cv))
  -- This is -a + b = b - a in the additive group of matrices
  abel

/-- **Lemma 7.1** (Duhamel formula for matrix semigroups). -/
theorem duhamel_formula
    (L L' : CLM D) (t : ℝ) (ht : 0 ≤ t) :
    expSemigroupCLM L' t - expSemigroupCLM L t =
      ∫ s in Set.Icc 0 t,
        expSemigroupCLM L (t - s) * (L' - L) * expSemigroupCLM L' s := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht]
  -- Step 1: derivative
  have hderiv : ∀ s ∈ Set.uIcc 0 t,
      HasDerivAt (fun u => expSemigroupCLM L (t - u) * expSemigroupCLM L' u)
        (expSemigroupCLM L (t - s) * (L' - L) * expSemigroupCLM L' s) s :=
    fun s _ => hasDerivAt_semigroup_product L L' t s
  -- Step 2: Integrability of the derivative (continuous → integrable)
  have hintble : IntervalIntegrable
      (fun s => expSemigroupCLM L (t - s) * (L' - L) * expSemigroupCLM L' s)
      MeasureTheory.volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul
    · apply ContinuousOn.mul
      · -- expSemigroupCLM L (t - ·) is continuous
        exact (expSemigroupCLM_continuous L).continuousOn.comp
          (continuous_const.sub continuous_id).continuousOn (Set.mapsTo_univ _ _)
      · exact continuousOn_const
    · exact (expSemigroupCLM_continuous L').continuousOn
  -- Step 3: Apply FTC-2: ∫₀ᵗ f'(s) ds = f(t) - f(0)
  -- where f(s) = expSemigroupCLM L (t - s) * expSemigroupCLM L' s
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hintble]
  -- Simplify f(t) - f(0):
  -- f(t) = expSemigroupCLM L (t - t) * expSemigroupCLM L' t = 1 * T' t = T' t
  -- f(0) = expSemigroupCLM L (t - 0) * expSemigroupCLM L' 0 = T t * 1 = T t
  simp only [sub_self, sub_zero, expSemigroupCLM_zero, one_mul, mul_one]

/-! ## Helper for biSup bounds -/

private lemma norm_expSemigroup_le_biSup (L : CLM D) {t : ℝ} (ht : 0 ≤ t)
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
    (L L' : CLM D) (t : ℝ) (ht : 0 ≤ t) :
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
    (L L' : CLM D) (t : ℝ) (ht : 0 ≤ t)
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
    (L L' : CLM D) (t : ℝ) : ℕ → CLM D
  | 0 => expSemigroupCLM L t
  | n + 1 =>
      ∫ s in Set.Icc 0 t,
        expSemigroupCLM L (t - s) * (L' - L) * dysonTerm L L' s n

@[simp] lemma dysonTerm_zero (L L' : CLM D) (t : ℝ) :
    dysonTerm L L' t 0 = expSemigroupCLM L t := rfl

@[simp] lemma dysonTerm_succ (L L' : CLM D) (t : ℝ) (n : ℕ) :
    dysonTerm L L' t (n + 1) =
      ∫ s in Set.Icc 0 t,
        expSemigroupCLM L (t - s) * (L' - L) * dysonTerm L L' s n := rfl

/-- Zeroth Dyson term is controlled by the same compact-interval `iSup` used above. -/
lemma norm_dysonTerm_zero_le
    (L L' : CLM D) {t : ℝ} (ht : 0 ≤ t) :
    ‖dysonTerm L L' t 0‖ ≤ ⨆ s ∈ Set.Icc 0 t, ‖expSemigroupCLM L s‖ := by
  simpa [dysonTerm] using
    (norm_expSemigroup_le_biSup (L := L) (t := t) ht (x := t) (Set.right_mem_Icc.mpr ht))

/-- One-step norm estimate for the Dyson recursion.
This is the inductive estimate used to bootstrap higher-order bounds. -/
lemma norm_dysonTerm_succ_le
    (L L' : CLM D) {t K : ℝ} (ht : 0 ≤ t) (n : ℕ)
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
    (L L' : CLM D) {t M : ℝ}
    (hbound : ∀ n, ‖dysonTerm L L' t n‖ ≤ M * ((t * ‖L' - L‖ * M) ^ n / (Nat.factorial n))) :
    Summable (fun n => dysonTerm L L' t n) := by
  refine Summable.of_norm_bounded ?_ hbound
  simpa [mul_div_assoc, mul_comm, mul_left_comm, mul_assoc] using
    (Real.summable_pow_div_factorial (t * ‖L' - L‖ * M)).mul_left M

/-- Consumer lemma for the Dyson-series convergence pipeline:
`factorial bound → summable Dyson terms`. -/
lemma dysonSeries_summable
    (L L' : CLM D) {t M : ℝ}
    (hbound : ∀ n, ‖dysonTerm L L' t n‖ ≤ M * ((t * ‖L' - L‖ * M) ^ n / (Nat.factorial n))) :
    Summable (fun n => dysonTerm L L' t n) :=
  summable_dysonTerm_of_factorial_bound (L := L) (L' := L') hbound

end -- noncomputable section
