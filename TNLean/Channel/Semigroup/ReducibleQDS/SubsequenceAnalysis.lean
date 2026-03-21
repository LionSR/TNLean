/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Semigroup.ReducibleQDS.GeneratorCompression

/-!
# Subsequence Analysis: (4) → (2) via Cesàro + subsequences

This file proves that block-upper-triangular Lindblad form implies the existence
of a rank-deficient kernel element (condition (2) of Wolf Prop 7.6).

The proof combines:
1. Cesàro fixed point within PMP
2. Parametric refinement using channels `exp((1/m)L)`
3. Generator vanishing via Taylor remainder bounds
-/

open scoped Matrix ComplexOrder BigOperators NNReal MatrixOrder
open Matrix Finset

noncomputable section

attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

-- Re-expose endCLMEquiv' for use in this file
private abbrev endCLMEquiv' :
    (Mat →ₗ[ℂ] Mat) ≃ₐ[ℂ] (Mat →L[ℂ] Mat) :=
  Module.End.toContinuousLinearMap Mat

/-! ## (4) → (2): Block-upper-triangular → rank-deficient kernel element -/

/-- An orthogonal projection is PSD: `P = P * P = P * Pᴴ` is a sum of PSD terms. -/
private lemma orthogonalProjection_posSemidef'
    {P : Mat} (hP : IsOrthogonalProjection P) : P.PosSemidef := by
  have : P = Pᴴ * P := by rw [hP.1, hP.2]
  rw [this]; exact P.posSemidef_conjTranspose_mul_self

/-- A nonzero orthogonal projection has nonzero trace. -/
private lemma trace_ne_zero_of_proj_ne_zero'
    {P : Mat} (hP : IsOrthogonalProjection P) (hP_ne : P ≠ 0) :
    Matrix.trace P ≠ 0 := by
  intro htr
  exact hP_ne ((orthogonalProjection_posSemidef' hP).trace_eq_zero_iff.1 htr)

/-- `P / tr(P)` is a density matrix. -/
private lemma normalizedProj_mem_densityMatrices'
    {P : Mat} (hP : IsOrthogonalProjection P) (hP_ne : P ≠ 0) :
    ((trace P)⁻¹ • P) ∈ densityMatrices D := by
  have hP_psd := orthogonalProjection_posSemidef' hP
  have htrP_ne := trace_ne_zero_of_proj_ne_zero' hP hP_ne
  exact ⟨hP_psd.smul (inv_nonneg_of_nonneg hP_psd.trace_nonneg),
    by simp [Matrix.trace_smul, htrP_ne]⟩

/-- `P * (P/tr(P)) * P = P/tr(P)` (the normalized projection is in `PMP`). -/
private lemma normalizedProj_in_PMP'
    {P : Mat} (hP : IsOrthogonalProjection P) :
    P * ((trace P)⁻¹ • P) * P = (trace P)⁻¹ • P := by
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  rw [hP.2, hP.2]

/-- `D > 0` if there exists a nontrivial projection in `M_D(ℂ)`. -/
private lemma pos_dim_of_nontrivialProjection
    {P : Mat} (hP_nt : IsNontrivialProjection P) : 0 < D := by
  by_contra hD_le
  push_neg at hD_le
  interval_cases D
  exact hP_nt.2.1 (Subsingleton.elim P 0)

/-- Adapted Cesàro argument: a channel preserving `PMP` has a fixed density
matrix in `PMP`. -/
private theorem channel_fixedPoint_in_PMP
    {E : Mat →ₗ[ℂ] Mat} {P : Mat}
    (hP : IsOrthogonalProjection P) (hP_ne : P ≠ 0)
    (hE : IsChannel E)
    (hE_pres : ∀ X : Mat,
      P * E (P * X * P) * P = E (P * X * P)) :
    ∃ ρ : Mat, ρ ∈ densityMatrices D ∧
      P * ρ * P = ρ ∧ E ρ = ρ := by
  -- Set up initial state
  set σ₀ := (trace P)⁻¹ • P with hσ₀_def
  have hσ₀_mem : σ₀ ∈ densityMatrices D := normalizedProj_mem_densityMatrices' hP hP_ne
  have hσ₀_PMP : P * σ₀ * P = σ₀ := normalizedProj_in_PMP' hP
  -- Iterates stay in PMP ∩ DM
  have h_iter_mem : ∀ n : ℕ, (E ^ n) σ₀ ∈ densityMatrices D := by
    intro n; induction n with
    | zero => simpa [pow_zero]
    | succ n ih =>
      rw [pow_succ']; change E ((E ^ n) σ₀) ∈ densityMatrices D
      exact IsChannel.map_densityMatrices E hE _ ih
  have h_iter_PMP : ∀ n : ℕ, P * (E ^ n) σ₀ * P = (E ^ n) σ₀ := by
    intro n; induction n with
    | zero => simpa [pow_zero]
    | succ n ih =>
      rw [pow_succ']; change P * E ((E ^ n) σ₀) * P = E ((E ^ n) σ₀)
      rw [← ih]; exact hE_pres _
  -- Cesàro means
  set σ : ℕ → Mat := fun N => cesaroMean E σ₀ (N + 1)
  -- Cesàro means are density matrices
  have hσ_dm : ∀ N, σ N ∈ densityMatrices D := by
    intro N
    refine ⟨?_, ?_⟩
    · change cesaroMean E σ₀ (N + 1) |>.PosSemidef
      rw [cesaroMean_eq]
      exact (Matrix.posSemidef_sum _ fun n _ => (h_iter_mem n).1).smul
        (by rw [one_div]; exact_mod_cast inv_nonneg_of_nonneg (Nat.cast_nonneg' (N + 1)))
    · change (cesaroMean E σ₀ (N + 1)).trace = 1
      rw [cesaroMean_eq, trace_smul, trace_sum,
        Finset.sum_congr rfl (fun n _ => (h_iter_mem n).2),
        Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, one_div]
      exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (by omega))
  -- Cesàro means are in PMP
  have hσ_PMP : ∀ N, P * σ N * P = σ N := by
    intro N
    change P * cesaroMean E σ₀ (N + 1) * P = cesaroMean E σ₀ (N + 1)
    rw [cesaroMean_eq]
    simp only [Matrix.mul_smul, Matrix.smul_mul, mul_sum, Finset.sum_mul]
    refine congrArg ((1 / ↑(N + 1 : ℕ) : ℂ) • ·) ?_
    exact Finset.sum_congr rfl (fun n _ => h_iter_PMP n)
  -- Extract convergent subsequence
  haveI : FirstCountableTopology Mat := @UniformSpace.firstCountableTopology _ _ inferInstance
  obtain ⟨ρ, hρ_mem, φ, hφ_mono, hφ_tendsto⟩ :=
    densityMatrices_isCompact.tendsto_subseq hσ_dm
  -- ρ is in PMP (limit of PMP elements, PMP is closed)
  have hρ_PMP : P * ρ * P = ρ := by
    have hcont : Continuous (fun X : Mat => P * X * P) :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact tendsto_nhds_unique
      (hcont.continuousAt.tendsto.comp hφ_tendsto |>.congr
        (fun n => hσ_PMP (φ n)))
      hφ_tendsto
  -- Show E(ρ) = ρ by telescoping
  have hE_cont : Continuous E := LinearMap.continuous_of_finiteDimensional E
  have h_Eσ : Filter.Tendsto (E ∘ σ ∘ φ) Filter.atTop (nhds (E ρ)) :=
    (hE_cont.tendsto ρ).comp hφ_tendsto
  have h_diff : Filter.Tendsto (fun k => (E ∘ σ ∘ φ) k - (σ ∘ φ) k)
      Filter.atTop (nhds (E ρ - ρ)) :=
    h_Eσ.sub hφ_tendsto
  have h_telesc : ∀ k, (E ∘ σ ∘ φ) k - (σ ∘ φ) k =
      (1 / ((φ k + 1 : ℕ) : ℂ)) • ((E ^ (φ k + 1)) σ₀ - σ₀) :=
    fun k => cesaroMean_telescope E σ₀ (φ k + 1) (Nat.succ_pos _)
  have h_rhs_zero : Filter.Tendsto (fun k => (1 / ((φ k + 1 : ℕ) : ℂ)) •
      ((E ^ (φ k + 1)) σ₀ - σ₀)) Filter.atTop (nhds 0) := by
    change Filter.Tendsto
      ((fun k => (1 / ((φ k + 1 : ℕ) : ℂ))) • (fun k => (E ^ (φ k + 1)) σ₀ - σ₀))
      Filter.atTop (nhds 0)
    apply NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded
    · simp_rw [one_div]
      have h_succ_tendsto : Filter.Tendsto (fun k => φ k + 1) Filter.atTop Filter.atTop := by
        apply Filter.tendsto_atTop_atTop_of_monotone
        · intro a b hab; exact Nat.add_le_add_right (hφ_mono.monotone hab) 1
        · intro b; exact ⟨b, Nat.le_succ_of_le (hφ_mono.id_le b)⟩
      exact (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)).comp h_succ_tendsto
    · have hbdd := densityMatrices_isCompact (D := D) |>.isBounded
      rw [Metric.isBounded_iff_subset_ball 0] at hbdd
      obtain ⟨R, hR⟩ := hbdd
      apply Filter.isBoundedUnder_of
      refine ⟨R + R, fun k => ?_⟩
      have h1 := hR (h_iter_mem (φ k + 1))
      have h2 := hR hσ₀_mem
      rw [Metric.mem_ball, dist_zero_right] at h1 h2
      exact le_trans (norm_sub_le _ _) (by linarith)
  have hρ_fix : E ρ = ρ :=
    sub_eq_zero.mp (tendsto_nhds_unique (h_diff.congr h_telesc) h_rhs_zero)
  exact ⟨ρ, hρ_mem, hρ_PMP, hρ_fix⟩

/-- Taylor remainder bound: `‖exp(x) - 1 - x‖ ≤ ‖x‖² · exp(‖x‖)` for normed algebras. -/
private theorem norm_exp_sub_one_sub_self_le'
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    [NormOneClass A] (x : A) :
    ‖NormedSpace.exp x - 1 - x‖ ≤ ‖x‖ ^ 2 * Real.exp ‖x‖ := by
  have hsum : HasSum (fun n : ℕ => ((Nat.factorial n : ℂ)⁻¹) • x ^ n)
      (NormedSpace.exp x) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) x
  have htail := (hasSum_nat_add_iff' 2).2 hsum
  have htail_eq : NormedSpace.exp x - 1 - x =
      ∑' n : ℕ, ((Nat.factorial (n + 2) : ℂ)⁻¹) • x ^ (n + 2) := by
    have := htail.tsum_eq
    simpa [Finset.sum_range_succ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      this.symm
  rw [htail_eq]
  have hsummable_tail : Summable (fun n : ℕ =>
      ‖((Nat.factorial (n + 2) : ℂ)⁻¹) • x ^ (n + 2)‖) := by
    exact (summable_nat_add_iff 2).2
      (by simpa using NormedSpace.norm_expSeries_summable' (𝕂 := ℂ) x)
  have hsummable_cmp : Summable (fun n : ℕ => ‖x‖ ^ 2 * (‖x‖ ^ n / Nat.factorial n)) :=
    (Real.summable_pow_div_factorial ‖x‖).mul_left (‖x‖ ^ 2)
  have hterm : ∀ n : ℕ,
      ‖((Nat.factorial (n + 2) : ℂ)⁻¹) • x ^ (n + 2)‖ ≤
        ‖x‖ ^ 2 * (‖x‖ ^ n / Nat.factorial n) := by
    intro n
    calc ‖((Nat.factorial (n + 2) : ℂ)⁻¹) • x ^ (n + 2)‖
        = ‖((Nat.factorial (n + 2) : ℂ)⁻¹)‖ * ‖x ^ (n + 2)‖ := norm_smul _ _
      _ ≤ ‖((Nat.factorial (n + 2) : ℂ)⁻¹)‖ * ‖x‖ ^ (n + 2) := by gcongr; exact norm_pow_le _ _
      _ = ‖x‖ ^ (n + 2) / Nat.factorial (n + 2) := by simp [div_eq_mul_inv, mul_comm]
      _ ≤ ‖x‖ ^ (n + 2) / Nat.factorial n := by
            exact div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg x) _) (by positivity)
              (by exact_mod_cast Nat.factorial_le (by omega))
      _ = ‖x‖ ^ 2 * (‖x‖ ^ n / Nat.factorial n) := by rw [pow_add, div_eq_mul_inv]; ring
  calc ‖∑' n, ((Nat.factorial (n + 2) : ℂ)⁻¹) • x ^ (n + 2)‖
      ≤ ∑' n, ‖((Nat.factorial (n + 2) : ℂ)⁻¹) • x ^ (n + 2)‖ :=
        norm_tsum_le_tsum_norm hsummable_tail
    _ ≤ ∑' n, ‖x‖ ^ 2 * (‖x‖ ^ n / Nat.factorial n) :=
        Summable.tsum_le_tsum hterm hsummable_tail hsummable_cmp
    _ = ‖x‖ ^ 2 * ∑' n, ‖x‖ ^ n / Nat.factorial n := by
        rw [tsum_mul_left]
    _ = ‖x‖ ^ 2 * Real.exp ‖x‖ := by
        rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

private axiom norm_expSemigroupCLM_taylor_bound [NeZero D]
    (E : (Mat →L[ℂ] Mat)) {s : ℝ} (hs : 0 ≤ s) :
    ‖expSemigroupCLM E s - (1 + (s : ℂ) • E)‖ ≤
      s ^ 2 * ‖E‖ ^ 2 * Real.exp (s * ‖E‖)

private axiom smul_clm_eq_neg_taylor_of_fixed_point
    [NeZero D]
    (E : Mat →L[ℂ] Mat) {ρ : Mat} {s : ℝ}
    (hfix : expSemigroupCLM E s ρ = ρ) :
    s • E ρ = -(((expSemigroupCLM E s) - 1 - (s : ℂ) • E) ρ)

private axiom norm_smul_clm_of_fixed_point_le
    [NeZero D]
    (E : Mat →L[ℂ] Mat) {ρ : Mat} {s : ℝ}
    (hs : 0 ≤ s)
    (hfix : expSemigroupCLM E s ρ = ρ) :
    ‖s • E ρ‖ ≤ s ^ 2 * ‖E‖ ^ 2 * Real.exp (s * ‖E‖) * ‖ρ‖

private axiom generator_norm_bound_of_fixed_point
    [NeZero D]
    {L : Mat →ₗ[ℂ] Mat} {ρ : Mat} {s : ℝ}
    (hs_pos : 0 < s)
    (hfix : expSemigroup L s ρ = ρ) :
    ‖L ρ‖ ≤ s * ‖endCLMEquiv' (D := D) L‖ ^ 2 * Real.exp (s * ‖endCLMEquiv' (D := D) L‖) * ‖ρ‖

private axiom clm_uniform_bound_of_fixed_point
    [NeZero D]
    (E : Mat →L[ℂ] Mat) {ρ : Mat} {s R : ℝ}
    (hs_pos : 0 < s)
    (hs_le : s ≤ 1)
    (hfix : expSemigroupCLM E s ρ = ρ)
    (hρ_bound : ‖ρ‖ ≤ R) :
    ‖E ρ‖ ≤ s * ‖E‖ ^ 2 * Real.exp ‖E‖ * R

private theorem density_subseq_norm_bounded
    [NeZero D]
    (ρ_shift : ℕ → Mat)
    (hρ_mem : ∀ n, ρ_shift n ∈ densityMatrices D)
    {φ : ℕ → ℕ} :
    ∃ R : ℝ, ∀ n, ‖ρ_shift (φ n)‖ ≤ R := by
  have hbdd := densityMatrices_isCompact (D := D) |>.isBounded
  rw [Metric.isBounded_iff_subset_ball 0] at hbdd
  obtain ⟨R, hR⟩ := hbdd
  refine ⟨R, ?_⟩
  intro n
  have h_mem := hR (hρ_mem (φ n))
  rw [Metric.mem_ball, dist_zero_right] at h_mem
  exact le_of_lt h_mem

private theorem one_div_subseq_tendsto_zero
    {φ : ℕ → ℕ}
    (hφ_mono : StrictMono φ) :
    Filter.Tendsto (fun n => (1 / (φ n + 1 : ℝ))) Filter.atTop (nhds 0) := by
  have hφ_tendsto_atTop : Filter.Tendsto φ Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_atTop_of_monotone
    · intro a b hab
      exact hφ_mono.monotone hab
    · intro b
      exact ⟨b, hφ_mono.id_le b⟩
  exact (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ_tendsto_atTop

private theorem scaled_one_div_subseq_tendsto_zero
    {φ : ℕ → ℕ}
    (hφ_mono : StrictMono φ)
    (C : ℝ) :
    Filter.Tendsto (fun n => (1 / (φ n + 1 : ℝ)) * C) Filter.atTop (nhds 0) := by
  have := (one_div_subseq_tendsto_zero hφ_mono).mul_const C
  simpa [mul_assoc] using this

private theorem generator_norm_bound_of_fixed_point_recip
    [NeZero D]
    {L : Mat →ₗ[ℂ] Mat} {ρ : Mat} {m : ℕ} {R : ℝ}
    (hm_pos : 0 < m)
    (hfix : expSemigroup L (1 / (m : ℝ)) ρ = ρ)
    (hρ_bound : ‖ρ‖ ≤ R) :
    ‖L ρ‖ ≤ (1 / (m : ℝ)) * ‖endCLMEquiv' (D := D) L‖ ^ 2 *
      Real.exp ‖endCLMEquiv' (D := D) L‖ * R := by
  set E := endCLMEquiv' (D := D) L
  set s := 1 / (m : ℝ) with hs_def
  have hm_ge_one : (1 : ℝ) ≤ m := by exact_mod_cast hm_pos
  have hs_le : s ≤ 1 := by
    rw [hs_def]
    exact div_le_one_of_le₀ hm_ge_one (by linarith)
  have hs_pos : 0 < s := by
    rw [hs_def]
    positivity
  have hfp : expSemigroupCLM E s ρ = ρ := hfix
  calc
    ‖L ρ‖ = ‖E ρ‖ := by rfl
    _ ≤ s * ‖E‖ ^ 2 * Real.exp ‖E‖ * R :=
        clm_uniform_bound_of_fixed_point
          (D := D) E hs_pos hs_le hfp hρ_bound
    _ = (1 / (m : ℝ)) * ‖E‖ ^ 2 * Real.exp ‖E‖ * R := by
        simp [hs_def, mul_assoc, mul_comm]

private theorem generator_subseq_norm_bound_of_fixed_points
    [NeZero D]
    {L : Mat →ₗ[ℂ] Mat}
    (ρ_shift : ℕ → Mat)
    (hρ_fix : ∀ n,
      expSemigroup L (1 / ((n + 1 : ℕ) : ℝ)) (ρ_shift n) = ρ_shift n)
    {φ : ℕ → ℕ}
    (R : ℝ)
  (hρ_norm : ∀ n, ‖ρ_shift (φ n)‖ ≤ R) :
    ∀ n, ‖L (ρ_shift (φ n))‖ ≤
      (1 / (φ n + 1 : ℝ)) * ‖endCLMEquiv' (D := D) L‖ ^ 2 *
        Real.exp ‖endCLMEquiv' (D := D) L‖ * R := by
  intro n
  simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using
    (generator_norm_bound_of_fixed_point_recip
      (D := D) (m := φ n + 1) (R := R) (Nat.succ_pos _) (hρ_fix (φ n)) (hρ_norm n))

private theorem generator_subseq_tendsto_zero_of_bounded_fixed_points
    [NeZero D]
    {L : Mat →ₗ[ℂ] Mat}
    (ρ_shift : ℕ → Mat)
    (hρ_fix : ∀ n,
      expSemigroup L (1 / ((n + 1 : ℕ) : ℝ)) (ρ_shift n) = ρ_shift n)
    {φ : ℕ → ℕ}
    (hφ_mono : StrictMono φ)
    (R : ℝ)
    (hρ_norm : ∀ n, ‖ρ_shift (φ n)‖ ≤ R) :
    Filter.Tendsto (fun n => L (ρ_shift (φ n))) Filter.atTop (nhds 0) := by
  set E := endCLMEquiv' (D := D) L
  have hL_bound : ∀ n, ‖L (ρ_shift (φ n))‖ ≤
      (1 / (φ n + 1 : ℝ)) * ‖E‖ ^ 2 * Real.exp (‖E‖) * R :=
    generator_subseq_norm_bound_of_fixed_points
      (D := D) (L := L) ρ_shift hρ_fix R hρ_norm
  have h_bound_tends : Filter.Tendsto
      (fun n => (1 / (φ n + 1 : ℝ)) * ‖E‖ ^ 2 * Real.exp ‖E‖ * R)
      Filter.atTop (nhds 0) := by
    simpa [mul_assoc] using
      scaled_one_div_subseq_tendsto_zero hφ_mono (‖E‖ ^ 2 * (Real.exp ‖E‖ * R))
  exact squeeze_zero_norm hL_bound h_bound_tends

private theorem generator_subseq_tendsto_zero_of_fixed_points
    [NeZero D]
    {L : Mat →ₗ[ℂ] Mat}
    (ρ_shift : ℕ → Mat)
    (hρ_mem : ∀ n, ρ_shift n ∈ densityMatrices D)
    (hρ_fix : ∀ n,
      expSemigroup L (1 / ((n + 1 : ℕ) : ℝ)) (ρ_shift n) = ρ_shift n)
    {φ : ℕ → ℕ}
    (hφ_mono : StrictMono φ) :
    Filter.Tendsto (fun n => L (ρ_shift (φ n))) Filter.atTop (nhds 0) := by
  obtain ⟨R, hρ_norm⟩ := density_subseq_norm_bounded (D := D) ρ_shift hρ_mem
  exact generator_subseq_tendsto_zero_of_bounded_fixed_points
    (D := D) (L := L) ρ_shift hρ_fix hφ_mono R hρ_norm

private theorem eq_zero_of_tendsto_linear_subseq
    {L : Mat →ₗ[ℂ] Mat}
    {ρ_shift : ℕ → Mat} {ρ : Mat} {φ : ℕ → ℕ}
    (hφ_tendsto : Filter.Tendsto (fun n => ρ_shift (φ n)) Filter.atTop (nhds ρ))
    (h_to_zero : Filter.Tendsto (fun n => L (ρ_shift (φ n))) Filter.atTop (nhds 0)) :
    L ρ = 0 := by
  have hL_cont : Continuous L := LinearMap.continuous_of_finiteDimensional L
  have hL_tends : Filter.Tendsto (fun n => L (ρ_shift (φ n)))
      Filter.atTop (nhds (L ρ)) :=
    (hL_cont.tendsto ρ).comp hφ_tendsto
  exact tendsto_nhds_unique hL_tends h_to_zero

private theorem generator_zero_of_subseq_fixed_points
    [NeZero D]
    {L : Mat →ₗ[ℂ] Mat}
    (ρ_shift : ℕ → Mat)
    (hρ_mem : ∀ n, ρ_shift n ∈ densityMatrices D)
    (hρ_fix : ∀ n,
      expSemigroup L (1 / ((n + 1 : ℕ) : ℝ)) (ρ_shift n) = ρ_shift n)
    {ρ : Mat} {φ : ℕ → ℕ}
    (hφ_mono : StrictMono φ)
    (hφ_tendsto : Filter.Tendsto (fun n => ρ_shift (φ n)) Filter.atTop (nhds ρ)) :
    L ρ = 0 := by
  have h_to_zero : Filter.Tendsto (fun n => L (ρ_shift (φ n)))
      Filter.atTop (nhds 0) :=
    generator_subseq_tendsto_zero_of_fixed_points
      (D := D) ρ_shift hρ_mem hρ_fix hφ_mono
  exact eq_zero_of_tendsto_linear_subseq hφ_tendsto h_to_zero

private theorem exists_fixed_point_sequence_in_PMP
    [NeZero D]
    {L : Mat →ₗ[ℂ] Mat} {P : Mat}
    (hP : IsOrthogonalProjection P) (hP_ne : P ≠ 0)
    (hGKSL : IsGKSLGenerator L)
    (hT_pres : ∀ t : ℝ, 0 ≤ t → ∀ X : Mat,
      P * (expSemigroup L t (P * X * P)) * P = expSemigroup L t (P * X * P)) :
    ∃ ρ_shift : ℕ → Mat,
      (∀ n, ρ_shift n ∈ densityMatrices D) ∧
      (∀ n, P * ρ_shift n * P = ρ_shift n) ∧
      (∀ n, expSemigroup L (1 / ((n + 1 : ℕ) : ℝ)) (ρ_shift n) = ρ_shift n) := by
  have h_fix : ∀ m : ℕ, 0 < m → ∃ ρ : Mat,
      ρ ∈ densityMatrices D ∧ P * ρ * P = ρ ∧
      expSemigroup L (1 / (m : ℝ)) ρ = ρ := by
    intro m hm
    exact channel_fixedPoint_in_PMP hP hP_ne (hGKSL _ (by positivity))
      (fun X => hT_pres _ (by positivity) X)
  refine ⟨fun n => (h_fix (n + 1) (Nat.succ_pos n)).choose, ?_, ?_, ?_⟩
  · intro n
    exact (h_fix (n + 1) (Nat.succ_pos n)).choose_spec.1
  · intro n
    exact (h_fix (n + 1) (Nat.succ_pos n)).choose_spec.2.1
  · intro n
    exact (h_fix (n + 1) (Nat.succ_pos n)).choose_spec.2.2

private theorem compression_eq_limit_of_tendsto
    {P ρ : Mat} {ρ_shift : ℕ → Mat} {φ : ℕ → ℕ}
    (hρ_PMP : ∀ n, P * ρ_shift n * P = ρ_shift n)
    (hφ_tendsto : Filter.Tendsto (fun n => ρ_shift (φ n)) Filter.atTop (nhds ρ)) :
    P * ρ * P = ρ := by
  have hcont : Continuous (fun X : Mat => P * X * P) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  exact tendsto_nhds_unique
    (hcont.continuousAt.tendsto.comp hφ_tendsto |>.congr
      (fun n => hρ_PMP (φ n)))
    hφ_tendsto

/-- **Wolf Proposition 7.6, (4) → (2)**: Given block-upper-triangular Lindblad
operators, the compressed channel has a fixed density matrix, giving (2). -/
axiom hasRankDeficientKernelElement_of_hasBlockUpperTriangularLindblad
    {L : Mat →ₗ[ℂ] Mat}
    (hGKSL : IsGKSLGenerator L)
    (h : HasBlockUpperTriangularLindblad L) :
    HasRankDeficientKernelElement L

end -- noncomputable section
