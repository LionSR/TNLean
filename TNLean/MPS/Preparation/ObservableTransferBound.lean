/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.Blocking
import TNLean.MPS.Preparation.CorrelatorFiniteSize

/-!
# Inserted transfer maps are bounded independently of the block length

For a tensor with `∑ (A^i)† A^i = 1` and an operator `X` on `m` consecutive sites, the
inserted transfer map `E_X(Z) = ∑_{σ,τ} X_{τσ} A^σ Z (A^τ)†` satisfies
`|E_X(e_{ce})_{ba}| ≤ ‖X‖` for all matrix units, with a bound that does not depend on `m`.
Indeed the entry is the inner product `⟨p, X q⟩` of the vectors `p_τ = A^τ_{ae}` and
`q_σ = A^σ_{bc}` of length `d^m`, and `∑_τ |A^τ_{ae}|² ≤ (∑_τ (A^τ)† A^τ)_{ee} = 1`.

This is the fact, used in the chapter's proof of `thm:ldp_depth_lower_bound` (the
chapter's version of arXiv:2307.01696, Theorem 1), that "in the gauge
(`eq:ldp_normal_gauge`) the maps `E_Z` have norm bounded by a multiple of `‖Z‖`
independent of the size of the support".

## Main results

* `norm_physicalObservableTransfer_single_apply_le`: the matrix-unit bound.
* `norm_toContinuousLinearMap_physicalObservableTransfer_le`: `‖E_X‖ ≤ D³ ‖X‖` for the
  `ℓ^∞` operator norm on `D × D` matrices.
-/

open scoped Matrix BigOperators InnerProductSpace Matrix.Norms.Operator

namespace MPSTensor

variable {d D : ℕ}

/-- For a left-canonical tensor, `∑_τ |(A^τ)_{ae}|² ≤ 1` over the words `τ` of length `m`:
the column `e` of the stacked words is a unit vector. This is the normalization of the
gauge `eq:ldp_normal_gauge` (arXiv:2307.01696, eq. (5)) used for the uniform bound on the
maps `E_Z` in the chapter's proof of `thm:ldp_depth_lower_bound`. -/
theorem sum_norm_sq_evalWord_apply_le {A : MPSTensor d D} (hA : ∑ i, (A i)ᴴ * A i = 1)
    (m : ℕ) (a e : Fin D) :
    ∑ τ : Fin m → Fin d, ‖Kraus.evalWord A (List.ofFn τ) a e‖ ^ 2 ≤ 1 := by
  have hW := congrFun (congrFun (sum_evalWord_conjTranspose_mul_evalWord A hA m) e) e
  rw [Matrix.sum_apply, Matrix.one_apply_eq] at hW
  have hre : ∑ τ : Fin m → Fin d, ∑ a' : Fin D,
      ‖Kraus.evalWord A (List.ofFn τ) a' e‖ ^ 2 = 1 := by
    have h := congrArg Complex.re hW
    rw [Complex.re_sum, Complex.one_re] at h
    rw [← h]
    refine Finset.sum_congr rfl fun τ _ ↦ ?_
    rw [Matrix.mul_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun a' _ ↦ ?_
    rw [Matrix.conjTranspose_apply, RCLike.star_def, mul_comm, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    norm_cast
  rw [← hre]
  refine Finset.sum_le_sum fun τ _ ↦ ?_
  exact Finset.single_le_sum (f := fun a' ↦ ‖Kraus.evalWord A (List.ofFn τ) a' e‖ ^ 2)
    (fun _ _ ↦ by positivity) (Finset.mem_univ a)

/-- The vector of entries `(A^τ)_{ae}` over the words `τ` of length `m` has norm at most
one. -/
theorem norm_toLp_evalWord_apply_le {A : MPSTensor d D} (hA : ∑ i, (A i)ᴴ * A i = 1)
    (m : ℕ) (a e : Fin D) :
    ‖WithLp.toLp 2 (fun τ : Fin m → Fin d ↦ Kraus.evalWord A (List.ofFn τ) a e)‖ ≤ 1 := by
  rw [EuclideanSpace.norm_eq]
  calc Real.sqrt (∑ τ : Fin m → Fin d, ‖Kraus.evalWord A (List.ofFn τ) a e‖ ^ 2)
      ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (sum_norm_sq_evalWord_apply_le hA m a e)
    _ = 1 := Real.sqrt_one

/-- **Uniform bound on inserted transfer maps.** For a left-canonical tensor and an
operator `X` on `m` sites, every entry of `E_X` applied to a matrix unit is at most the
operator norm of `X`, independently of `m`.

This is the step "in the gauge (`eq:ldp_normal_gauge`) the maps `E_Z` have norm bounded by
a multiple of `‖Z‖` independent of the size of the support" of the chapter's proof of
`thm:ldp_depth_lower_bound` (the chapter's version of arXiv:2307.01696, Theorem 1). -/
theorem norm_physicalObservableTransfer_single_apply_le {A : MPSTensor d D}
    (hA : ∑ i, (A i)ᴴ * A i = 1) (m : ℕ)
    (X : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ) (a b c e : Fin D) :
    ‖physicalObservableTransfer A m X (Matrix.single c e 1) b a‖ ≤
      ‖Matrix.toEuclideanCLM (n := Fin m → Fin d) (𝕜 := ℂ) X‖ := by
  classical
  set W : (Fin m → Fin d) → Matrix (Fin D) (Fin D) ℂ := fun σ ↦ Kraus.evalWord A (List.ofFn σ)
  set p : EuclideanSpace ℂ (Fin m → Fin d) := WithLp.toLp 2 fun τ ↦ W τ a e
  set q : EuclideanSpace ℂ (Fin m → Fin d) := WithLp.toLp 2 fun σ ↦ W σ b c
  have hmsm : ∀ M N : Matrix (Fin D) (Fin D) ℂ,
      (M * Matrix.single c e (1 : ℂ) * N : Matrix (Fin D) (Fin D) ℂ) b a = M b c * N e a := by
    intro M N
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_apply, Matrix.single_apply, mul_ite, mul_one, mul_zero, ite_and]
    simp [Finset.sum_ite_eq, ite_mul]
  have hentry : physicalObservableTransfer A m X (Matrix.single c e 1) b a =
      ⟪p, Matrix.toEuclideanCLM (n := Fin m → Fin d) (𝕜 := ℂ) X q⟫_ℂ := by
    rw [physicalObservableTransfer_apply, Matrix.sum_apply]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, hmsm,
      Matrix.conjTranspose_apply, RCLike.star_def]
    rw [PiLp.inner_apply]
    simp only [Matrix.toEuclideanCLM_toLp, Matrix.mulVec, dotProduct, p, q, W,
      RCLike.inner_apply, PiLp.toLp_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ ↦ ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    ring
  rw [hentry]
  calc ‖⟪p, Matrix.toEuclideanCLM (n := Fin m → Fin d) (𝕜 := ℂ) X q⟫_ℂ‖
      ≤ ‖p‖ * ‖Matrix.toEuclideanCLM (n := Fin m → Fin d) (𝕜 := ℂ) X q‖ :=
        norm_inner_le_norm _ _
    _ ≤ 1 * (‖Matrix.toEuclideanCLM (n := Fin m → Fin d) (𝕜 := ℂ) X‖ * 1) := by
        refine mul_le_mul (norm_toLp_evalWord_apply_le hA m a e) ?_ (norm_nonneg _) zero_le_one
        refine ((Matrix.toEuclideanCLM (n := Fin m → Fin d) (𝕜 := ℂ) X).le_opNorm q).trans ?_
        exact mul_le_mul_of_nonneg_left (norm_toLp_evalWord_apply_le hA m b c) (norm_nonneg _)
    _ = ‖Matrix.toEuclideanCLM (n := Fin m → Fin d) (𝕜 := ℂ) X‖ := by ring

/-- Entries of a matrix are bounded by its `ℓ^∞` operator norm. -/
theorem _root_.Matrix.norm_apply_le_linfty_opNorm (M : Matrix (Fin D) (Fin D) ℂ) (p q : Fin D) :
    ‖M p q‖ ≤ ‖M‖ := by
  rw [← coe_nnnorm, ← coe_nnnorm, NNReal.coe_le_coe, Matrix.linfty_opNNNorm_def]
  calc ‖M p q‖₊ ≤ ∑ j, ‖M p j‖₊ :=
        Finset.single_le_sum (f := fun j ↦ ‖M p j‖₊) (fun _ _ ↦ bot_le) (Finset.mem_univ q)
    _ ≤ Finset.univ.sup fun i ↦ ∑ j, ‖M i j‖₊ :=
        Finset.le_sup (f := fun i ↦ ∑ j, ‖M i j‖₊) (Finset.mem_univ p)

/-- The `ℓ^∞` operator norm of a matrix is at most `D` times a bound on its entries. -/
theorem _root_.Matrix.linfty_opNorm_le_of_forall_norm_apply_le {M : Matrix (Fin D) (Fin D) ℂ}
    {B : ℝ} (hB : 0 ≤ B) (h : ∀ p q, ‖M p q‖ ≤ B) : ‖M‖ ≤ D * B := by
  have hDB : 0 ≤ (D : ℝ) * B := by positivity
  have hrow : ∀ i, (∑ j, ‖M i j‖₊) ≤ Real.toNNReal (D * B) := fun i ↦ by
    rw [← NNReal.coe_le_coe, NNReal.coe_sum, Real.coe_toNNReal _ hDB]
    calc ∑ j, (‖M i j‖₊ : ℝ) ≤ ∑ _j : Fin D, B :=
          Finset.sum_le_sum fun j _ ↦ by rw [coe_nnnorm]; exact h i j
      _ = D * B := by simp
  have hsup : ‖M‖₊ ≤ Real.toNNReal (D * B) := by
    rw [Matrix.linfty_opNNNorm_def]
    exact Finset.sup_le fun i _ ↦ hrow i
  rw [← coe_nnnorm, ← Real.coe_toNNReal _ hDB]
  exact_mod_cast hsup

/-- **Uniform operator bound on inserted transfer maps.** For a left-canonical tensor and
an operator `X` on `m` sites, `‖E_X‖ ≤ D³ ‖X‖` for the `ℓ^∞` operator norm on `D × D`
matrices, independently of `m`.

This is the bound "in the gauge (`eq:ldp_normal_gauge`) the maps `E_Z` have norm bounded
by a multiple of `‖Z‖` independent of the size of the support" of the chapter's proof of
`thm:ldp_depth_lower_bound` (the chapter's version of arXiv:2307.01696, Theorem 1). -/
theorem norm_toContinuousLinearMap_physicalObservableTransfer_le {A : MPSTensor d D}
    (hA : ∑ i, (A i)ᴴ * A i = 1) (m : ℕ)
    (X : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ) :
    ‖Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)
        (physicalObservableTransfer A m X)‖ ≤
      (D : ℝ) ^ 3 * ‖Matrix.toEuclideanCLM (n := Fin m → Fin d) (𝕜 := ℂ) X‖ := by
  classical
  set x := ‖Matrix.toEuclideanCLM (n := Fin m → Fin d) (𝕜 := ℂ) X‖
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun Z ↦ ?_
  change ‖physicalObservableTransfer A m X Z‖ ≤ _
  have hZ : Z = ∑ c : Fin D, ∑ e : Fin D, Z c e • Matrix.single c e (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
    simp only [Matrix.smul_single, smul_eq_mul, mul_one]
  have hent : ∀ b a, ‖physicalObservableTransfer A m X Z b a‖ ≤ (D : ℝ) ^ 2 * x * ‖Z‖ := by
    intro b a
    conv_lhs => rw [hZ]
    rw [map_sum, Matrix.sum_apply]
    calc ‖∑ c, (physicalObservableTransfer A m X
            (∑ e, Z c e • Matrix.single c e (1 : ℂ))) b a‖
        ≤ ∑ _c : Fin D, ∑ _e : Fin D, ‖Z‖ * x := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ ↦ ?_)
          rw [map_sum, Matrix.sum_apply]
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun e _ ↦ ?_)
          rw [map_smul, Matrix.smul_apply, smul_eq_mul, norm_mul]
          exact mul_le_mul (Matrix.norm_apply_le_linfty_opNorm Z c e)
            (norm_physicalObservableTransfer_single_apply_le hA m X a b c e) (norm_nonneg _)
            (norm_nonneg _)
      _ = (D : ℝ) ^ 2 * x * ‖Z‖ := by simp; ring
  calc ‖physicalObservableTransfer A m X Z‖ ≤ D * ((D : ℝ) ^ 2 * x * ‖Z‖) :=
        Matrix.linfty_opNorm_le_of_forall_norm_apply_le (by positivity) hent
    _ = (D : ℝ) ^ 3 * x * ‖Z‖ := by ring

end MPSTensor
