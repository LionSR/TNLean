import MPSLean.PiAlgebra.BlockSeparation

open scoped Matrix BigOperators


namespace MPSTensor

/-- A 1×1 matrix with entry `z`. -/
def mat1 (z : ℂ) : Matrix (Fin 1) (Fin 1) ℂ := fun _ _ => z

@[simp] lemma mat1_apply (z : ℂ) (i j : Fin 1) : mat1 z i j = z := rfl

-- A concrete counterexample showing the statement of `block_powsum_separation` (as currently
-- stated in `PiAlgebra/BlockSeparation.lean`) cannot be true in this generality.
--
-- We take `r = 2`, `d = 1`, and 1-dimensional blocks. Then `mpv` depends only on the length `N`.
-- We can arrange cancellation in the weighted sum without having per-block equality.
section

/-! ### Basic calculations for `mat1` -/

@[simp] lemma mat1_add (a b : ℂ) : mat1 (a + b) = mat1 a + mat1 b := by
  ext i j; simp [mat1]

@[simp] lemma mat1_smul (c a : ℂ) : mat1 (c • a) = c • mat1 a := by
  ext i j; simp [mat1]

@[simp] lemma mat1_mul (a b : ℂ) : mat1 a * mat1 b = mat1 (a * b) := by
  ext i j
  -- `Fin 1` has a unique element, so matrix multiplication is a 1-term sum.
  simp [mat1, Matrix.mul_apply]

@[simp] lemma mat1_one : mat1 (1 : ℂ) = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext i j
  -- There is only one index, so we're on the diagonal.
  have hi : i = 0 := Fin.eq_zero i
  have hj : j = 0 := Fin.eq_zero j
  subst hi; subst hj
  simp [mat1, Matrix.one_apply]

@[simp] lemma mat1_pow (a : ℂ) : ∀ n : ℕ, (mat1 a) ^ n = mat1 (a ^ n)
  | 0 => by
      simp [pow_zero, mat1_one]
  | n+1 => by
      simpa [pow_succ, mat1_mul, mat1_pow a n]

@[simp] lemma trace_mat1 (a : ℂ) : Matrix.trace (mat1 a) = a := by
  simpa [Matrix.trace_fin_one, mat1]

@[simp] lemma trace_mat1_pow (a : ℂ) (n : ℕ) : Matrix.trace ((mat1 a) ^ n) = a ^ n := by
  simp [mat1_pow, trace_mat1]

/-! ### The counterexample -/

/-- `μ` for the counterexample: `μ 0 = 1`, `μ 1 = 2`. -/
noncomputable def μEx : Fin 2 → ℂ
  | 0 => 1
  | 1 => 2

noncomputable def dimEx : Fin 2 → ℕ := fun _ => 1

/-- Blocks `A₀ = 1`, `A₁ = 3/2`. -/
noncomputable def AEx : (k : Fin 2) → MPSTensor 1 (dimEx k)
  | 0 => fun _ => mat1 1
  | 1 => fun _ => mat1 ((3 : ℂ) / 2)

/-- Blocks `B₀ = 3`, `B₁ = 1/2`. -/
noncomputable def BEx : (k : Fin 2) → MPSTensor 1 (dimEx k)
  | 0 => fun _ => mat1 3
  | 1 => fun _ => mat1 ((1 : ℂ) / 2)

lemma μEx_injective : Function.Injective μEx := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp [μEx] at hab ⊢

lemma μEx_ne_zero : ∀ k, μEx k ≠ 0 := by
  intro k; fin_cases k <;> simp [μEx]

/-- Each `AEx k` is injective in the sense `span (range _) = ⊤`.

This holds because for `D = 1` the matrix algebra is 1-dimensional and is spanned by any nonzero
matrix. -/
lemma span_mat1_eq_top (a : ℂ) (ha : a ≠ 0) : (ℂ ∙ mat1 a) = ⊤ := by
  -- Use the standard characterisation of the span of a singleton.
  refine (Submodule.span_singleton_eq_top_iff ℂ (mat1 a)).2 ?_
  intro v
  refine ⟨v 0 0 / a, ?_⟩
  ext i j
  have hi : i = 0 := Fin.eq_zero i
  have hj : j = 0 := Fin.eq_zero j
  subst hi; subst hj
  -- Now it’s a scalar identity.
  simp [mat1, div_eq_mul_inv, ha]

lemma AEx_isInjective : ∀ k, IsInjective (AEx k) := by
  classical
  intro k
  fin_cases k
  · -- k = 0
    -- Unfold the definition: range is a singleton containing `mat1 1`.
    simpa [MPSTensor.IsInjective, AEx, Set.range_const] using (span_mat1_eq_top (a := (1 : ℂ)) one_ne_zero)
  · -- k = 1
    -- Here `3/2 ≠ 0`.
    have hne : ( (3 : ℂ) / 2) ≠ 0 := by
      norm_num
    simpa [MPSTensor.IsInjective, AEx, Set.range_const] using (span_mat1_eq_top (a := ((3 : ℂ) / 2)) hne)

/-- The weighted MPV sum cancels for all system sizes (here `d = 1`, so there is only one σ at each
size). -/
lemma hδEx : ∀ N (σ : Fin N → Fin 1),
    ∑ k : Fin 2, (μEx k) ^ N • (mpv (AEx k) σ - mpv (BEx k) σ) = 0 := by
  classical
  intro N σ
  -- `Fin 1` is subsingleton, so `σ` is the constant-0 configuration.
  have hσ : σ = (fun _ => (0 : Fin 1)) := by
    funext i
    exact Fin.eq_zero (σ i)
  subst hσ
  -- Reduce MPVs to traces of powers.
  -- `mpv` for a constant configuration is `trace ((A i)^N)`.
  -- Rewrite MPVs as traces of powers.
  simp [AEx, BEx, μEx, MPSTensor.mpv_const_eq_trace_pow, smul_eq_mul]
  -- Reduce traces of `mat1` powers to scalar powers.
  simp [trace_mat1_pow, dimEx]
  -- Expand the remaining product.
  simp [mul_sub, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  -- Use `(a*b)^N = a^N*b^N` backwards to simplify the products of powers.
  have h23 : (2 : ℂ) ^ N * ((3 : ℂ) / 2) ^ N = (3 : ℂ) ^ N := by
    -- First rewrite `a^N*b^N` as `(a*b)^N`.
    have h : (2 : ℂ) ^ N * ((3 : ℂ) / 2) ^ N = ((2 : ℂ) * ((3 : ℂ) / 2)) ^ N :=
      (mul_pow (2 : ℂ) ((3 : ℂ) / 2) N).symm
    -- Then simplify the base.
    have hbase : (2 : ℂ) * ((3 : ℂ) / 2) = (3 : ℂ) := by
      norm_num
    simpa [hbase] using h
  -- (Not strictly needed, but kept for clarity: the same simplification gives `2^N*(1/2)^N = 1`.)
  have h21 : (2 : ℂ) ^ N * ((1 : ℂ) / 2) ^ N = (1 : ℂ) ^ N := by
    have h : (2 : ℂ) ^ N * ((1 : ℂ) / 2) ^ N = ((2 : ℂ) * ((1 : ℂ) / 2)) ^ N :=
      (mul_pow (2 : ℂ) ((1 : ℂ) / 2) N).symm
    have hbase : (2 : ℂ) * ((1 : ℂ) / 2) = (1 : ℂ) := by
      norm_num
    simpa [hbase] using h
  -- Finish the scalar identity.
  have h2ne : (2 : ℂ) ^ N ≠ 0 := by
    exact pow_ne_zero N (by norm_num)
  -- Expand the product and use `h23` plus `a * a⁻¹ = 1`.
  -- (We don't actually need `h21`; it was convenient to compute `2*(1/2)=1`.)
  simp [mul_add, mul_neg, h23, h2ne, mul_inv_cancel, add_assoc, add_left_comm, add_comm,
    sub_eq_add_neg, mul_assoc]

/-- The per-block MPVs are *not* equal: block 0 differs at `N = 1`. -/
lemma not_perBlock_sameMPV : ¬ (∀ k : Fin 2, SameMPV (AEx k) (BEx k)) := by
  intro h
  have h0 := h 0 1 (fun _ => (0 : Fin 1))
  -- Compute the two MPVs explicitly.
  -- For `N = 1`, `mpv` is just the trace of the single-site matrix.
  have h13 : (1 : ℂ) = 3 := by
    -- `N = 1` forces `trace(mat1 1) = trace(mat1 3)`, i.e. `1 = 3`.
    -- The left-hand side simplifies to the trace of the identity, i.e. `D = 1`.
    simpa [AEx, BEx, dimEx, MPSTensor.mpv_const_eq_trace_pow, trace_mat1_pow] using h0
  -- Contradiction.
  have : False := by
    norm_num at h13
  exact this

/-- Summary: there exist data satisfying the hypotheses of the naive separation statement, but not
its conclusion. -/
theorem counterexample_block_powsum_separation :
    (Function.Injective μEx) ∧ (∀ k, μEx k ≠ 0) ∧
    (∀ k, IsInjective (AEx k)) ∧
    (∀ N (σ : Fin N → Fin 1),
      ∑ k : Fin 2, (μEx k) ^ N • (mpv (AEx k) σ - mpv (BEx k) σ) = 0) ∧
    ¬ (∀ k : Fin 2, SameMPV (AEx k) (BEx k)) := by
  refine ⟨μEx_injective, μEx_ne_zero, AEx_isInjective, hδEx, not_perBlock_sameMPV⟩


end

end MPSTensor
