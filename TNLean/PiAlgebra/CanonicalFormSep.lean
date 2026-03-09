/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.PiAlgebra.BlockSeparation
import TNLean.PiAlgebra.FundamentalTheoremComplete
import TNLean.Spectral.SpectralGap
import TNLean.Spectral.MPVOverlapDecay
import Mathlib.Analysis.Complex.Basic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.style.show false

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

/-! ### Normalization convention

In this file the legacy field/lemma name `ds_gauge` refers only to the **one-sided**
normalization
`∑ᵢ Aᵢ† Aᵢ = I`.
Equivalently, the associated transfer map is trace-preserving. We do **not** assume the separate
unital identity `∑ᵢ Aᵢ Aᵢ† = I`.
-/

/-! ### Canonical form predicate -/

structure IsCanonicalForm {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k)) : Prop where
  /-- Each block is algebraically injective (`span (range (A k)) = ⊤`). -/
  block_injective : ∀ k, IsInjective (A k)
  /-- Legacy name: `ds_gauge` stores only the one-sided trace-preserving / canonical
  normalization `∑ᵢ Aᵢ† Aᵢ = I`. -/
  ds_gauge : ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1
  /-- Strict ordering of the block weights by modulus. -/
  mu_strict_anti : StrictAnti (fun k : Fin r => ‖μ k‖)
  /-- No block weight vanishes. -/
  mu_ne_zero : ∀ k, μ k ≠ 0
  /-- **Aperiodicity / primitivity hypothesis** (literature-normalized): the MPV self-overlap
  converges to `1`.  This is used in `block_separation_core` to rule out the “overlap → 0”
  branch in the equal-or-orthogonal dichotomy.

  TODO: derive this from primitivity of the transfer map (peripheral spectrum = `{1}`), rather
  than assuming it. -/
  overlap_tendsto_one :
    ∀ k,
      Filter.Tendsto (fun N => mpvOverlap (d := d) (A k) (A k) N)
        Filter.atTop (nhds (1 : ℂ))

namespace IsCanonicalForm

variable {r : ℕ} {dim : Fin r → ℕ}
variable {μ : Fin r → ℂ} {A : (k : Fin r) → MPSTensor d (dim k)}

theorem mu_injective (hCF : IsCanonicalForm μ A) : Function.Injective μ := by
  intro j k hjk
  have h : ‖μ j‖ = ‖μ k‖ := by rw [hjk]
  exact hCF.mu_strict_anti.injective h

theorem mu_norm_injective (hCF : IsCanonicalForm μ A) :
    Function.Injective (fun k : Fin r => ‖μ k‖) :=
  hCF.mu_strict_anti.injective

/-- Alias emphasizing that the field `ds_gauge` is only the one-sided
trace-preserving normalization `∑ᵢ Aᵢ† Aᵢ = I`. -/
theorem tp_gauge (hCF : IsCanonicalForm μ A) :
    ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1 :=
  hCF.ds_gauge

/-- Preferred alias for `tp_gauge` using the project's left-canonical terminology. -/
theorem leftCanonical (hCF : IsCanonicalForm μ A) :
    ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1 :=
  hCF.tp_gauge

end IsCanonicalForm

/-! ### Auxiliary algebraic lemmas -/

section AlgebraicLemmas

lemma scalar_mul_sub_smul {n : Type*} [DecidableEq n] [Fintype n]
    (c z : ℂ) (M : Matrix n n ℂ) :
    Matrix.scalar n (c * z) - c • M = c • (Matrix.scalar n z - M) := by
  ext i j
  simp [Matrix.scalar, Matrix.smul_apply, Matrix.sub_apply, Matrix.diagonal_apply, smul_eq_mul]
  split <;> ring

lemma eval_charpoly_smul_mul {n : Type*} [DecidableEq n] [Fintype n]
    (c z : ℂ) (M : Matrix n n ℂ) :
    (c • M).charpoly.eval (c * z) = c ^ Fintype.card n * M.charpoly.eval z := by
  rw [Matrix.eval_charpoly, Matrix.eval_charpoly, scalar_mul_sub_smul, Matrix.det_smul]

theorem charpoly_eq_of_smul_charpoly_eq {n : Type*} [DecidableEq n] [Fintype n]
    (c : ℂ) (hc : c ≠ 0) (T U : Matrix n n ℂ)
    (h : (c • T).charpoly = (c • U).charpoly) :
    T.charpoly = U.charpoly := by
  have hcn : c ^ Fintype.card n ≠ 0 := pow_ne_zero _ hc
  apply Polynomial.funext
  intro z
  have h1 := eval_charpoly_smul_mul c z T
  have h2 := eval_charpoly_smul_mul c z U
  have h3 : (c • T).charpoly.eval (c * z) = (c • U).charpoly.eval (c * z) := by rw [h]
  rw [h1] at h3; rw [h2] at h3
  exact mul_left_cancel₀ hcn h3

theorem trace_eq_of_charpoly_eq
    {D : ℕ} [NeZero D]
    (T U : Matrix (Fin D) (Fin D) ℂ)
    (h : T.charpoly = U.charpoly) :
    Matrix.trace T = Matrix.trace U := by
  have : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp (NeZero.pos D)
  have hT := Matrix.trace_eq_neg_charpoly_coeff T
  have hU := Matrix.trace_eq_neg_charpoly_coeff U
  rw [hT, hU, h]

end AlgebraicLemmas

/-! ### MPV overlap bounds from one-sided canonical normalization

For the peeling argument in `block_separation_core` we need uniform (in the chain length) bounds on
MPV overlaps. The key input is the one-sided normalization
`∑ᵢ Aᵢ† Aᵢ = I` (stored under the legacy name `ds_gauge`), together with the iterated TP identity
`word_conjTranspose_mul_sum` and the elementary trace inequality
$|\mathrm{tr}(M)|^2 \le D\,\mathrm{tr}(M^\dagger M)$.
-/

open scoped InnerProductSpace

section OverlapBounds

variable {d : ℕ}

/-- Cauchy–Schwarz for complex sums, in a convenient squared form.

This is the same estimate as `MPSTensor.norm_sq_sum_mul_le` in `SpectralGap.lean`, but we keep a
local copy here to avoid depending on private lemmas. -/
private lemma norm_sq_sum_mul_le {ι : Type*} [Fintype ι] (a b : ι → ℂ) :
    ‖(∑ i : ι, a i * b i)‖ ^ 2 ≤ (∑ i : ι, ‖a i‖ ^ 2) * (∑ i : ι, ‖b i‖ ^ 2) := by
  classical
  -- Triangle inequality + Cauchy–Schwarz for real sequences of norms.
  have h :
      ‖(∑ i : ι, a i * b i)‖ ≤ ∑ i : ι, ‖a i‖ * ‖b i‖ := by
    -- `Fintype.sum` is definitionally a `Finset.univ` sum.
    simpa [norm_mul] using
      (norm_sum_le (s := (Finset.univ : Finset ι)) (f := fun i => a i * b i)).trans
        (Finset.sum_le_sum (fun i _ => by simp [norm_mul]))
  have hsq :
      ‖(∑ i : ι, a i * b i)‖ ^ 2 ≤ (∑ i : ι, ‖a i‖ * ‖b i‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h 2
  have hcs :
      (∑ i : ι, ‖a i‖ * ‖b i‖) ^ 2 ≤ (∑ i : ι, ‖a i‖ ^ 2) * (∑ i : ι, ‖b i‖ ^ 2) := by
    simpa using
      (Finset.sum_mul_sq_le_sq_mul_sq (s := (Finset.univ : Finset ι))
        (f := fun i => ‖a i‖) (g := fun i => ‖b i‖))
  exact hsq.trans hcs

/-- Trace inequality: $|\mathrm{tr}(M)|^2 \le D\,\mathrm{tr}(M^\dagger M)$. -/
private lemma norm_trace_sq_le_dim_mul_trace_conjTranspose_mul
    {D : ℕ} [NeZero D] (M : Matrix (Fin D) (Fin D) ℂ) :
    ‖Matrix.trace M‖ ^ 2 ≤ (D : ℝ) * (Matrix.trace (Mᴴ * M)).re := by
  classical
  -- Cauchy–Schwarz on the diagonal sum.
  have hCS :
      ‖(∑ i : Fin D, M i i)‖ ^ 2 ≤ (D : ℝ) * (∑ i : Fin D, ‖M i i‖ ^ 2) := by
    have h := norm_sq_sum_mul_le (a := fun _ : Fin D => (1 : ℂ)) (b := fun i => M i i)
    -- simplify the constant factor `∑ ‖1‖^2 = D`.
    simpa [Matrix.trace, norm_mul, one_mul, pow_two, Finset.sum_const, Finset.card_fin] using h
  -- Bound the diagonal square sum by the full Frobenius square sum.
  have hdiag :
      (∑ i : Fin D, ‖M i i‖ ^ 2) ≤ ∑ i : Fin D, ∑ j : Fin D, ‖M i j‖ ^ 2 := by
    have hper : ∀ i : Fin D, ‖M i i‖ ^ 2 ≤ ∑ j : Fin D, ‖M i j‖ ^ 2 := by
      intro i
      have hnonneg : ∀ j : Fin D, 0 ≤ ‖M i j‖ ^ 2 := fun _ => by positivity
      -- `‖M i i‖^2` is one term of the `j`-sum.
      -- Use the fact that a single term is bounded by the whole sum.
      have hsingle : ‖M i i‖ ^ 2 ≤ ∑ j : Fin D, ‖M i j‖ ^ 2 := by
        -- We specify `f` explicitly so Lean does not guess the wrong function.
        simpa using
          (Finset.single_le_sum (s := (Finset.univ : Finset (Fin D)))
            (f := fun j : Fin D => ‖M i j‖ ^ 2)
            (fun j _ => hnonneg j) (Finset.mem_univ i))
      exact hsingle
    exact Finset.sum_le_sum (fun i _ => hper i)
  -- Rewrite the Frobenius square sum as `trace(M†M).re`.
  have hfrob : (Matrix.trace (Mᴴ * M)).re = ∑ i : Fin D, ∑ j : Fin D, ‖M i j‖ ^ 2 := by
    simpa [MPSTensor.frobSq] using (MPSTensor.frobSq_eq_sum (D := D) M)
  -- Assemble.
  calc
    ‖Matrix.trace M‖ ^ 2
        = ‖(∑ i : Fin D, M i i)‖ ^ 2 := by simp [Matrix.trace]
    _ ≤ (D : ℝ) * (∑ i : Fin D, ‖M i i‖ ^ 2) := hCS
    _ ≤ (D : ℝ) * (∑ i : Fin D, ∑ j : Fin D, ‖M i j‖ ^ 2) := by
          gcongr
    _ = (D : ℝ) * (Matrix.trace (Mᴴ * M)).re := by simp [hfrob]

/-- Under the one-sided normalization `∑ᵢ Aᵢ† Aᵢ = I` (legacy name: `ds_gauge`),
the MPV self-overlap is uniformly bounded: `‖mpvOverlap A A N‖ ≤ D^2`. -/
lemma ds_gauge_mpvOverlap_self_bound
    {D : ℕ} [NeZero D]
    (A : MPSTensor d D)
    (hA_ds : ∑ i : Fin d, (A i)ᴴ * (A i) = 1)
    (N : ℕ) :
    ‖mpvOverlap (d := d) A A N‖ ≤ (D : ℝ) ^ 2 := by
  classical
  -- Let `Mσ` be the word-evaluation matrices.
  let M : (Fin N → Fin d) → Matrix (Fin D) (Fin D) ℂ :=
    fun σ => evalWord A (List.ofFn σ)
  -- Start from the overlap and bound it by the sum of squared traces.
  have h1 :
      ‖mpvOverlap (d := d) A A N‖ ≤ ∑ σ : Fin N → Fin d, ‖Matrix.trace (M σ)‖ ^ 2 := by
    simp only [mpvOverlap, MPSTensor.mpv, MPSTensor.coeff, M]
    -- Use the triangle inequality for the finite sum.
    simpa using
      (calc
        ‖∑ σ : Fin N → Fin d,
            Matrix.trace (evalWord A (List.ofFn σ)) *
              star (Matrix.trace (evalWord A (List.ofFn σ)))‖
            ≤ ∑ σ : Fin N → Fin d,
                ‖Matrix.trace (evalWord A (List.ofFn σ)) *
                  star (Matrix.trace (evalWord A (List.ofFn σ)))‖ :=
          norm_sum_le (s := (Finset.univ : Finset (Fin N → Fin d))) _
        _ = ∑ σ : Fin N → Fin d, ‖Matrix.trace (evalWord A (List.ofFn σ))‖ ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro σ _
          simp [norm_mul, norm_star, pow_two])
  -- Use the iterated TP condition.
  have hword :
      ∑ σ : Fin N → Fin d, (M σ)ᴴ * M σ = (1 : Matrix (Fin D) (Fin D) ℂ) := by
    simpa [M] using (word_conjTranspose_mul_sum (K := A) hA_ds N)
  -- Bound the RHS by `D^2`.
  have h2 : (∑ σ : Fin N → Fin d, ‖Matrix.trace (M σ)‖ ^ 2) ≤ (D : ℝ) ^ 2 := by
    -- Apply the trace inequality termwise, then use `hword`.
    have hterm :
        ∀ σ : Fin N → Fin d, ‖Matrix.trace (M σ)‖ ^ 2 ≤
          (D : ℝ) * (Matrix.trace ((M σ)ᴴ * M σ)).re := fun σ =>
        norm_trace_sq_le_dim_mul_trace_conjTranspose_mul (D := D) (M σ)
    have hsum :
        (∑ σ : Fin N → Fin d, ‖Matrix.trace (M σ)‖ ^ 2) ≤
          ∑ σ : Fin N → Fin d, (D : ℝ) * (Matrix.trace ((M σ)ᴴ * M σ)).re :=
      Finset.sum_le_sum (fun σ _ => hterm σ)
    -- Reassociate and compute the trace sum using `hword`.
    calc
      (∑ σ : Fin N → Fin d, ‖Matrix.trace (M σ)‖ ^ 2)
          ≤ ∑ σ : Fin N → Fin d, (D : ℝ) * (Matrix.trace ((M σ)ᴴ * M σ)).re := hsum
      _ = (D : ℝ) * ∑ σ : Fin N → Fin d, (Matrix.trace ((M σ)ᴴ * M σ)).re := by
            simp [Finset.mul_sum]
      _ = (D : ℝ) * (Matrix.trace (∑ σ : Fin N → Fin d, (M σ)ᴴ * M σ)).re := by
            -- Move `re` and `trace` outside the finite sum (as in `SpectralGap.sum_frobSq_words`).
            congr 1
            rw [← Complex.re_sum, ← Matrix.trace_sum]
      _ = (D : ℝ) * (Matrix.trace (1 : Matrix (Fin D) (Fin D) ℂ)).re := by
            simp [hword]
      _ = (D : ℝ) * (D : ℝ) := by
            simp [Matrix.trace_one, Fintype.card_fin]
      _ = (D : ℝ) ^ 2 := by ring
  exact h1.trans h2

/-- Under the one-sided normalization `∑ᵢ Aᵢ† Aᵢ = I` (legacy name: `ds_gauge`),
the MPV state has uniformly bounded norm: `‖mpvState A N‖ ≤ D`. -/
lemma ds_gauge_mpvState_norm_bound
    {D : ℕ} [NeZero D]
    (A : MPSTensor d D)
    (hA_ds : ∑ i : Fin d, (A i)ᴴ * (A i) = 1)
    (N : ℕ) :
    ‖mpvState (d := d) A N‖ ≤ (D : ℝ) := by
  classical
  have hself : ‖mpvOverlap (d := d) A A N‖ ≤ (D : ℝ) ^ 2 :=
    ds_gauge_mpvOverlap_self_bound (d := d) (A := A) hA_ds N
  have hEq : ‖mpvOverlap (d := d) A A N‖ = ‖mpvState (d := d) A N‖ ^ 2 := by
    -- `mpvOverlap = star (mpvInner)` and `⟪x,x⟫ = ‖x‖²`.
    -- The RHS is a nonnegative real number, so its complex norm is just an absolute value.
    simp [mpvOverlap_eq_star_mpvInner, mpvInner, inner_self_eq_norm_sq_to_K,
      RCLike.norm_ofReal, abs_of_nonneg (sq_nonneg (‖mpvState (d := d) A N‖))]
  have hsq : ‖mpvState (d := d) A N‖ ^ 2 ≤ (D : ℝ) ^ 2 := by
    simpa [hEq] using hself
  have hsqrt :
      Real.sqrt (‖mpvState (d := d) A N‖ ^ 2) ≤ Real.sqrt ((D : ℝ) ^ 2) :=
    Real.sqrt_le_sqrt hsq
  -- Simplify `√(x^2) = x` for nonnegative `x`.
  simpa [Real.sqrt_sq (norm_nonneg (mpvState (d := d) A N)),
    Real.sqrt_sq (Nat.cast_nonneg D)] using hsqrt

/-- Under the one-sided normalization `∑ᵢ Aᵢ† Aᵢ = I` (legacy name: `ds_gauge`),
MPV overlaps are uniformly bounded: `‖mpvOverlap A B N‖ ≤ D₁ · D₂`. -/
lemma ds_gauge_mpvOverlap_bound
    {D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA_ds : ∑ i : Fin d, (A i)ᴴ * (A i) = 1)
    (hB_ds : ∑ i : Fin d, (B i)ᴴ * (B i) = 1)
    (N : ℕ) :
    ‖mpvOverlap (d := d) A B N‖ ≤ (D₁ : ℝ) * (D₂ : ℝ) := by
  classical
  -- Convert to Lean's inner product, then apply Cauchy–Schwarz.
  have hCS : ‖mpvInner (d := d) A B N‖ ≤
      ‖mpvState (d := d) A N‖ * ‖mpvState (d := d) B N‖ :=
    norm_inner_le_norm (mpvState (d := d) A N) (mpvState (d := d) B N)
  -- `mpvOverlap = star (mpvInner)`.
  have hOverlap : ‖mpvOverlap (d := d) A B N‖ = ‖mpvInner (d := d) A B N‖ := by
    simp [mpvOverlap_eq_star_mpvInner]
  -- Apply the one-sided normalization bounds on each factor.
  have hA : ‖mpvState (d := d) A N‖ ≤ (D₁ : ℝ) := ds_gauge_mpvState_norm_bound (d := d) A hA_ds N
  have hB : ‖mpvState (d := d) B N‖ ≤ (D₂ : ℝ) := ds_gauge_mpvState_norm_bound (d := d) B hB_ds N
  calc
    ‖mpvOverlap (d := d) A B N‖ = ‖mpvInner (d := d) A B N‖ := hOverlap
    _ ≤ ‖mpvState (d := d) A N‖ * ‖mpvState (d := d) B N‖ := hCS
    _ ≤ (D₁ : ℝ) * (D₂ : ℝ) := by gcongr

end OverlapBounds


/-! ### One-sided canonical normalization implies trace bound

**Mathematical content**: Under the one-sided normalization
`∑_i A_i† A_i = I` (stored under the legacy name `ds_gauge`), the iterated TP condition
`word_conjTranspose_mul_sum` gives
`∑_σ (evalWord A (ofFn σ))† (evalWord A (ofFn σ)) = I`
for words of any length. Each term is PSD, so for any specific word `w`,
`(evalWord A w)† (evalWord A w) ≤ I`
(in the Loewner order). This means each diagonal entry satisfies ‖M_ii‖ ≤ 1,
giving |tr(M)| ≤ ∑ ‖M_ii‖ ≤ D. For `M = (evalWord A w)^L`, we use the
identity `(evalWord A w)^L = evalWord A (w ++ w ++ ... ++ w)`. -/

open scoped ComplexOrder

private lemma star_mul_self_re_eq' (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
  have : star z = starRingEnd ℂ z := rfl; rw [this, Complex.conj_mul']; norm_cast

private lemma star_mul_self_re_nonneg' (z : ℂ) : 0 ≤ (star z * z).re := by
  rw [star_mul_self_re_eq']; exact sq_nonneg _

/-- If ∑_σ (f σ)† (f σ) = I, then each diagonal entry of each f σ₀ has norm ≤ 1.
This follows from the PSD ordering: each (f σ₀)† (f σ₀) ≤ I. -/
private lemma norm_diag_le_one_from_sum_eq_one
    {D' : ℕ} {ι : Type*} [Fintype ι]
    (f : ι → Matrix (Fin D') (Fin D') ℂ)
    (hf : ∑ σ, (f σ)ᴴ * f σ = 1)
    (σ₀ : ι) (i : Fin D') :
    ‖f σ₀ i i‖ ≤ 1 := by
  classical
  -- 1 - M†M is PSD (sum of remaining PSD terms)
  have h_psd : (1 - (f σ₀)ᴴ * f σ₀).PosSemidef := by
    have hsub : 1 - (f σ₀)ᴴ * f σ₀ = ∑ σ ∈ Finset.univ.erase σ₀, (f σ)ᴴ * f σ := by
      rw [← hf, ← Finset.add_sum_erase _ _ (Finset.mem_univ σ₀), add_sub_cancel_left]
    rw [hsub]
    exact Matrix.posSemidef_sum _ (fun σ _ => Matrix.posSemidef_conjTranspose_mul_self (f σ))
  -- (M†M)_ii ≤ 1 via ComplexOrder
  have h_diag_nn : 0 ≤ (1 - (f σ₀)ᴴ * f σ₀) i i := h_psd.diag_nonneg
  rw [Matrix.sub_apply, Matrix.one_apply_eq] at h_diag_nn
  have h_le : ((f σ₀)ᴴ * f σ₀) i i ≤ 1 := sub_nonneg.mp h_diag_nn
  -- Extract real-part bound
  have h_re : (((f σ₀)ᴴ * f σ₀) i i).re ≤ 1 := by
    have := (Complex.le_def.mp h_le).1; simpa using this
  -- (M†M)_ii = ∑_j star(M_ji) * M_ji
  have h_expand : ((f σ₀)ᴴ * f σ₀) i i = ∑ j, star ((f σ₀) j i) * (f σ₀) j i := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  -- ‖M_ii‖² ≤ re(∑_j star(M_ji) * M_ji) = re((M†M)_ii) ≤ 1
  have h_sq : ‖f σ₀ i i‖ ^ 2 ≤ 1 := by
    have h1 : (star (f σ₀ i i) * f σ₀ i i).re ≤
        (∑ j : Fin D', star (f σ₀ j i) * f σ₀ j i).re := by
      simp only [Complex.re_sum]
      have : ∀ j : Fin D', j ∈ Finset.univ →
          0 ≤ (fun k => (star (f σ₀ k i) * f σ₀ k i).re) j :=
        fun j _ => star_mul_self_re_nonneg' (f σ₀ j i)
      exact Finset.single_le_sum this (Finset.mem_univ i)
    calc ‖f σ₀ i i‖ ^ 2
        = (star (f σ₀ i i) * f σ₀ i i).re := (star_mul_self_re_eq' _).symm
      _ ≤ (∑ j : Fin D', star (f σ₀ j i) * f σ₀ j i).re := h1
      _ = (((f σ₀)ᴴ * f σ₀) i i).re := by rw [h_expand]
      _ ≤ 1 := h_re
  rwa [← abs_of_nonneg (norm_nonneg _), ← sq_le_one_iff_abs_le_one]

/-- Under the one-sided normalization `∑ᵢ Aᵢ† Aᵢ = I` (legacy name: `ds_gauge`),
the trace of any power of any word evaluation is bounded by `D`.
Uses the iterated TP condition and PSD diagonal bounds. -/
lemma ds_gauge_evalWord_trace_bound
    {D : ℕ} [NeZero D]
    (A : MPSTensor d D)
    (hA_ds : ∑ i : Fin d, (A i)ᴴ * (A i) = 1)
    (w : List (Fin d)) (L : ℕ) :
    ‖Matrix.trace ((evalWord A w) ^ L)‖ ≤ (D : ℝ) := by
  -- (evalWord A w)^L = evalWord A ((replicate L w).flatten)
  set n := w.length * L
  rw [← evalWord_flatten_replicate A w L]
  set w' := (List.replicate L w).flatten
  have hlen : w'.length = n := by
    simp [w', n, List.length_flatten, List.map_replicate,
      List.sum_replicate, smul_eq_mul, mul_comm]
  -- Express w' as List.ofFn σ₀ for a specific σ₀
  set σ₀ : Fin n → Fin d := fun i => w'.get (Fin.cast hlen.symm i)
  have hofFn : List.ofFn σ₀ = w' := by
    conv_rhs => rw [← List.ofFn_getElem w']
    apply List.ofFn_congr (by omega)
  rw [← hofFn]
  -- word_conjTranspose_mul_sum: ∑_σ (evalWord A (ofFn σ))† (evalWord A (ofFn σ)) = I
  have h_sum := word_conjTranspose_mul_sum (fun i => A i) hA_ds n
  -- Each diagonal entry of evalWord A (ofFn σ₀) has norm ≤ 1
  have h_diag : ∀ i : Fin D, ‖evalWord A (List.ofFn σ₀) i i‖ ≤ 1 :=
    norm_diag_le_one_from_sum_eq_one
      (fun σ => evalWord A (List.ofFn σ)) h_sum σ₀
  -- ‖tr(M)‖ ≤ ∑_i ‖M_ii‖ ≤ ∑_i 1 = D
  calc ‖Matrix.trace (evalWord A (List.ofFn σ₀))‖
      ≤ ∑ i : Fin D, ‖evalWord A (List.ofFn σ₀) i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin D, (1 : ℝ) := Finset.sum_le_sum (fun i _ => h_diag i)
    _ = (D : ℝ) := by simp [Finset.sum_const, Finset.card_fin]

/-! ### Peeling lemma -/

section PeelingLemma

/-- **Peeling lemma**: Given a weighted sum ∑_k α_k^L · δ_k(L) = 0 where
the leading coefficient |α₀| strictly dominates the others (|α_k| ≤ |α₀|·ρ
for k ≠ 0 with ρ < 1), and all δ_k are uniformly bounded, then δ₀(L)
decays exponentially: |δ₀(L)| ≤ C · ρ^L.

This is the key technical tool for extracting per-block information from
the global identity. It works by isolating δ₀ from the sum and bounding
the remaining terms using the dominance gap. -/
theorem peeling_exponential_bound
    {r : ℕ} (hr : 0 < r)
    (α : Fin r → ℂ) (hα₀ : α ⟨0, hr⟩ ≠ 0)
    (δ : Fin r → ℕ → ℂ)
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hδ_bound : ∀ k L, ‖δ k L‖ ≤ B)
    (h_sum : ∀ L : ℕ, ∑ k : Fin r, (α k) ^ L * δ k L = 0)
    (ρ : ℝ) (hρ_pos : 0 < ρ) (hρ_lt : ρ < 1)
    (hρ_bound : ∀ k : Fin r, k ≠ ⟨0, hr⟩ → ‖α k‖ ≤ ‖α ⟨0, hr⟩‖ * ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℕ,
      ‖δ ⟨0, hr⟩ L‖ ≤ C * ρ ^ L := by
  set idx₀ : Fin r := ⟨0, hr⟩
  refine ⟨↑(r - 1) * B, mul_nonneg (Nat.cast_nonneg' _) hB_nn, ?_⟩
  intro L
  have h_eq := h_sum L
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ idx₀)] at h_eq
  have h_neg : (α idx₀) ^ L * δ idx₀ L =
      -(∑ k ∈ Finset.univ.erase idx₀, (α k) ^ L * δ k L) :=
    eq_neg_of_add_eq_zero_left h_eq
  have h_norm_eq : ‖(α idx₀) ^ L‖ * ‖δ idx₀ L‖ =
      ‖∑ k ∈ Finset.univ.erase idx₀, (α k) ^ L * δ k L‖ := by
    rw [← norm_mul, h_neg, norm_neg]
  have h_term_le : ∀ k ∈ Finset.univ.erase idx₀,
      ‖(α k) ^ L * δ k L‖ ≤ (‖α idx₀‖ * ρ) ^ L * B := by
    intro k hk
    rw [Finset.mem_erase] at hk
    rw [norm_mul, norm_pow]
    apply mul_le_mul
    · exact pow_le_pow_left₀ (norm_nonneg _) (hρ_bound k hk.1) L
    · exact hδ_bound k L
    · exact norm_nonneg _
    · exact pow_nonneg (mul_nonneg (norm_nonneg _) hρ_pos.le) L
  have h_erase_card : (Finset.univ.erase idx₀).card = r - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin]
  have h_sum_le : ‖∑ k ∈ Finset.univ.erase idx₀, (α k) ^ L * δ k L‖ ≤
      ↑(r - 1) * ((‖α idx₀‖ * ρ) ^ L * B) := by
    calc ‖∑ k ∈ Finset.univ.erase idx₀, (α k) ^ L * δ k L‖
        ≤ ∑ k ∈ Finset.univ.erase idx₀, ‖(α k) ^ L * δ k L‖ :=
          norm_sum_le (Finset.univ.erase idx₀) _
      _ ≤ ∑ _k ∈ Finset.univ.erase idx₀, ((‖α idx₀‖ * ρ) ^ L * B) :=
          Finset.sum_le_sum h_term_le
      _ = ↑(Finset.univ.erase idx₀).card * ((‖α idx₀‖ * ρ) ^ L * B) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ↑(r - 1) * ((‖α idx₀‖ * ρ) ^ L * B) := by rw [h_erase_card]
  have hα₀_pow_pos : (0 : ℝ) < ‖α idx₀‖ ^ L :=
    pow_pos (norm_pos_iff.mpr hα₀) L
  have h_chain : ‖α idx₀‖ ^ L * ‖δ idx₀ L‖ ≤
      ↑(r - 1) * ((‖α idx₀‖ * ρ) ^ L * B) := by
    calc ‖α idx₀‖ ^ L * ‖δ idx₀ L‖
        = ‖(α idx₀) ^ L‖ * ‖δ idx₀ L‖ := by rw [norm_pow]
      _ = ‖∑ k ∈ Finset.univ.erase idx₀, (α k) ^ L * δ k L‖ := h_norm_eq
      _ ≤ ↑(r - 1) * ((‖α idx₀‖ * ρ) ^ L * B) := h_sum_le
  rw [mul_pow] at h_chain
  have : ↑(r - 1) * (‖α idx₀‖ ^ L * ρ ^ L * B) =
      ‖α idx₀‖ ^ L * (↑(r - 1) * B * ρ ^ L) := by ring
  rw [this] at h_chain
  exact le_of_mul_le_mul_left h_chain hα₀_pow_pos

end PeelingLemma

section BlockSeparationCoreHelpers

private lemma eq_one_of_tendsto_pow_atTop_nhds_one (z : ℂ)
    (hz : Filter.Tendsto (fun N : ℕ => z ^ N) Filter.atTop (nhds (1 : ℂ))) :
    z = 1 := by
  have hz_shift :
      Filter.Tendsto (fun N : ℕ => z ^ (N + 1)) Filter.atTop (nhds (1 : ℂ)) :=
    (Filter.tendsto_add_atTop_iff_nat 1).2 hz
  have hz_mul : Filter.Tendsto (fun N : ℕ => z ^ (N + 1)) Filter.atTop (nhds z) := by
    have h := (Filter.Tendsto.mul_const (b := z) hz)
    simpa [pow_succ, mul_assoc] using h
  have huniq := tendsto_nhds_unique hz_shift hz_mul
  simpa [eq_comm] using huniq

private lemma gaugePhaseEquiv_of_mpvOverlap_tendsto_one
    {D : ℕ} [NeZero D] (A B : MPSTensor d D)
    (hA_inj : IsInjective A) (hB_inj : IsInjective B)
    (hA_ds : ∑ i : Fin d, (A i)ᴴ * (A i) = 1)
    (hB_ds : ∑ i : Fin d, (B i)ᴴ * (B i) = 1)
    (h : Filter.Tendsto (fun N => mpvOverlap (d := d) A B N) Filter.atTop (nhds (1 : ℂ))) :
    GaugePhaseEquiv A B := by
  by_contra hnot
  have hto0 :=
    mpvOverlap_tendsto_zero (A := A) (B := B) hA_inj hB_inj hA_ds hB_ds hnot
  have : (0 : ℂ) = 1 := tendsto_nhds_unique hto0 h
  exact zero_ne_one this

private lemma mpv_eq_pow_mul_of_gaugePhase
    {D : ℕ} (A B : MPSTensor d D)
    (X : GL (Fin D) ℂ) (ζ : ℂ)
    (hX :
      ∀ i : Fin d,
        B i =
          ζ •
            ((X : Matrix (Fin D) (Fin D) ℂ) * A i *
              ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))) :
    ∀ (N : ℕ) (σ : Fin N → Fin d), mpv B σ = ζ ^ N * mpv A σ := by
  intro N σ
  set w : List (Fin d) := List.ofFn σ
  have hwlen : w.length = N := by simp [w]
  let C : MPSTensor d D := fun i =>
    (X : Matrix (Fin D) (Fin D) ℂ) * A i *
      ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
  have hB : B = fun i => ζ • C i := by
    funext i
    simpa [C] using hX i
  have hGauge :
      evalWord C w =
        (X : Matrix (Fin D) (Fin D) ℂ) * evalWord A w *
          ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
    simpa [C] using (evalWord_gauge (A := A) (B := C) X (by intro i; rfl) w)
  have htrace : Matrix.trace (evalWord C w) = Matrix.trace (evalWord A w) := by
    simpa [hGauge, Matrix.mul_assoc] using (trace_conj_eq (X := X) (M := evalWord A w))
  calc
    mpv B σ = Matrix.trace (evalWord B w) := by simp [mpv, coeff, w]
    _ = Matrix.trace (evalWord (fun i => ζ • C i) w) := by simp [hB]
    _ = Matrix.trace ((ζ ^ w.length) • evalWord C w) := by
          simpa using congrArg Matrix.trace (evalWord_smul (ζ := ζ) (A := C) w)
    _ = (ζ ^ w.length) * Matrix.trace (evalWord C w) := by
          simp [Matrix.trace_smul, smul_eq_mul, mul_assoc]
    _ = (ζ ^ w.length) * Matrix.trace (evalWord A w) := by simp [htrace]
    _ = ζ ^ N * mpv A σ := by simp [mpv, coeff, w, hwlen, mul_assoc]

private lemma mpvOverlap_eq_pow_mul_self_of_mpv_eq_pow_mul
    {D : ℕ} (A B : MPSTensor d D) (ζ : ℂ)
    (hmpv : ∀ (N : ℕ) (σ : Fin N → Fin d), mpv B σ = ζ ^ N * mpv A σ) :
    ∀ N : ℕ,
      mpvOverlap (d := d) A B N = (star ζ) ^ N * mpvOverlap (d := d) A A N := by
  intro N
  classical
  calc
    mpvOverlap (d := d) A B N = ∑ σ : Fin N → Fin d, mpv A σ * star (mpv B σ) := by
      simp [mpvOverlap]
    _ = ∑ σ : Fin N → Fin d, mpv A σ * star (ζ ^ N * mpv A σ) := by
      refine Finset.sum_congr rfl ?_
      intro σ _
      simp [hmpv]
    _ = ∑ σ : Fin N → Fin d, mpv A σ * (star (mpv A σ) * (star ζ) ^ N) := by
      refine Finset.sum_congr rfl ?_
      intro σ _
      simp [star_mul, star_pow, mul_assoc, mul_left_comm, mul_comm]
    _ = (star ζ) ^ N * ∑ σ : Fin N → Fin d, mpv A σ * star (mpv A σ) := by
      -- factor out the constant `(star ζ) ^ N`
      simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    _ = (star ζ) ^ N * mpvOverlap (d := d) A A N := by
      simp [mpvOverlap]

private lemma sameMPV_of_gaugePhaseEquiv_of_mpvOverlap_tendsto_one
    {D : ℕ} (A B : MPSTensor d D)
    (hSelf : Filter.Tendsto (fun N => mpvOverlap (d := d) A A N) Filter.atTop (nhds (1 : ℂ)))
    (hCross : Filter.Tendsto (fun N => mpvOverlap (d := d) A B N) Filter.atTop (nhds (1 : ℂ)))
    (hGaugePhase : GaugePhaseEquiv A B) :
    SameMPV A B := by
  classical
  rcases hGaugePhase with ⟨X, ζ, hζ, hX⟩
  have hmpv : ∀ (N : ℕ) (σ : Fin N → Fin d), mpv B σ = ζ ^ N * mpv A σ :=
    mpv_eq_pow_mul_of_gaugePhase (A := A) (B := B) X ζ hX
  have hoverlap :
      ∀ N : ℕ,
        mpvOverlap (d := d) A B N = (star ζ) ^ N * mpvOverlap (d := d) A A N :=
    mpvOverlap_eq_pow_mul_self_of_mpv_eq_pow_mul (A := A) (B := B) (ζ := ζ) hmpv
  have hSelf_ne :
      (∀ᶠ N in Filter.atTop, mpvOverlap (d := d) A A N ≠ 0) :=
    hSelf.eventually_ne (by simp)
  have hratio_tendsto :
      Filter.Tendsto
        (fun N => mpvOverlap (d := d) A B N / mpvOverlap (d := d) A A N)
        Filter.atTop (nhds (1 : ℂ)) := by
    simpa using (Filter.Tendsto.div hCross hSelf (by simp))
  have hratio_eq :
      ∀ᶠ N in Filter.atTop,
        mpvOverlap (d := d) A B N / mpvOverlap (d := d) A A N = (star ζ) ^ N := by
    filter_upwards [hSelf_ne] with N hN
    have hEq := hoverlap N
    calc
      mpvOverlap (d := d) A B N / mpvOverlap (d := d) A A N
          = ((star ζ) ^ N * mpvOverlap (d := d) A A N) / mpvOverlap (d := d) A A N := by
              simp [hEq]
      _ = (star ζ) ^ N := by
            simpa using (mul_div_cancel_right₀ ((star ζ) ^ N) hN)
  have hpow_tendsto :
      Filter.Tendsto (fun N : ℕ => (star ζ) ^ N) Filter.atTop (nhds (1 : ℂ)) :=
    Filter.Tendsto.congr' hratio_eq hratio_tendsto
  have hstarζ : star ζ = (1 : ℂ) :=
    eq_one_of_tendsto_pow_atTop_nhds_one (z := star ζ) hpow_tendsto
  have hζ : ζ = 1 := by
    have := congrArg star hstarζ
    simpa using this
  have hGauge : GaugeEquiv A B := by
    refine ⟨X, ?_⟩
    intro i
    simp [hζ, hX i]
  exact GaugeEquiv.sameMPV hGauge

end BlockSeparationCoreHelpers

/-! ### Block separation core lemma (mixed-transfer / overlap route)

This is the literature-aligned block-separation step in canonical form.
Compared to the naive statement in `PiAlgebra/BlockSeparation.lean`, we assume:

* `hB_inj` : every block of `B` is injective (needed for the overlap decay lemma
  `mpvOverlap_tendsto_zero`), and
* `hA_overlap` : aperiodicity / primitive normalization, expressed as
  `mpvOverlap (A k) (A k) N → 1` as `N → ∞`. This rules out the "overlap → 0" branch
  in the equal-or-orthogonal dichotomy.

The proof follows Pérez-García et al. (2007, Appendix E) / Cirac et al. (2021, Thm. IV.3):
we take overlaps with the leading block, apply `peeling_exponential_bound` to obtain
exponential decay of the leading overlap difference, conclude equality of the leading
block via overlap decay, and finally iterate by induction on the number of blocks.
-/
lemma block_separation_core
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hμ_strict : StrictAnti (fun k : Fin r => ‖μ k‖))
    (hμ_ne_zero : ∀ k, μ k ≠ 0)
    (hA_inj : ∀ k, IsInjective (A k))
    (hB_inj : ∀ k, IsInjective (B k))
    (hA_ds : ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1)
    (hB_ds : ∀ k, ∑ i : Fin d, (B k i)ᴴ * (B k i) = 1)
    (hA_overlap :
      ∀ k,
        Filter.Tendsto (fun N => mpvOverlap (d := d) (A k) (A k) N)
          Filter.atTop (nhds (1 : ℂ)))
    (h_summed : ∀ (N : ℕ) (σ : Fin N → Fin d),
      ∑ k : Fin r, (μ k) ^ N * (mpv (A k) σ - mpv (B k) σ) = 0) :
    ∀ k, SameMPV (A k) (B k) := by
  classical
  -- Induction on the number of blocks.
  revert μ A B hμ_strict hμ_ne_zero hA_inj hB_inj hA_ds hB_ds hA_overlap h_summed
  induction r with
  | zero =>
      intro μ A B hμ_strict hμ_ne_zero hA_inj hB_inj hA_ds hB_ds hA_overlap h_summed k
      exact k.elim0
  | succ r ih =>
      intro μ A B hμ_strict hμ_ne_zero hA_inj hB_inj hA_ds hB_ds hA_overlap h_summed
      cases r with
      | zero =>
          -- Single-block case.
          intro k
          have hk : k = 0 := Fin.ext (by omega)
          subst hk
          intro N σ
          have h_eq : (μ 0) ^ N * (mpv (A 0) σ - mpv (B 0) σ) = 0 := by
            simpa [Fin.sum_univ_one] using h_summed N σ
          have hμ_pow : (μ 0) ^ N ≠ 0 := pow_ne_zero N (hμ_ne_zero 0)
          have hsub := (mul_eq_zero.mp h_eq).resolve_left hμ_pow
          exact sub_eq_zero.mp hsub
      | succ r =>
          -- At least two blocks: peel off the leading block `0`, then apply the IH to the tail.
          have hHead : SameMPV (A 0) (B 0) := by
            -- Step 1: take overlaps with the test tensor `A 0` and rewrite the summed identity.
            have h_sum_overlap :
                ∀ N : ℕ,
                  ∑ k : Fin (Nat.succ (Nat.succ r)),
                      (star (μ k)) ^ N *
                        (mpvOverlap (d := d) (A 0) (A k) N -
                          mpvOverlap (d := d) (A 0) (B k) N) = 0 := by
              intro N
              classical
              -- Take `star` of the pointwise identity `h_summed`, then sum against `mpv (A 0)`.
              have hs_star :
                  ∀ σ : Fin N → Fin d,
                    ∑ k : Fin (Nat.succ (Nat.succ r)),
                        (star (μ k)) ^ N *
                          (star (mpv (A k) σ) - star (mpv (B k) σ)) = 0 := by
                intro σ
                have hs := h_summed N σ
                have hs' : star (∑ k : Fin (Nat.succ (Nat.succ r)),
                    (μ k) ^ N * (mpv (A k) σ - mpv (B k) σ)) = (0 : ℂ) := by
                  simpa using congrArg star hs
                -- Simplify the `star` of the sum.
                simpa [star_sum, star_mul, star_pow, star_sub,
                  mul_comm, mul_left_comm, mul_assoc] using hs'
              -- Expand the overlap sums and use `hs_star`.
              calc
                ∑ k : Fin (Nat.succ (Nat.succ r)),
                    (star (μ k)) ^ N *
                      (mpvOverlap (d := d) (A 0) (A k) N -
                        mpvOverlap (d := d) (A 0) (B k) N)
                    =
                    ∑ k : Fin (Nat.succ (Nat.succ r)),
                      (star (μ k)) ^ N *
                        (∑ σ : Fin N → Fin d,
                          mpv (A 0) σ * (star (mpv (A k) σ) - star (mpv (B k) σ))) := by
                      -- Rewrite each overlap difference as a single configuration sum.
                      simp [mpvOverlap, Finset.sum_sub_distrib, mul_sub]
                _ =
                    ∑ k : Fin (Nat.succ (Nat.succ r)),
                      ∑ σ : Fin N → Fin d,
                        (star (μ k)) ^ N *
                          (mpv (A 0) σ * (star (mpv (A k) σ) - star (mpv (B k) σ))) := by
                      -- Push the scalar coefficient into the inner sum.
                      simp [Finset.mul_sum, mul_assoc]
                _ =
                    ∑ σ : Fin N → Fin d,
                      ∑ k : Fin (Nat.succ (Nat.succ r)),
                        (star (μ k)) ^ N *
                          (mpv (A 0) σ * (star (mpv (A k) σ) - star (mpv (B k) σ))) := by
                      -- Swap the finite sums.
                      simpa using
                        (Finset.sum_comm (s := (Finset.univ : Finset (Fin (Nat.succ (Nat.succ r)))))
                          (t := (Finset.univ : Finset (Fin N → Fin d)))
                          (f := fun k σ =>
                            (star (μ k)) ^ N *
                              (mpv (A 0) σ * (star (mpv (A k) σ) - star (mpv (B k) σ)))))
                _ =
                    ∑ σ : Fin N → Fin d,
                      mpv (A 0) σ *
                        ∑ k : Fin (Nat.succ (Nat.succ r)),
                          (star (μ k)) ^ N *
                            (star (mpv (A k) σ) - star (mpv (B k) σ)) := by
                      -- Factor out `mpv (A 0) σ` from the inner sum.
                      refine Finset.sum_congr rfl ?_
                      intro σ _
                      simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
                _ = 0 := by
                      -- Each inner sum is `0` by `hs_star`.
                      -- We rewrite termwise and use that a sum of zeros is zero.
                      refine Finset.sum_eq_zero ?_
                      intro σ hσ
                      -- The inner sum vanishes by `hs_star σ`.
                      exact mul_eq_zero_of_right (mpv (A 0) σ) (hs_star σ)
            -- Step 2: apply the peeling lemma to show exponential decay of the leading overlap difference.
            let δ : Fin (Nat.succ (Nat.succ r)) → ℕ → ℂ :=
              fun k N => mpvOverlap (d := d) (A 0) (A k) N - mpvOverlap (d := d) (A 0) (B k) N
            let Dsum : ℝ := ∑ k : Fin (Nat.succ (Nat.succ r)), (dim k : ℝ)
            let Bbound : ℝ := 2 * (dim 0 : ℝ) * Dsum
            have hBbound_nn : 0 ≤ Bbound := by
              have h2dim0 : 0 ≤ (2 : ℝ) * (dim 0 : ℝ) := by positivity
              have hDsum : 0 ≤ Dsum := by
                refine Finset.sum_nonneg ?_
                intro k hk
                positivity
              -- `Bbound = (2*dim0) * Dsum`
              simpa [Bbound, mul_assoc] using mul_nonneg h2dim0 hDsum
            have hδ_bound : ∀ k N, ‖δ k N‖ ≤ Bbound := by
              intro k N
              -- triangle inequality + uniform overlap bounds from the one-sided normalization
              have h1 :
                  ‖mpvOverlap (d := d) (A 0) (A k) N‖ ≤ (dim 0 : ℝ) * (dim k : ℝ) :=
                ds_gauge_mpvOverlap_bound (d := d) (A := A 0) (B := A k)
                  (hA_ds 0) (hA_ds k) N
              have h2 :
                  ‖mpvOverlap (d := d) (A 0) (B k) N‖ ≤ (dim 0 : ℝ) * (dim k : ℝ) :=
                ds_gauge_mpvOverlap_bound (d := d) (A := A 0) (B := B k)
                  (hA_ds 0) (hB_ds k) N
              have hdim_le : (dim k : ℝ) ≤ Dsum := by
                -- `dim k` is one term in the sum
                have hnonneg : ∀ j : Fin (Nat.succ (Nat.succ r)), 0 ≤ (dim j : ℝ) := fun j => by
                  positivity
                simpa [Dsum] using
                  (Finset.single_le_sum (s := (Finset.univ : Finset (Fin (Nat.succ (Nat.succ r)))))
                    (f := fun j : Fin (Nat.succ (Nat.succ r)) => (dim j : ℝ))
                    (hf := fun j _ => hnonneg j) (a := k) (h := Finset.mem_univ k))
              calc
                ‖δ k N‖
                    = ‖mpvOverlap (d := d) (A 0) (A k) N -
                        mpvOverlap (d := d) (A 0) (B k) N‖ := rfl
                _ ≤ ‖mpvOverlap (d := d) (A 0) (A k) N‖ +
                      ‖mpvOverlap (d := d) (A 0) (B k) N‖ := norm_sub_le _ _
                _ ≤ (dim 0 : ℝ) * (dim k : ℝ) + (dim 0 : ℝ) * (dim k : ℝ) := by
                      gcongr
                _ = 2 * (dim 0 : ℝ) * (dim k : ℝ) := by ring
                _ ≤ 2 * (dim 0 : ℝ) * Dsum := by
                      have h2dim0 : 0 ≤ (2 : ℝ) * (dim 0 : ℝ) := by positivity
                      -- multiply `dim k ≤ Dsum` by the nonnegative scalar `2*dim0`
                      have := mul_le_mul_of_nonneg_left hdim_le h2dim0
                      simpa [mul_assoc, mul_left_comm, mul_comm] using this
                _ = Bbound := by
                      simp [Bbound, mul_assoc, mul_left_comm, mul_comm]
            -- Choose the dominance ratio `ρ = ‖μ 1‖ / ‖μ 0‖ < 1`.
            let ρ : ℝ :=
              ‖μ (1 : Fin (Nat.succ (Nat.succ r)))‖ / ‖μ (0 : Fin (Nat.succ (Nat.succ r)))‖
            have hρ_pos : 0 < ρ := by
              have hμ0 : 0 < ‖μ (0 : Fin (Nat.succ (Nat.succ r)))‖ :=
                norm_pos_iff.mpr (hμ_ne_zero 0)
              have hμ1 : 0 < ‖μ (1 : Fin (Nat.succ (Nat.succ r)))‖ :=
                norm_pos_iff.mpr (hμ_ne_zero 1)
              exact div_pos hμ1 hμ0
            have hρ_lt : ρ < 1 := by
              have hμ0 : 0 < ‖μ (0 : Fin (Nat.succ (Nat.succ r)))‖ :=
                norm_pos_iff.mpr (hμ_ne_zero 0)
              have h01 : (0 : Fin (Nat.succ (Nat.succ r))) < 1 :=
                (Fin.zero_lt_one : (0 : Fin (Nat.succ (Nat.succ r))) < 1)
              have hstrict : ‖μ (1 : Fin (Nat.succ (Nat.succ r)))‖ < ‖μ (0 : Fin (Nat.succ (Nat.succ r)))‖ :=
                hμ_strict h01
              exact (div_lt_one hμ0).2 hstrict
            have hρ_bound :
                ∀ k : Fin (Nat.succ (Nat.succ r)),
                  k ≠ (0 : Fin (Nat.succ (Nat.succ r))) →
                    ‖star (μ k)‖ ≤ ‖star (μ (0 : Fin (Nat.succ (Nat.succ r))))‖ * ρ := by
              intro k hk
              have hanti : Antitone (fun j : Fin (Nat.succ (Nat.succ r)) => ‖μ j‖) :=
                (hμ_strict).antitone
              have hkval : (k : ℕ) ≠ 0 := by
                simpa using (Fin.val_ne_of_ne hk)
              have hk1 : (1 : Fin (Nat.succ (Nat.succ r))) ≤ k := by
                apply (Fin.le_iff_val_le_val).2
                have : (1 : ℕ) ≤ (k : ℕ) :=
                  (Nat.one_le_iff_ne_zero).2 hkval
                simpa using this
              have hk_le : ‖μ k‖ ≤ ‖μ (1 : Fin (Nat.succ (Nat.succ r)))‖ := hanti hk1
              have hμ0ne : ‖μ (0 : Fin (Nat.succ (Nat.succ r)))‖ ≠ 0 := by
                exact ne_of_gt (norm_pos_iff.mpr (hμ_ne_zero 0))
              have hmul : ‖μ (0 : Fin (Nat.succ (Nat.succ r)))‖ * ρ =
                  ‖μ (1 : Fin (Nat.succ (Nat.succ r)))‖ := by
                dsimp [ρ]
                calc
                  ‖μ (0 : Fin (Nat.succ (Nat.succ r)))‖ *
                      (‖μ (1 : Fin (Nat.succ (Nat.succ r)))‖ /
                        ‖μ (0 : Fin (Nat.succ (Nat.succ r)))‖)
                      = (‖μ (0 : Fin (Nat.succ (Nat.succ r)))‖ *
                          ‖μ (1 : Fin (Nat.succ (Nat.succ r)))‖) /
                          ‖μ (0 : Fin (Nat.succ (Nat.succ r)))‖ := by
                            simpa [mul_assoc] using
                              (mul_div_assoc
                                ‖μ (0 : Fin (Nat.succ (Nat.succ r)))‖
                                ‖μ (1 : Fin (Nat.succ (Nat.succ r)))‖
                                ‖μ (0 : Fin (Nat.succ (Nat.succ r)))‖).symm
                  _ = ‖μ (1 : Fin (Nat.succ (Nat.succ r)))‖ := by
                            simpa [mul_assoc] using
                              (mul_div_cancel_left₀
                                (M₀ := ℝ)
                                (b := ‖μ (1 : Fin (Nat.succ (Nat.succ r)))‖)
                                (a := ‖μ (0 : Fin (Nat.succ (Nat.succ r)))‖)
                                hμ0ne)
              have : ‖μ k‖ ≤ ‖μ (0 : Fin (Nat.succ (Nat.succ r)))‖ * ρ := by
                simpa [hmul] using hk_le
              simpa [norm_star] using this
            have hpeel :
                ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ‖δ (0 : Fin (Nat.succ (Nat.succ r))) N‖ ≤ C * ρ ^ N :=
              peeling_exponential_bound (r := Nat.succ (Nat.succ r))
                (hr := Nat.succ_pos _)
                (α := fun k : Fin (Nat.succ (Nat.succ r)) => star (μ k))
                (hα₀ := (star_ne_zero).2 (hμ_ne_zero 0))
                (δ := δ)
                (B := Bbound) (hB_nn := hBbound_nn)
                (hδ_bound := hδ_bound)
                (h_sum := fun N => by simpa [δ] using h_sum_overlap N)
                (ρ := ρ) (hρ_pos := hρ_pos) (hρ_lt := hρ_lt)
                (hρ_bound := by
                  intro k hk
                  simpa using (hρ_bound k hk))
            rcases hpeel with ⟨C, hC_nn, hδ0_le⟩
            -- Step 3: the leading overlap difference tends to `0`, hence the cross-overlap tends to `1`.
            have hδ0_tendsto :
                Filter.Tendsto (fun N => δ (0 : Fin (Nat.succ (Nat.succ r))) N)
                  Filter.atTop (nhds 0) := by
              -- First show the norms tend to `0` by squeezing with `C * ρ^N`.
              have habs : |ρ| < 1 := by
                have hpos : 0 < ρ := hρ_pos
                have hlt : ρ < 1 := hρ_lt
                simpa [abs_of_pos hpos] using hlt
              have hpow :
                  Filter.Tendsto (fun N => ρ ^ N) Filter.atTop (nhds (0 : ℝ)) := by
                simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one habs)
              have hmul :
                  Filter.Tendsto (fun N => C * ρ ^ N) Filter.atTop (nhds (0 : ℝ)) := by
                simpa using (Filter.Tendsto.const_mul C hpow)
              have hnorm :
                  Filter.Tendsto (fun N => ‖δ (0 : Fin (Nat.succ (Nat.succ r))) N‖)
                    Filter.atTop (nhds (0 : ℝ)) := by
                refine tendsto_of_tendsto_of_tendsto_of_le_of_le
                  (f := fun N => ‖δ (0 : Fin (Nat.succ (Nat.succ r))) N‖)
                  (g := fun _ => (0 : ℝ)) (h := fun N => C * ρ ^ N)
                  (hg := tendsto_const_nhds)
                  (hh := hmul)
                  (hgf := fun N => norm_nonneg (δ (0 : Fin (Nat.succ (Nat.succ r))) N))
                  (hfh := fun N => hδ0_le N)
              exact (tendsto_zero_iff_norm_tendsto_zero).2 hnorm
            have hCross_tendsto :
                Filter.Tendsto (fun N => mpvOverlap (d := d) (A 0) (B 0) N)
                  Filter.atTop (nhds (1 : ℂ)) := by
              have hSelf := hA_overlap (0 : Fin (Nat.succ (Nat.succ r)))
              have h :
                  Filter.Tendsto
                    (fun N =>
                      mpvOverlap (d := d) (A 0) (A 0) N -
                        δ (0 : Fin (Nat.succ (Nat.succ r))) N)
                    Filter.atTop (nhds (1 : ℂ)) := by
                simpa using (hSelf.sub hδ0_tendsto)
              refine Filter.Tendsto.congr (fun N => ?_) h
              simp [δ, sub_sub]
            -- Step 4: overlap limit forces gauge equivalence, hence `SameMPV`.
            have hGaugePhase : GaugePhaseEquiv (A 0) (B 0) :=
              gaugePhaseEquiv_of_mpvOverlap_tendsto_one (A := A 0) (B := B 0)
                (hA_inj 0) (hB_inj 0) (hA_ds 0) (hB_ds 0) hCross_tendsto
            exact
              sameMPV_of_gaugePhaseEquiv_of_mpvOverlap_tendsto_one (A := A 0) (B := B 0)
                (hSelf := hA_overlap 0) (hCross := hCross_tendsto) hGaugePhase
          -- Derive the summed identity for the tail blocks and apply the induction hypothesis.
          have h_summed_tail :
              ∀ (N : ℕ) (σ : Fin N → Fin d),
                ∑ k : Fin (Nat.succ r),
                  (μ k.succ) ^ N * (mpv (A k.succ) σ - mpv (B k.succ) σ) = 0 := by
            intro N σ
            have hsum :
                (μ 0) ^ N * (mpv (A 0) σ - mpv (B 0) σ) +
                  ∑ k : Fin (Nat.succ r),
                    (μ k.succ) ^ N * (mpv (A k.succ) σ - mpv (B k.succ) σ) = 0 := by
              simpa [Fin.sum_univ_succ] using h_summed N σ
            have hhead : (μ 0) ^ N * (mpv (A 0) σ - mpv (B 0) σ) = 0 := by
              simp [hHead N σ]
            simpa [hhead] using hsum
          have hTail :
              ∀ k : Fin (Nat.succ r), SameMPV (A k.succ) (B k.succ) := by
            -- apply IH to the shifted data
            have hμ_strict_tail :
                StrictAnti (fun k : Fin (Nat.succ r) => ‖μ k.succ‖) := by
              intro a b hab
              have hab' : a.succ < b.succ := (Fin.succ_lt_succ_iff).2 hab
              exact hμ_strict hab'
            exact ih
              (dim := fun k : Fin (Nat.succ r) => dim k.succ)
              (μ := fun k : Fin (Nat.succ r) => μ k.succ)
              (A := fun k : Fin (Nat.succ r) => A k.succ)
              (B := fun k : Fin (Nat.succ r) => B k.succ)
              (hμ_strict := hμ_strict_tail)
              (hμ_ne_zero := fun k => hμ_ne_zero k.succ)
              (hA_inj := fun k => hA_inj k.succ)
              (hB_inj := fun k => hB_inj k.succ)
              (hA_ds := fun k => hA_ds k.succ)
              (hB_ds := fun k => hB_ds k.succ)
              (hA_overlap := fun k => hA_overlap k.succ)
              (h_summed := h_summed_tail)
          -- Assemble head + tail.
          intro k
          refine Fin.cases
            (motive := fun k : Fin (Nat.succ (Nat.succ r)) => SameMPV (A k) (B k))
            hHead (fun k => hTail k) k

/-! ### Block separation -/

section BlockSeparation

/-- The summed identity for a fixed word w and all powers L.
From SameMPV₂ of block-diagonal tensors, for any word w of length M:
  ∑_k (μ_k^M)^L · [tr(T_k^L) - tr(U_k^L)] = 0
where T_k = evalWord(A_k, w), U_k = evalWord(B_k, w). -/
theorem summed_identity_for_word
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (h_summed : ∀ (N : ℕ) (σ : Fin N → Fin d),
      ∑ k : Fin r, (μ k) ^ N * (mpv (A k) σ - mpv (B k) σ) = 0)
    (w : List (Fin d)) (L : ℕ) :
    ∑ k : Fin r, ((μ k) ^ w.length) ^ L *
      (Matrix.trace ((evalWord (A k) w) ^ L) -
       Matrix.trace ((evalWord (B k) w) ^ L)) = 0 := by
  set M := w.length
  have hlen : ((List.replicate L w).flatten).length = M * L := by
    rw [List.length_flatten, List.map_replicate, List.sum_replicate, smul_eq_mul, mul_comm]
  set σ : Fin (M * L) → Fin d := fun i =>
    ((List.replicate L w).flatten).get (Fin.cast hlen.symm i)
  have hofFn : List.ofFn σ = (List.replicate L w).flatten := by
    conv_rhs => rw [← List.ofFn_getElem ((List.replicate L w).flatten)]
    apply List.ofFn_congr (by omega)
  have hsummed := h_summed (M * L) σ
  simp only [mpv, coeff, hofFn, evalWord_flatten_replicate, mul_sub] at hsummed
  rw [Finset.sum_sub_distrib, sub_eq_zero] at hsummed
  conv_lhs =>
    arg 2; ext k
    rw [show ((μ k) ^ M) ^ L = (μ k) ^ (M * L) from (pow_mul _ _ _).symm]
  rw [show (∑ k : Fin r, (μ k) ^ (M * L) *
    (Matrix.trace ((evalWord (A k) w) ^ L) -
     Matrix.trace ((evalWord (B k) w) ^ L))) =
    ∑ k : Fin r, (μ k) ^ (M * L) * Matrix.trace ((evalWord (A k) w) ^ L) -
    ∑ k : Fin r, (μ k) ^ (M * L) * Matrix.trace ((evalWord (B k) w) ^ L)
    from by rw [← Finset.sum_sub_distrib]; congr 1; ext k; ring]
  exact sub_eq_zero.mpr hsummed

theorem sameMPV_of_charpoly_eq_all_words
    {D : ℕ} [NeZero D]
    (A B : MPSTensor d D)
    (h : ∀ w : List (Fin d), (evalWord A w).charpoly = (evalWord B w).charpoly) :
    SameMPV A B := by
  intro N σ
  simp only [mpv, coeff]
  exact trace_eq_of_charpoly_eq _ _ (h (List.ofFn σ))

/-- Block separation for all blocks: a direct consequence of the core lemma.
Under canonical form hypotheses, the summed identity implies per-block SameMPV.
Requires injectivity of all blocks (used in the core lemma for the spectral gap
argument). -/
theorem block_separation_all_words
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hμ_strict : StrictAnti (fun k : Fin r => ‖μ k‖))
    (hμ_ne_zero : ∀ k, μ k ≠ 0)
    (hA_inj : ∀ k, IsInjective (A k))
    (hB_inj : ∀ k, IsInjective (B k))
    (hA_ds : ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1)
    (hB_ds : ∀ k, ∑ i : Fin d, (B k i)ᴴ * (B k i) = 1)
    (hA_overlap :
      ∀ k,
        Filter.Tendsto (fun N => mpvOverlap (d := d) (A k) (A k) N)
          Filter.atTop (nhds (1 : ℂ)))
    (h_summed : ∀ (N : ℕ) (σ : Fin N → Fin d),
      ∑ k : Fin r, (μ k) ^ N *
        (mpv (A k) σ - mpv (B k) σ) = 0) :
    ∀ k, SameMPV (A k) (B k) :=
  block_separation_core μ A B hμ_strict hμ_ne_zero hA_inj hB_inj hA_ds hB_ds hA_overlap h_summed

end BlockSeparation

/-! ### Block separation under canonical form -/

section CanonicalFormSeparation

variable {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]

theorem per_block_sameMPV_of_canonical_form
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : IsCanonicalForm μ A)
    (hB_inj : ∀ k, IsInjective (B k))
    (hB_ds : ∀ k, ∑ i : Fin d, (B k i)ᴴ * (B k i) = 1)
    (hSame₂ : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B)) :
    ∀ k, SameMPV (A k) (B k) := by
  by_cases hr : r ≤ 1
  · intro k N σ
    have := sameMPV₂_summed_blocks μ A B hSame₂ N σ
    interval_cases r
    · exact k.elim0
    · have hk : k = 0 := Fin.ext (by omega)
      subst hk
      simp only [Fin.sum_univ_one, smul_eq_mul] at this
      exact mul_left_cancel₀ (pow_ne_zero N (hA.mu_ne_zero 0)) this
  · push_neg at hr
    have h_summed : ∀ (N : ℕ) (σ : Fin N → Fin d),
        ∑ k : Fin r, (μ k) ^ N * (mpv (A k) σ - mpv (B k) σ) = 0 := by
      intro N σ
      have heq := sameMPV₂_summed_blocks μ A B hSame₂ N σ
      simp only [smul_eq_mul] at heq
      simp only [mul_sub]
      rw [Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr heq
    exact block_separation_all_words μ A B hA.mu_strict_anti hA.mu_ne_zero
      hA.block_injective hB_inj hA.ds_gauge hB_ds hA.overlap_tendsto_one h_summed

theorem fundamentalTheorem_canonicalForm
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : IsCanonicalForm μ A)
    (hB_inj : ∀ k, IsInjective (B k))
    (hB_ds : ∀ k, ∑ i : Fin d, (B k i)ᴴ * (B k i) = 1)
    (hSame₂ : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B)) :
    (∀ k, GaugeEquiv (A k) (B k)) ∧
    GaugeEquiv (toTensorFromBlocks μ A) (toTensorFromBlocks μ B) := by
  have hSep := per_block_sameMPV_of_canonical_form μ A B hA hB_inj hB_ds hSame₂
  exact ⟨fun k => fundamentalTheorem_singleBlock (hA.block_injective k) (hSep k),
         fundamentalTheorem_multiBlock_global μ A B hA.block_injective hSep⟩

theorem fundamentalTheorem_canonicalForm_explicit
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : IsCanonicalForm μ A)
    (hB_inj : ∀ k, IsInjective (B k))
    (hB_ds : ∀ k, ∑ i : Fin d, (B k i)ᴴ * (B k i) = 1)
    (hSame₂ : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B)) :
    ∃ (X : ∀ k, GL (Fin (dim k)) ℂ),
    ∀ k i, B k i = (X k : Matrix _ _ ℂ) * A k i *
      (((X k)⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) := by
  have hSep := per_block_sameMPV_of_canonical_form μ A B hA hB_inj hB_ds hSame₂
  exact fundamentalTheorem_multiBlock_explicit A B hA.block_injective hSep

end CanonicalFormSeparation

end MPSTensor
