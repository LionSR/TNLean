/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.Correlations
import TNLean.Spectral.QuantitativeGap

/-!
# Unconditional exponential decay of connected correlations

This file proves an **unconditional** exponential decay bound for the connected
correlator `connectedCorrelator A ρ X Y n` of an injective MPS tensor `A`.

The source is CPGSV21, arXiv:2011.12127, Sec. II.B.3.

## Outline

1. **Reduction identity**: for a right fixed point `ρ` of the transfer map
   with `tr(ρ) = 1`, define the traceless matrix
   `Z = X * ρ − (tr(X * ρ)) • ρ`.  Then `tr(Z) = 0` and the connected
   correlator reduces to
   `C(X,Y;n) = tr(Y · E_A^n (Z))`.

2. **Unconditional exponential decay**: combine the reduction identity with
   the traceless-iterate estimate `correlation_length_bound` (which follows
   from the complementary transfer-map gap) to obtain
   `|C(X,Y;n)| ≤ C · ‖X‖ · ‖Y‖ · exp(−n/ξ)` for all `n`, `X`, `Y`, where
   `C > 0` and `ξ > 0` depend only on `A` and `ρ`.

   **Scope restriction (rate above the complementary spectral radius):**
   The source arXiv:2011.12127, Sec. II.B.3, gives the rate as `|λ₂|`, the
   modulus of the largest subleading eigenvalue.  The Gelfand-formula route
   behind `correlation_length_bound` yields only some rate strictly above
   the complementary spectral radius (see
   `docs/paper-gaps/correlator_decay_rate_above_spectral_radius.tex`).
   The exact rate `|λ₂|` requires explicit eigenvalue extraction, which is
   the remaining half of Issue #1447.

## Non-goals

The statement `connectedCorrelator_eq_sum` and its blueprint labels are
untouched.  That extraction of eigenvalues and coefficients from `E_A`
(producing the sum-of-exponentials form) is tracked by the other half of
this issue.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

private abbrev Mat (D : ℕ) := Matrix (Fin D) (Fin D) ℂ

/-! ### Reduction identity -/

/-- The traceless part of `X` relative to a fixed point `ρ` with `tr ρ = 1`:
`Z = X * ρ − (tr(X * ρ)) • ρ`.  This satisfies `tr Z = 0`. -/
noncomputable def tracelessPart (ρ X : Mat D) : Mat D :=
  X * ρ - (Matrix.trace (X * ρ)) • ρ

/-- The traceless part indeed has trace zero. -/
theorem tracelessPart_trace (ρ X : Mat D) (hTr : Matrix.trace ρ = 1) :
    Matrix.trace (tracelessPart ρ X) = 0 := by
  dsimp [tracelessPart]
  simp [Matrix.trace_mul_comm ρ X, hTr]

/-- Reduction identity for the connected correlator.

Let `ρ` satisfy `E_A(ρ) = ρ` and `tr(ρ) = 1`.  Set
`Z = X * ρ − (tr(X * ρ)) • ρ`.
Then `C(X,Y;n) = tr(Y · E_A^n (Z))`.

Reference: arXiv:2011.12127, Sec. II.B.3. -/
theorem connectedCorrelator_eq_trace_transfer_traceless
    (A : MPSTensor d D) (ρ X Y : Mat D) (n : ℕ)
    (hFix : transferMap (d := d) (D := D) A ρ = ρ)
    (hTr : Matrix.trace ρ = 1) :
    connectedCorrelator (d := d) (D := D) A ρ X Y n =
      Matrix.trace (Y * (((transferMap (d := d) (D := D) A)) ^ n) (tracelessPart ρ X)) := by
  set E := transferMap (d := d) (D := D) A
  have hE_ρ_n : ∀ k : ℕ, (E ^ k) ρ = ρ := by
    intro k
    induction' k with k ih
    · rfl
    · simp [pow_succ, hFix, ih]
  unfold connectedCorrelator twoPointExpectation onePointExpectation tracelessPart
  calc
    Matrix.trace (Y * ((E ^ n) (X * ρ))) -
        (Matrix.trace (X * ρ)) * Matrix.trace (Y * ρ) =
      Matrix.trace (Y * ((E ^ n) (X * ρ))) -
        Matrix.trace ((Matrix.trace (X * ρ)) • (Y * ρ)) := by
      simp [Matrix.trace_smul]
    _ = Matrix.trace (Y * ((E ^ n) (X * ρ)) - (Matrix.trace (X * ρ)) • (Y * ρ)) := by
      rw [Matrix.trace_sub]
    _ = Matrix.trace (Y * ((E ^ n) (X * ρ)) - Y * ((Matrix.trace (X * ρ)) • ρ)) := by
      simp [mul_smul_comm]
    _ = Matrix.trace (Y * (((E ^ n) (X * ρ)) - ((Matrix.trace (X * ρ)) • ρ))) := by
      rw [mul_sub]
    _ = Matrix.trace (Y * ((E ^ n) (X * ρ - (Matrix.trace (X * ρ)) • ρ))) := by
      simp [map_sub, map_smul, hE_ρ_n n]

/-! ### Norm estimates via entrywise Frobenius norm

All norm estimates in this section use the Frobenius (Hilbert–Schmidt) norm
`‖M‖² = ∑_{i,j} |M_{ij}|²`, which is the default `‖·‖` on
`Matrix (Fin D) (Fin D) ℂ` via the `PiLp 2` instance. -/

/-- The trace of a matrix product expanded entrywise:
`tr(Y * M) = ∑_{i,j} Y_{ij} · M_{ji}`. -/
private lemma trace_mul_eq_sum_sum (Y M : Mat D) :
    Matrix.trace (Y * M) = ∑ i : Fin D, ∑ j : Fin D, (Y i j) * (M j i) := by
  simp [Matrix.trace, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]

/-- Finite-sum estimate: `|tr(Y * M)| ≤ ‖Y‖ · ‖M‖` for the Frobenius norm.

Proof: expand the trace entrywise, apply the triangle inequality to the
double sum, then use the real Cauchy–Schwarz inequality
(`sum_mul_sq_le_sq_mul_sq`) on the `(i,j)` pairs.  Reindexing
`M_{ji} → M_{ij}` in the second factor preserves the Frobenius norm.

Reference: arXiv:2011.12127, Sec. II.B.3. -/
private lemma abs_trace_mul_le_norm_mul_norm (Y M : Mat D) :
    |Matrix.trace (Y * M)| ≤ ‖Y‖ * ‖M‖ := by
  rw [trace_mul_eq_sum_sum Y M]
  -- Triangle inequality on the double sum.
  have h_tri : |∑ i : Fin D, ∑ j : Fin D, (Y i j) * (M j i)| ≤
      ∑ i : Fin D, ∑ j : Fin D, |(Y i j) * (M j i)| := by
    -- For ℂ, ‖z‖ = |z|, so `norm_sum_le` gives the triangle inequality for sums.
    simpa using le_trans (norm_sum_le (Finset.univ : Finset (Fin D))
      (fun i => ∑ j : Fin D, (Y i j) * (M j i)))
      (Finset.sum_le_sum fun i _ => norm_sum_le (Finset.univ : Finset (Fin D))
        (fun j => (Y i j) * (M j i)))
  have h_abs_mul : ∑ i : Fin D, ∑ j : Fin D, |(Y i j) * (M j i)| =
      ∑ i : Fin D, ∑ j : Fin D, |Y i j| * |M j i| := by
    simp_rw [abs_mul]
  rw [h_abs_mul] at h_tri
  -- Cauchy–Schwarz on the product set.
  have h_sq : ((∑ i : Fin D, ∑ j : Fin D, |Y i j| * |M j i| : ℝ) ^ 2) ≤
      ((∑ i : Fin D, ∑ j : Fin D, (|Y i j| : ℝ) ^ 2) *
       (∑ i : Fin D, ∑ j : Fin D, (|M j i| : ℝ) ^ 2)) := by
    have := sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin D × Fin D))
      (fun (p : Fin D × Fin D) => (|Y p.1 p.2| : ℝ))
      (fun (p : Fin D × Fin D) => (|M p.2 p.1| : ℝ))
    simpa [Finset.sum_product] using this
  have h_nonneg : 0 ≤ (∑ i : Fin D, ∑ j : Fin D, |Y i j| * |M j i| : ℝ) := by
    refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
    positivity
  -- Take square roots.
  have h_sqrt : (∑ i : Fin D, ∑ j : Fin D, |Y i j| * |M j i| : ℝ) ≤
      Real.sqrt ((∑ i : Fin D, ∑ j : Fin D, (|Y i j| : ℝ) ^ 2) *
        (∑ i : Fin D, ∑ j : Fin D, (|M j i| : ℝ) ^ 2)) := by
    calc
      (∑ i : Fin D, ∑ j : Fin D, |Y i j| * |M j i| : ℝ) =
          Real.sqrt (((∑ i : Fin D, ∑ j : Fin D, |Y i j| * |M j i| : ℝ) ^ 2)) := by
        rw [Real.sqrt_sq h_nonneg]
      _ ≤ Real.sqrt ((∑ i : Fin D, ∑ j : Fin D, (|Y i j| : ℝ) ^ 2) *
          (∑ i : Fin D, ∑ j : Fin D, (|M j i| : ℝ) ^ 2)) :=
        Real.sqrt_le_sqrt h_sq
  have h_sqrt_mul : Real.sqrt ((∑ i : Fin D, ∑ j : Fin D, (|Y i j| : ℝ) ^ 2) *
      (∑ i : Fin D, ∑ j : Fin D, (|M j i| : ℝ) ^ 2)) =
    Real.sqrt (∑ i : Fin D, ∑ j : Fin D, (|Y i j| : ℝ) ^ 2) *
    Real.sqrt (∑ i : Fin D, ∑ j : Fin D, (|M j i| : ℝ) ^ 2) := by
    rw [Real.sqrt_mul (Finset.sum_nonneg fun _ _ => by positivity)]
  have h_normY : Real.sqrt (∑ i : Fin D, ∑ j : Fin D, (|Y i j| : ℝ) ^ 2) = ‖Y‖ := by
    -- ‖Y‖² = ∑_{i,j} |Y_{ij}|² via PiLp 2.
    have h_norm_sq_eq : ‖Y‖ ^ 2 = ∑ i : Fin D, ∑ j : Fin D, (|Y i j| : ℝ) ^ 2 := by
      calc
        ‖Y‖ ^ 2 = ∑ i : Fin D, ‖Y i‖ ^ 2 :=
          norm_sq_eq_of_L2 (β := fun _ : Fin D => PiLp 2 (fun _ : Fin D => ℂ)) Y
        _ = ∑ i : Fin D, (∑ j : Fin D, ‖Y i j‖ ^ 2) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_sq_eq_of_L2 (β := fun _ : Fin D => ℂ) (Y i)]
        _ = ∑ i : Fin D, ∑ j : Fin D, (|Y i j| : ℝ) ^ 2 := by simp
    simp [h_norm_sq_eq, Real.sqrt_sq (norm_nonneg _)]
  have h_normM : Real.sqrt (∑ i : Fin D, ∑ j : Fin D, (|M j i| : ℝ) ^ 2) = ‖M‖ := by
    -- Re-indexing (j,i) → (k,l) preserves the square sum.
    have h_reindex : (∑ i : Fin D, ∑ j : Fin D, (|M j i| : ℝ) ^ 2) =
        (∑ k : Fin D, ∑ l : Fin D, (|M k l| : ℝ) ^ 2) := by
      rw [Finset.sum_comm]
    have h_norm_sq_eq : ‖M‖ ^ 2 = ∑ k : Fin D, ∑ l : Fin D, (|M k l| : ℝ) ^ 2 := by
      calc
        ‖M‖ ^ 2 = ∑ i : Fin D, ‖M i‖ ^ 2 :=
          norm_sq_eq_of_L2 (β := fun _ : Fin D => PiLp 2 (fun _ : Fin D => ℂ)) M
        _ = ∑ i : Fin D, (∑ j : Fin D, ‖M i j‖ ^ 2) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_sq_eq_of_L2 (β := fun _ : Fin D => ℂ) (M i)]
        _ = ∑ i : Fin D, ∑ j : Fin D, (|M i j| : ℝ) ^ 2 := by simp
    simp [h_reindex, h_norm_sq_eq, Real.sqrt_sq (norm_nonneg _)]
  -- Assemble.
  refine le_trans h_tri (le_trans h_sqrt ?_)
  rw [h_sqrt_mul, h_normY, h_normM]

/-- Frobenius-norm submultiplicativity for square matrices:
`‖X * ρ‖ ≤ ‖X‖ · ‖ρ‖`.

Proof: entrywise expansion with Cauchy–Schwarz on the inner sum index.

Reference: arXiv:2011.12127, Sec. II.B.3. -/
private lemma norm_mul_le_norm_mul_norm (X ρ : Mat D) :
    ‖X * ρ‖ ≤ ‖X‖ * ‖ρ‖ := by
  -- Use the squared norm to avoid square roots.
  have h_sq : ‖X * ρ‖ ^ 2 ≤ (‖X‖ * ‖ρ‖) ^ 2 := by
    have h_norm_sq : ‖X * ρ‖ ^ 2 = ∑ i : Fin D, ∑ k : Fin D, ‖(X * ρ) i k‖ ^ 2 := by
      calc
        ‖X * ρ‖ ^ 2 = ∑ i : Fin D, ‖(X * ρ) i‖ ^ 2 :=
          norm_sq_eq_of_L2 (β := fun _ : Fin D => PiLp 2 (fun _ : Fin D => ℂ)) (X * ρ)
        _ = ∑ i : Fin D, (∑ k : Fin D, ‖(X * ρ) i k‖ ^ 2) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_sq_eq_of_L2 (β := fun _ : Fin D => ℂ) ((X * ρ) i)]
    rw [h_norm_sq]
    have h_entry : ∀ i k, ‖(X * ρ) i k‖ ^ 2 = |∑ j : Fin D, X i j * ρ j k| ^ 2 := by
      intro i k; simp [Matrix.mul_apply]
    simp_rw [h_entry]
    have h_entry_bound : ∀ i k,
        |∑ j : Fin D, X i j * ρ j k| ^ 2 ≤
        (∑ j : Fin D, ‖X i j‖ ^ 2) * (∑ j : Fin D, ‖ρ j k‖ ^ 2) := by
      intro i k
      calc
        |∑ j : Fin D, X i j * ρ j k| ^ 2 ≤ (∑ j : Fin D, |X i j * ρ j k|) ^ 2 := by
          have h_sum_le : |∑ j : Fin D, X i j * ρ j k| ≤ ∑ j : Fin D, |X i j * ρ j k| := by
            simpa using norm_sum_le (Finset.univ : Finset (Fin D))
              (fun j => X i j * ρ j k)
          nlinarith
        _ ≤ (∑ j : Fin D, (|X i j| : ℝ) * (|ρ j k| : ℝ)) ^ 2 := by
          refine pow_le_pow_left (by positivity) (Finset.sum_le_sum fun j _ => ?_) 2
          rw [abs_mul]
        _ ≤ (∑ j : Fin D, (|X i j| : ℝ) ^ 2) * (∑ j : Fin D, (|ρ j k| : ℝ) ^ 2) := by
          -- Cauchy–Schwarz
          have h_cs := sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin D))
            (fun j => (|X i j| : ℝ)) (fun j => (|ρ j k| : ℝ))
          -- CS gives `(∑ ab)² ≤ (∑ a²) * (∑ b²)`.  We already have the square on the outside.
          have h_cs' : (∑ j : Fin D, (|X i j| : ℝ) * (|ρ j k| : ℝ)) ^ 2 ≤
            (∑ j : Fin D, ((|X i j| : ℝ) ^ 2)) * (∑ j : Fin D, ((|ρ j k| : ℝ) ^ 2)) := h_cs
          -- The goal is exactly this.
          exact h_cs'
        _ = (∑ j : Fin D, ‖X i j‖ ^ 2) * (∑ j : Fin D, ‖ρ j k‖ ^ 2) := by
          simp
    have h_sum_bound : (∑ i : Fin D, ∑ k : Fin D,
        |∑ j : Fin D, X i j * ρ j k| ^ 2) ≤
        (∑ i : Fin D, ∑ k : Fin D,
          (∑ j : Fin D, ‖X i j‖ ^ 2) * (∑ j : Fin D, ‖ρ j k‖ ^ 2)) := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => h_entry_bound i k
    -- Factor the RHS: (∑_{i,j} ‖X_{ij}‖²) * (∑_{j,k} ‖ρ_{jk}‖²)
    have h_factor : (∑ i : Fin D, ∑ k : Fin D,
        (∑ j : Fin D, ‖X i j‖ ^ 2) * (∑ j : Fin D, ‖ρ j k‖ ^ 2)) =
        (∑ i : Fin D, ∑ j : Fin D, ‖X i j‖ ^ 2) *
        (∑ j : Fin D, ∑ k : Fin D, ‖ρ j k‖ ^ 2) := by
      simp [Finset.sum_mul, Finset.mul_sum, Finset.sum_product]
    have h_normX_sq : ∑ i : Fin D, ∑ j : Fin D, ‖X i j‖ ^ 2 = ‖X‖ ^ 2 := by
      calc
        ∑ i : Fin D, ∑ j : Fin D, ‖X i j‖ ^ 2 = ∑ i : Fin D, ‖X i‖ ^ 2 := by
          simp_rw [norm_sq_eq_of_L2 (β := fun _ : Fin D => ℂ)]
        _ = ‖X‖ ^ 2 :=
          (norm_sq_eq_of_L2 (β := fun _ : Fin D => PiLp 2 (fun _ : Fin D => ℂ)) X).symm
    have h_normρ_sq : ∑ j : Fin D, ∑ k : Fin D, ‖ρ j k‖ ^ 2 = ‖ρ‖ ^ 2 := by
      calc
        ∑ j : Fin D, ∑ k : Fin D, ‖ρ j k‖ ^ 2 = ∑ j : Fin D, ‖ρ j‖ ^ 2 := by
          simp_rw [norm_sq_eq_of_L2 (β := fun _ : Fin D => ℂ)]
        _ = ‖ρ‖ ^ 2 :=
          (norm_sq_eq_of_L2 (β := fun _ : Fin D => PiLp 2 (fun _ : Fin D => ℂ)) ρ).symm
    have h_goal : (‖X‖ * ‖ρ‖) ^ 2 = ‖X‖ ^ 2 * ‖ρ‖ ^ 2 := by ring
    calc
      ‖X * ρ‖ ^ 2 = ∑ i : Fin D, ∑ k : Fin D, ‖(X * ρ) i k‖ ^ 2 := h_norm_sq
      _ = ∑ i : Fin D, ∑ k : Fin D, |∑ j : Fin D, X i j * ρ j k| ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
        simp [Matrix.mul_apply]
      _ ≤ ∑ i : Fin D, ∑ k : Fin D,
          (∑ j : Fin D, ‖X i j‖ ^ 2) * (∑ j : Fin D, ‖ρ j k‖ ^ 2) := h_sum_bound
      _ = (∑ i : Fin D, ∑ j : Fin D, ‖X i j‖ ^ 2) *
          (∑ j : Fin D, ∑ k : Fin D, ‖ρ j k‖ ^ 2) := h_factor
      _ = ‖X‖ ^ 2 * ‖ρ‖ ^ 2 := by rw [h_normX_sq, h_normρ_sq]
      _ = (‖X‖ * ‖ρ‖) ^ 2 := by ring
  -- From squared inequality to inequality, using nonnegativity of norms.
  have h_nonneg_Xρ : 0 ≤ ‖X * ρ‖ := norm_nonneg _
  have h_nonneg_mul : 0 ≤ ‖X‖ * ‖ρ‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith

/-- Bound on the norm of the traceless part:
`‖tracelessPart ρ X‖ ≤ ‖ρ‖ · (1 + ‖ρ‖) · ‖X‖`.

Reference: arXiv:2011.12127, Sec. II.B.3. -/
private lemma norm_tracelessPart_le (ρ X : Mat D) :
    ‖tracelessPart ρ X‖ ≤ ‖ρ‖ * (1 + ‖ρ‖) * ‖X‖ := by
  dsimp [tracelessPart]
  have h_norm_mul : ‖X * ρ‖ ≤ ‖X‖ * ‖ρ‖ := norm_mul_le_norm_mul_norm X ρ
  have h_abs_trace : |Matrix.trace (X * ρ)| ≤ ‖X‖ * ‖ρ‖ :=
    abs_trace_mul_le_norm_mul_norm X ρ
  calc
    ‖X * ρ - (Matrix.trace (X * ρ)) • ρ‖ ≤ ‖X * ρ‖ + ‖(Matrix.trace (X * ρ)) • ρ‖ :=
      norm_sub_le _ _
    _ ≤ ‖X * ρ‖ + |Matrix.trace (X * ρ)| * ‖ρ‖ := by simp
    _ ≤ (‖X‖ * ‖ρ‖) + (‖X‖ * ‖ρ‖) * ‖ρ‖ := by gcongr
    _ = ‖X‖ * (‖ρ‖ + ‖ρ‖ * ‖ρ‖) := by ring
    _ = ‖ρ‖ * (1 + ‖ρ‖) * ‖X‖ := by ring

/-! ### Unconditional exponential decay -/

/-- **Unconditional exponential decay of connected correlations**.

For an injective TP-normalized MPS tensor `A` and a right fixed point `ρ`
of the transfer map with `tr(ρ) = 1`, there exist `C > 0` and `ξ > 0` such
that for all `n`, `X`, `Y`,

`|C(X,Y;n)| ≤ C · ‖X‖ · ‖Y‖ · exp(−n / ξ)`.

The rate `ξ` is the same as in `correlation_length_bound`; it corresponds
to a rate strictly above the complementary transfer-map spectral radius.
The constants `‖ρ‖` and the factor from the trace-norm estimate are
absorbed into `C`.

**Scope restriction (rate above the complementary spectral radius):**
arXiv:2011.12127, Sec. II.B.3, gives the exact rate `|λ₂|`.  The present
bound uses the Gelfand route which yields only a rate strictly above
`ρ(E_A − P)`.  Documented in
`docs/paper-gaps/correlator_decay_rate_above_spectral_radius.tex`.

Reference: arXiv:2011.12127, Sec. II.B.3. -/
theorem connectedCorrelator_exp_decay [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hA : IsInjective A)
    (ρ : Mat D)
    (hFix : transferMap (d := d) (D := D) A ρ = ρ)
    (hTr : Matrix.trace ρ = 1) :
    ∃ (C : ℝ) (ξ : ℝ),
      0 < C ∧ 0 < ξ ∧
      ∀ (n : ℕ) (X Y : Mat D),
        ‖connectedCorrelator (d := d) (D := D) A ρ X Y n‖ ≤
          C * ‖X‖ * ‖Y‖ * Real.exp (-(n : ℝ) / ξ) := by
  set E := transferMap (d := d) (D := D) A
  rcases correlation_length_bound (A := A) hNorm hA with ⟨C₀, ξ, hC₀_pos, hξ_pos, h_bound⟩
  -- Absorb ‖ρ‖ into the constant.
  set C := C₀ * (‖ρ‖ * (1 + ‖ρ‖)) with hC_def
  have hC_pos : 0 < C := by
    dsimp [C]
    have hρ_norm_nonneg : 0 ≤ ‖ρ‖ := norm_nonneg _
    have h_one_plus_nonneg : 0 ≤ 1 + ‖ρ‖ := by nlinarith
    positivity
  refine ⟨C, ξ, hC_pos, hξ_pos, ?_⟩
  intro n X Y
  set Z := tracelessPart ρ X with hZ_def
  have htrZ : Matrix.trace Z = 0 := tracelessPart_trace ρ X hTr
  have h_reduction : connectedCorrelator (d := d) (D := D) A ρ X Y n =
      Matrix.trace (Y * ((E ^ n) Z)) :=
    connectedCorrelator_eq_trace_transfer_traceless A ρ X Y n hFix hTr
  rw [h_reduction]
  have h_EnZ_norm : ‖(E ^ n) Z‖ ≤ C₀ * Real.exp (-(n : ℝ) / ξ) * ‖Z‖ := by
    simpa [E, Module.End.pow_apply] using h_bound n Z htrZ
  calc
    ‖Matrix.trace (Y * ((E ^ n) Z))‖ = |Matrix.trace (Y * ((E ^ n) Z))| := rfl
    _ ≤ ‖Y‖ * ‖(E ^ n) Z‖ := abs_trace_mul_le_norm_mul_norm Y ((E ^ n) Z)
    _ ≤ ‖Y‖ * (C₀ * Real.exp (-(n : ℝ) / ξ) * ‖Z‖) := by gcongr
    _ = C₀ * ‖Z‖ * ‖Y‖ * Real.exp (-(n : ℝ) / ξ) := by ring
    _ ≤ C₀ * (‖ρ‖ * (1 + ‖ρ‖) * ‖X‖) * ‖Y‖ * Real.exp (-(n : ℝ) / ξ) := by
      gcongr
      exact norm_tracelessPart_le ρ X
    _ = C * ‖X‖ * ‖Y‖ * Real.exp (-(n : ℝ) / ξ) := by
      dsimp [C]
      ring

end MPSTensor
