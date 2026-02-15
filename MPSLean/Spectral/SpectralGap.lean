/-
Copyright (c) 2025 MPSLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MPSLean.Spectral.MixedTransfer
import MPSLean.QuantumPerronFrobenius
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Spectral gap for the mixed transfer operator

The key analytic ingredient: if a linear operator on a finite-dimensional
space has spectral radius strictly less than 1, then its iterates converge
to zero. This is the mechanism by which the mixed transfer operator
`F_{AB}` for distinct blocks `A ≠ B` decays, enabling block separation.

## Main results

* `eigenvalue_norm_le_one`: every eigenvalue of `F_{AB}` has modulus ≤ 1
* `spectralRadius_mixedTransfer_le_one`: `ρ(F_{AB}) ≤ 1` for normalized tensors
* `spectralRadius_mixedTransfer_lt_one`: strict spectral gap for non-equivalent blocks
* `mixedTransfer_pow_tendsto_zero`: `F_{AB}^n → 0` for distinct blocks

## References

* [PerezGarcia2007String] Pérez-García, Verstraete, Wolf, Cirac,
  *Matrix Product State Representations*, 2007.
* [Evans1978Spectral] Evans, Hanche-Olsen, *Spectral properties of positive
  maps on C*-algebras*, 1978.
-/

open scoped Matrix ComplexOrder BigOperators NNReal ENNReal

namespace MPSTensor

variable {d D : ℕ}

section SpectralConvergence

/-! ### Normed algebra structure on matrices

We use the L∞-operator norm on matrices, which Mathlib provides as
`Matrix.linftyOpNormedRing` and `Matrix.linftyOpNormedAlgebra`.
These are not global instances, so we introduce them locally. -/

/-- Local instance: `Matrix (Fin D) (Fin D) ℂ` is a normed ring
under the L∞-operator norm. -/
noncomputable scoped instance : NormedRing (Matrix (Fin D) (Fin D) ℂ) :=
  Matrix.linftyOpNormedRing

/-- Local instance: `Matrix (Fin D) (Fin D) ℂ` is a normed algebra over `ℂ`
under the L∞-operator norm. -/
noncomputable scoped instance : NormedAlgebra ℂ (Matrix (Fin D) (Fin D) ℂ) :=
  Matrix.linftyOpNormedAlgebra

/-! ### Transfer matrix (vectorized transfer operator)

The transfer matrix is the Kronecker-product representation of the
mixed transfer map, acting on vectorized matrices. -/

/-- The **transfer matrix** (vectorized transfer operator): the
`(D×D) × (D×D)` matrix representing the mixed transfer operator
under the vectorization isomorphism `M_D(ℂ) ≅ ℂ^{D²}`.

`T_AB = ∑_k A^k ⊗ conj(B^k)` where `⊗` is the Kronecker product. -/
noncomputable def transferMatrix (A B : MPSTensor d D) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  ∑ k : Fin d, Matrix.kroneckerMap (· * ·) (A k) (star (B k))

/-- The transfer matrix for `A = B` is the standard self-transfer matrix. -/
theorem transferMatrix_self (A : MPSTensor d D) :
    transferMatrix A A = ∑ k : Fin d, Matrix.kroneckerMap (· * ·) (A k) (star (A k)) := by
  rfl

/-! ### Spectral radius of the mixed transfer operator -/

/-- The **spectral radius** of the mixed transfer operator,
defined as the spectral radius of the linear map `F_{AB}` viewed in
the normed algebra of continuous linear endomorphisms.

Mathematically this equals the spectral radius of the vectorized
transfer matrix; the connection is given by
`mixedTransferSpectralRadius_eq_transferMatrix_spectralRadius`. -/
noncomputable def mixedTransferSpectralRadius (A B : MPSTensor d D) : ENNReal :=
  spectralRadius ℂ
    ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) (mixedTransferMap A B))

/-- The spectral radius of the mixed transfer operator (as a linear map) equals
the spectral radius of the vectorized transfer matrix (Kronecker form).

This follows from the fact that vectorization gives an algebra isomorphism
between `Module.End ℂ (M_D(ℂ))` and `M_{D²}(ℂ)`. -/
theorem mixedTransferSpectralRadius_eq_transferMatrix
    (A B : MPSTensor d D) :
    mixedTransferSpectralRadius A B =
      (⨆ k ∈ spectrum ℂ (transferMatrix A B), (‖k‖₊ : ENNReal)) := by
  sorry

/-! ### Spectral radius bound from uniform power-norm bound

A general Banach-algebra fact: if every power of `a` has nonnegative
norm bounded by a fixed constant `C`, then the spectral radius of `a`
is at most 1.  The proof uses `ρ(a)^n ≤ ρ(a^n) ≤ ‖a^n‖₊ ≤ C`, so
`ρ(a)^n` is bounded, which forces `ρ(a) ≤ 1`. -/

/-! ### Key spectral gap property

The crucial fact for block separation: when `A` and `B` come from
**different** irreducible blocks, the mixed transfer operator `F_{AB}`
has spectral radius strictly less than 1 (assuming both blocks are
individually normalized so their self-transfer maps have spectral
radius 1).

The proof factors into two independent ingredients:
1. **Spectral radius bound** (`spectralRadius_mixedTransfer_le_one`): ρ(F_{AB}) ≤ 1.
2. **Eigenvalue rigidity** (`modulus_one_eigenvalue_implies_gauge`): if ρ(F_{AB}) ≥ 1,
   then A and B are gauge-phase equivalent.

Combining via contrapositive: ¬gauge → ρ < 1. -/

/-! ### Frobenius norm squared

The Frobenius norm squared `frobSq(X) = tr(X† X).re = ∑ᵢⱼ ‖Xᵢⱼ‖²` is used
as a proxy for the Hilbert–Schmidt norm to prove that every eigenvalue of
the mixed transfer operator has modulus ≤ 1. -/

/-- Frobenius norm squared of a matrix: `tr(X† X).re`. -/
noncomputable def frobSq (X : Matrix (Fin D) (Fin D) ℂ) : ℝ :=
  (Matrix.trace (Xᴴ * X)).re

lemma frobSq_nonneg (X : Matrix (Fin D) (Fin D) ℂ) : 0 ≤ frobSq X := by
  unfold frobSq
  have h := (Matrix.posSemidef_conjTranspose_mul_self X).trace_nonneg
  rw [Complex.le_def] at h; exact h.1

private lemma complex_mul_star_re (z : ℂ) : (z * star z).re = ‖z‖ ^ 2 := by
  change (z * starRingEnd ℂ z).re = ‖z‖ ^ 2
  rw [Complex.mul_conj', ← Complex.ofReal_pow]; exact Complex.ofReal_re _

lemma frobSq_eq_sum (X : Matrix (Fin D) (Fin D) ℂ) :
    frobSq X = ∑ i : Fin D, ∑ j : Fin D, ‖X i j‖ ^ 2 := by
  unfold frobSq
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [show (∑ i : Fin D, ∑ j : Fin D, star (X j i) * X j i) =
      (∑ j : Fin D, ∑ i : Fin D, star (X j i) * X j i) from Finset.sum_comm]
  simp only [Complex.re_sum]; congr 1; ext i; congr 1; ext j
  rw [mul_comm, complex_mul_star_re]

lemma frobSq_eq_zero_iff (X : Matrix (Fin D) (Fin D) ℂ) : frobSq X = 0 ↔ X = 0 := by
  rw [frobSq_eq_sum]; constructor
  · intro h; ext i j
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      Finset.sum_nonneg (fun j _ => by positivity :
        ∀ j ∈ Finset.univ, (0:ℝ) ≤ ‖X i j‖ ^ 2))).mp h i (Finset.mem_univ _)
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity :
        ∀ j ∈ Finset.univ, (0:ℝ) ≤ ‖X i j‖ ^ 2)).mp h2 j (Finset.mem_univ _)
    rwa [sq_eq_zero_iff, norm_eq_zero] at h3
  · intro h; simp [h]

lemma frobSq_pos_of_ne_zero (X : Matrix (Fin D) (Fin D) ℂ) (hX : X ≠ 0) :
    0 < frobSq X :=
  lt_of_le_of_ne (frobSq_nonneg X) (Ne.symm (mt (frobSq_eq_zero_iff X).mp hX))

lemma frobSq_smul (c : ℂ) (X : Matrix (Fin D) (Fin D) ℂ) :
    frobSq (c • X) = ‖c‖ ^ 2 * frobSq X := by
  simp only [frobSq_eq_sum, Matrix.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  rw [Finset.mul_sum]; congr 1; ext i; rw [Finset.mul_sum]

/-! ### Eigenvector iteration -/

/-- If `F(v) = μ • v`, then `F^n(v) = μ^n • v`. -/
lemma eigenvector_pow {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (F : V →ₗ[ℂ] V) (v : V) (μ : ℂ) (h : F v = μ • v) (n : ℕ) :
    (F ^ n) v = μ ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    have : (F ^ (n + 1)) v = (F ^ n) (F v) := rfl
    rw [this, h, map_smul, ih, smul_smul, mul_comm]; ring_nf

/-! ### Helper lemmas for the HS contraction bound -/

/-- Factoring a sandwich sum: `∑ᵢ A Mᵢ B = A (∑ᵢ Mᵢ) B`. -/
private lemma sum_sandwich (A B : Matrix (Fin D) (Fin D) ℂ)
    (M : Fin d → Matrix (Fin D) (Fin D) ℂ) :
    ∑ i : Fin d, A * M i * B = A * (∑ i : Fin d, M i) * B := by
  rw [Finset.mul_sum, Finset.sum_mul]

/-- **Normalization gives `∑_σ w(σ)† w(σ) = I`.**

If `∑ Kᵢ† Kᵢ = I`, then summing over all words of length `n`:
`∑_σ evalWord(K,σ)† evalWord(K,σ) = I`.

This is the iterated version of the TP condition. -/
lemma word_conjTranspose_mul_sum (K : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hK : ∑ i : Fin d, (K i)ᴴ * K i = 1) (n : ℕ) :
    ∑ σ : Fin n → Fin d,
      (evalWord K (List.ofFn σ))ᴴ * evalWord K (List.ofFn σ) = 1 := by
  induction n with
  | zero => simp [evalWord, Finset.univ_unique]
  | succ n ih =>
    rw [sum_fin_succ_eq]
    simp_rw [List.ofFn_cons, evalWord, Matrix.conjTranspose_mul]
    have key : ∀ (A B C D : Matrix (Fin D) (Fin D) ℂ),
        A * B * (C * D) = A * (B * C) * D := fun _ _ _ _ => by
      simp [Matrix.mul_assoc]
    simp_rw [key]
    rw [Finset.sum_comm]
    simp_rw [sum_sandwich _ _ (fun i => (K i)ᴴ * K i)]
    simp_rw [hK, Matrix.mul_one]
    exact ih

/-- The standard transfer map preserves trace (for TP tensors). -/
lemma trace_transferMap (A : MPSTensor d D) (Z : Matrix (Fin D) (Fin D) ℂ)
    (hA : ∑ i : Fin d, (A i)ᴴ * A i = 1) :
    Matrix.trace (transferMap (d := d) (D := D) A Z) = Matrix.trace Z := by
  rw [transferMap_apply, Matrix.trace_sum]
  conv_lhs =>
    arg 2; ext i
    rw [show Matrix.trace (A i * Z * (A i)ᴴ) = Matrix.trace ((A i)ᴴ * A i * Z) from by
      rw [Matrix.trace_mul_comm (A i * Z) ((A i)ᴴ), Matrix.mul_assoc]]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, hA, one_mul]

/-! ### Hilbert–Schmidt contraction for the mixed transfer operator

The proof embeds `M_D(ℂ)` into `EuclideanSpace ℂ (Fin D × Fin D)` so that
`‖toES M‖² = frobSq M`. The triangle inequality and submultiplicativity of
the Frobenius norm, together with Cauchy–Schwarz on the word sum, yield:

$$‖F^n(X)‖² ≤ (∑_σ ‖w_A(σ)‖ ‖X w_B(σ)†‖)²
  ≤ (∑ ‖w_A‖²)(∑ ‖X w_B†‖²) = D · ‖X‖².$$
-/

/-- Embed a `D×D` matrix into `EuclideanSpace` to access the Frobenius norm. -/
private noncomputable def toES (M : Matrix (Fin D) (Fin D) ℂ) :
    EuclideanSpace ℂ (Fin D × Fin D) :=
  (EuclideanSpace.equiv (Fin D × Fin D) ℂ).symm (fun p => M p.1 p.2)

@[simp] private lemma toES_apply (M : Matrix (Fin D) (Fin D) ℂ) (p : Fin D × Fin D) :
    toES M p = M p.1 p.2 := by simp [toES, EuclideanSpace.equiv]

private lemma toES_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → Matrix (Fin D) (Fin D) ℂ) :
    toES (∑ i ∈ s, f i) = ∑ i ∈ s, toES (f i) := by
  ext p; simp [Matrix.sum_apply, Finset.sum_apply]

/-- The Euclidean norm squared of `toES M` equals `frobSq M`. -/
private lemma norm_toES_sq (M : Matrix (Fin D) (Fin D) ℂ) :
    ‖toES M‖ ^ 2 = frobSq M := by
  rw [sq, ← @inner_self_eq_norm_mul_norm ℂ]
  change RCLike.re (@inner ℂ _ _ (toES M) (toES M)) = _
  simp only [PiLp.inner_apply, RCLike.inner_apply', toES_apply, starRingEnd_apply]
  rw [show (∑ x : Fin D × Fin D, star (M x.1 x.2) * M x.1 x.2) =
    ∑ i : Fin D, ∑ j : Fin D, star (M i j) * M i j from Fintype.sum_prod_type _]
  simp only [frobSq, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [show (∑ i : Fin D, ∑ j : Fin D, star (M i j) * M i j) =
    ∑ j : Fin D, ∑ i : Fin D, star (M i j) * M i j from Finset.sum_comm]
  simp [RCLike.re_to_complex]

/-- Entry-wise Cauchy–Schwarz: `‖∑ aₖ bₖ‖² ≤ (∑ ‖aₖ‖²)(∑ ‖bₖ‖²)`. -/
private lemma norm_sq_sum_mul_le (a b : Fin D → ℂ) :
    ‖∑ k, a k * b k‖ ^ 2 ≤ (∑ k, ‖a k‖ ^ 2) * (∑ k, ‖b k‖ ^ 2) := by
  calc ‖∑ k, a k * b k‖ ^ 2
      ≤ (∑ k, ‖a k‖ * ‖b k‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _)
          ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => norm_mul_le _ _))) 2
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

set_option maxHeartbeats 800000 in
-- Frobenius submultiplicativity needs extra heartbeats for simp_rw over double sums
/-- Frobenius-norm submultiplicativity: `frobSq(A B) ≤ frobSq A · frobSq B`. -/
private lemma frobSq_mul_le (A B : Matrix (Fin D) (Fin D) ℂ) :
    frobSq (A * B) ≤ frobSq A * frobSq B := by
  simp only [frobSq_eq_sum, Matrix.mul_apply]
  calc ∑ i, ∑ j, ‖∑ k, A i k * B k j‖ ^ 2
      ≤ ∑ i, ∑ j, (∑ k, ‖A i k‖ ^ 2) * (∑ k, ‖B k j‖ ^ 2) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => norm_sq_sum_mul_le _ _))
    _ = (∑ i, ∑ k, ‖A i k‖ ^ 2) * (∑ j, ∑ k, ‖B k j‖ ^ 2) := by
        simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    _ = (∑ i, ∑ j, ‖A i j‖ ^ 2) * (∑ i, ∑ j, ‖B i j‖ ^ 2) := by
        congr 1; exact Finset.sum_comm

/-- `‖toES (A * B)‖ ≤ ‖toES A‖ * ‖toES B‖` — Frobenius submultiplicativity for norms. -/
private lemma norm_toES_mul_le (A B : Matrix (Fin D) (Fin D) ℂ) :
    ‖toES (A * B)‖ ≤ ‖toES A‖ * ‖toES B‖ := by
  have h : ‖toES (A * B)‖ ^ 2 ≤ (‖toES A‖ * ‖toES B‖) ^ 2 := by
    rw [norm_toES_sq, mul_pow, norm_toES_sq, norm_toES_sq]; exact frobSq_mul_le A B
  have h1 := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq (norm_nonneg _),
       Real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _))] at h1

/-- Trace cycling: `tr(w v† · v w†) = tr(w† w · v† v)`. -/
private lemma trace_cycle_for_frobSq (w v : Matrix (Fin D) (Fin D) ℂ) :
    (w * vᴴ * (v * wᴴ)).trace = (wᴴ * w * (vᴴ * v)).trace := by
  rw [Matrix.mul_assoc w vᴴ _, ← Matrix.mul_assoc vᴴ v wᴴ,
      ← Matrix.mul_assoc w (vᴴ * v) wᴴ,
      Matrix.trace_mul_comm (w * (vᴴ * v)) wᴴ,
      ← Matrix.mul_assoc wᴴ w (vᴴ * v)]

/-- **B-side collapse**: `∑_σ frobSq(v · w_B(σ)†) = frobSq v`.

Uses the TP condition `∑ Bᵢ† Bᵢ = I` iterated over words. -/
private lemma sum_frobSq_right (B : MPSTensor d D) (hB : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (v : Matrix (Fin D) (Fin D) ℂ) (n : ℕ) :
    ∑ σ : Fin n → Fin d, frobSq (v * (evalWord B (List.ofFn σ))ᴴ) = frobSq v := by
  simp only [frobSq, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  conv_lhs => arg 2; ext σ; rw [trace_cycle_for_frobSq (evalWord B (List.ofFn σ)) v]
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul,
      word_conjTranspose_mul_sum B hB n, Matrix.one_mul]

/-- **A-side word sum**: `∑_σ frobSq(w_K(σ)) = D`. -/
private lemma sum_frobSq_words (K : MPSTensor d D) (hK : ∑ i : Fin d, (K i)ᴴ * K i = 1)
    (n : ℕ) :
    ∑ σ : Fin n → Fin d, frobSq (evalWord K (List.ofFn σ)) = (D : ℝ) := by
  simp only [frobSq]
  rw [← Complex.re_sum, ← Matrix.trace_sum, word_conjTranspose_mul_sum K hK n]
  simp [Matrix.trace_one, Fintype.card_fin]

set_option maxHeartbeats 1600000 in
-- The uniform bound proof chains triangle + CS + Frobenius submult over word sums
/-- **Uniform Frobenius-norm bound** on the mixed transfer operator.

For normalized MPS tensors (`∑ Aᵢ† Aᵢ = 1` and `∑ Bᵢ† Bᵢ = 1`):
$$\|F_{AB}^n(X)\|_F^2 \le D^2 \cdot \|X\|_F^2$$

The proof embeds matrices in EuclideanSpace, applies the triangle inequality
and Frobenius submultiplicativity to factor each word term, then uses
Cauchy–Schwarz on the word sum. The A-side sum telescopes to `D` and the
B-side sum telescopes to `frobSq X`, giving `≤ D · frobSq X ≤ D² · frobSq X`. -/
private lemma hs_contraction_mixedTransfer [NeZero D]
    (A B : MPSTensor d D) (X : Matrix (Fin D) (Fin D) ℂ)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1) (n : ℕ) :
    frobSq (((mixedTransferMap A B) ^ n) X) ≤ (D : ℝ) ^ 2 * frobSq X := by
  -- Expand and reassociate: w_A(σ) * X * w_B(σ)† = w_A(σ) * (X * w_B(σ)†)
  rw [mixedTransferMap_pow_apply, show (∑ σ : Fin n → Fin d,
    evalWord A (List.ofFn σ) * X * (evalWord B (List.ofFn σ))ᴴ) =
    (∑ σ : Fin n → Fin d,
    evalWord A (List.ofFn σ) * (X * (evalWord B (List.ofFn σ))ᴴ)) from by
    congr 1; ext σ; rw [Matrix.mul_assoc]]
  -- Switch to EuclideanSpace norm: frobSq(M) = ‖toES M‖²
  rw [show frobSq (∑ σ : Fin n → Fin d,
    evalWord A (List.ofFn σ) * (X * (evalWord B (List.ofFn σ))ᴴ)) =
    ‖toES (∑ σ : Fin n → Fin d,
    evalWord A (List.ofFn σ) * (X * (evalWord B (List.ofFn σ))ᴴ))‖ ^ 2 from
    (norm_toES_sq _).symm]
  -- Per-term norms for Cauchy-Schwarz
  set fA := fun σ : Fin n → Fin d => ‖toES (evalWord A (List.ofFn σ))‖ with hfA_def
  set fB := fun σ : Fin n → Fin d => ‖toES (X * (evalWord B (List.ofFn σ))ᴴ)‖ with hfB_def
  -- Triangle inequality + Frobenius submultiplicativity chain
  have h_chain : ‖toES (∑ σ : Fin n → Fin d,
    evalWord A (List.ofFn σ) * (X * (evalWord B (List.ofFn σ))ᴴ))‖ ≤
    ∑ σ : Fin n → Fin d, fA σ * fB σ := by
    calc ‖toES (∑ σ : Fin n → Fin d,
        evalWord A (List.ofFn σ) * (X * (evalWord B (List.ofFn σ))ᴴ))‖
        ≤ ∑ σ : Fin n → Fin d,
          ‖toES (evalWord A (List.ofFn σ) * (X * (evalWord B (List.ofFn σ))ᴴ))‖ := by
          rw [toES_finset_sum]; exact norm_sum_le _ _
      _ ≤ ∑ σ : Fin n → Fin d, fA σ * fB σ :=
          Finset.sum_le_sum (fun σ _ => norm_toES_mul_le _ _)
  -- Cauchy–Schwarz: (∑ f·g)² ≤ (∑ f²)(∑ g²)
  have h_cs : (∑ σ : Fin n → Fin d, fA σ * fB σ) ^ 2 ≤
    (∑ σ : Fin n → Fin d, fA σ ^ 2) * (∑ σ : Fin n → Fin d, fB σ ^ 2) := by
    exact_mod_cast Finset.sum_mul_sq_le_sq_mul_sq Finset.univ fA fB
  -- A-side: ∑ fA² = ∑ frobSq(w_A(σ)) = D
  have h_A : ∑ σ : Fin n → Fin d, fA σ ^ 2 = (D : ℝ) := by
    simp_rw [hfA_def, norm_toES_sq]; exact sum_frobSq_words A hA_norm n
  -- B-side: ∑ fB² = ∑ frobSq(X w_B(σ)†) = frobSq X
  have h_B : ∑ σ : Fin n → Fin d, fB σ ^ 2 = frobSq X := by
    simp_rw [hfB_def, norm_toES_sq]; exact sum_frobSq_right B hB_norm X n
  -- Combine: ‖toES(...)‖² ≤ (∑ f·g)² ≤ D · frobSq X ≤ D² · frobSq X
  have hD : (1 : ℝ) ≤ D := by exact_mod_cast NeZero.one_le (n := D)
  calc ‖toES _‖ ^ 2
      ≤ (∑ σ : Fin n → Fin d, fA σ * fB σ) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h_chain 2
    _ ≤ (∑ σ : Fin n → Fin d, fA σ ^ 2) * (∑ σ : Fin n → Fin d, fB σ ^ 2) := h_cs
    _ = (D : ℝ) * frobSq X := by rw [h_A, h_B]
    _ ≤ (D : ℝ) ^ 2 * frobSq X := by nlinarith [sq_nonneg ((D : ℝ) - 1), frobSq_nonneg X]

/-! ### Eigenvalue bound -/

/-- **Every eigenvalue of the mixed transfer operator has modulus ≤ 1.**

If `F_{AB}(v) = μ v` with `v ≠ 0`, then `|μ| ≤ 1`.

**Proof:** By contradiction. If `|μ| > 1`, then
`‖F^n(v)‖_F² = |μ|^{2n} ‖v‖_F²` grows unboundedly with `n`,
contradicting the uniform bound `‖F^n(v)‖_F² ≤ D² ‖v‖_F²`. -/
theorem eigenvalue_norm_le_one [NeZero D]
    (A B : MPSTensor d D)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (μ : ℂ) (hμ : Module.End.HasEigenvalue (mixedTransferMap A B) μ) :
    ‖μ‖ ≤ 1 := by
  obtain ⟨v, hv_mem, hv_ne⟩ := hμ.exists_hasEigenvector
  have hFv := Module.End.mem_eigenspace_iff.mp hv_mem
  by_contra h_gt; push_neg at h_gt
  have h_pos : 0 < frobSq v := frobSq_pos_of_ne_zero v hv_ne
  -- Uniform bound: ‖μ‖^(2n) ≤ D² for all n
  have h_bound : ∀ n : ℕ, ‖μ‖ ^ (2 * n) ≤ (D : ℝ) ^ 2 := by
    intro n
    have h1 := hs_contraction_mixedTransfer A B v hA_norm hB_norm n
    rw [eigenvector_pow _ v μ hFv n, frobSq_smul, norm_pow] at h1
    have h2 : ‖μ‖ ^ (2 * n) = (‖μ‖ ^ n) ^ 2 := by ring
    rw [h2]; exact le_of_mul_le_mul_right (by linarith) h_pos
  -- Contradiction: ‖μ‖ > 1 means (‖μ‖²)^n → ∞, exceeding D²
  have h_sq_gt : 1 < ‖μ‖ ^ 2 := by nlinarith
  have htend := tendsto_pow_atTop_atTop_of_one_lt h_sq_gt
  rw [Filter.tendsto_atTop_atTop] at htend
  obtain ⟨n, hn⟩ := htend ((D : ℝ) ^ 2 + 1)
  linarith [h_bound n, show (‖μ‖ ^ 2) ^ n = ‖μ‖ ^ (2 * n) from by ring, hn n le_rfl]

/-- **Spectral radius bound**: For normalized MPS tensors A, B
(meaning `∑ Aᵢ† Aᵢ = 1` and `∑ Bᵢ† Bᵢ = 1`), the mixed transfer
operator `F_{AB}` has spectral radius at most 1.

**Proof:** In finite dimensions, every element of the spectrum is an
eigenvalue. By `eigenvalue_norm_le_one`, each eigenvalue has `|μ| ≤ 1`.
The spectral radius (supremum of `‖k‖₊` over the spectrum) is therefore ≤ 1. -/
theorem spectralRadius_mixedTransfer_le_one
    (A B : MPSTensor d D)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1) :
    mixedTransferSpectralRadius A B ≤ 1 := by
  unfold mixedTransferSpectralRadius
  rcases eq_or_ne D 0 with rfl | hD
  · -- D = 0: trivial (subsingleton)
    haveI : Subsingleton (Matrix (Fin 0) (Fin 0) ℂ) := by
      constructor; intro a b; ext i; exact i.elim0
    haveI : Subsingleton (Matrix (Fin 0) (Fin 0) ℂ →L[ℂ] Matrix (Fin 0) (Fin 0) ℂ) :=
      ContinuousLinearMap.uniqueOfLeft.instSubsingleton
    rw [spectrum.SpectralRadius.of_subsingleton]; exact zero_le _
  · -- D ≥ 1: eigenvalue-based argument
    haveI : NeZero D := ⟨hD⟩
    let V := Matrix (Fin D) (Fin D) ℂ
    let Φ : (V →ₗ[ℂ] V) ≃ₐ[ℂ] (V →L[ℂ] V) := Module.End.toContinuousLinearMap V
    let F := mixedTransferMap A B
    have h_spec : spectrum ℂ (Φ F) = spectrum ℂ F := AlgEquiv.spectrum_eq Φ F
    apply iSup₂_le
    intro k hk
    rw [ENNReal.coe_le_one_iff]
    haveI : FiniteDimensional ℂ V := Module.Finite.matrix
    have hk_eigen : Module.End.HasEigenvalue F k :=
      Module.End.hasEigenvalue_iff_mem_spectrum.mpr (h_spec ▸ hk)
    exact_mod_cast eigenvalue_norm_le_one A B hA_norm hB_norm k hk_eigen

/-- **Eigenvalue rigidity** (Pérez-García et al. 2007, Lemma 5):
If the mixed transfer operator `F_{AB}` has spectral radius ≥ 1 (i.e.,
it has an eigenvalue of modulus ≥ 1), and both A, B are injective and
normalized, then A and B must be gauge-phase equivalent.

This is the hard mathematical content of the spectral gap theorem.
The proof requires the doubly-stochastic gauge construction and
analysis of the Cauchy–Schwarz equality case in the Hilbert–Schmidt
contraction argument. -/
axiom modulus_one_eigenvalue_implies_gauge
    (A B : MPSTensor d D)
    (hA : IsInjective A) (hB : IsInjective B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hsr : mixedTransferSpectralRadius A B ≥ 1) :
    GaugePhaseEquiv A B

/-- **Spectral gap for distinct blocks**: If `A` and `B` are injective,
normalized MPS tensors that are *not* gauge-phase equivalent, then the
mixed transfer operator `F_{AB}` has spectral radius strictly less than 1.

This is the quantum analogue of: for a primitive non-negative matrix,
off-diagonal blocks in the transfer matrix have spectral radius < 1.

**Proof:** Combines the two ingredients:
- `spectralRadius_mixedTransfer_le_one`: ρ(F_{AB}) ≤ 1
- `modulus_one_eigenvalue_implies_gauge`: ρ(F_{AB}) ≥ 1 → gauge equivalent

By contrapositive of the second, ¬gauge → ρ < 1 (together with ≤ 1). -/
theorem spectralRadius_mixedTransfer_lt_one
    (A B : MPSTensor d D)
    (hA : IsInjective A) (hB : IsInjective B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hAB : ¬ GaugePhaseEquiv A B) :
    mixedTransferSpectralRadius A B < 1 := by
  have h_le := spectralRadius_mixedTransfer_le_one A B hA_norm hB_norm
  by_contra h_not_lt
  push_neg at h_not_lt
  -- h_le : ρ ≤ 1, h_not_lt : 1 ≤ ρ, so ρ ≥ 1
  exact hAB (modulus_one_eigenvalue_implies_gauge A B hA hB hA_norm hB_norm h_not_lt)

/-! ### Power convergence from spectral radius bound

The following theorem gives the fundamental convergence result:
if the spectral radius of an element in a Banach algebra is < 1,
then its powers converge to zero.

This can be derived from the Gelfand formula (available in Mathlib)
combined with the norm convergence criterion. -/

/-- **Powers tend to zero when spectral radius < 1.** In a complex
Banach algebra, if `spectralRadius ℂ a < 1`, then `a ^ n → 0`.

This follows from the Gelfand formula: `‖a^n‖^{1/n} → ρ(a)`, so
for large `n`, `‖a^n‖^{1/n} < r` for some `r < 1`, giving
`‖a^n‖ < r^n → 0`.

**Mathlib ingredients:**
- `pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`: Gelfand formula
- `tendsto_pow_atTop_nhds_zero_of_norm_lt_one`: ‖x‖ < 1 ⟹ x^n → 0
- The connection requires showing that `spectralRadius < 1` implies
  `‖a^N‖ < 1` for some `N`, and then `(a^N)^n → 0` implies `a^n → 0`.

The full formal proof requires careful handling of the `ℝ≥0∞`-valued
spectral radius and the passage from the limit to a uniform bound. -/
theorem pow_tendsto_zero_of_spectralRadius_lt_one
    {A : Type*} [NormedRing A] [CompleteSpace A] [NormedAlgebra ℂ A]
    (a : A) (h : spectralRadius ℂ a < 1) :
    Filter.Tendsto (fun n => a ^ n) Filter.atTop (nhds 0) := by
  -- Step 1: Find r : NNReal with spectralRadius ℂ a < r < 1
  rw [ENNReal.lt_iff_exists_nnreal_btwn] at h
  obtain ⟨r, hr_above, hr_below⟩ := h
  -- hr_above : spectralRadius ℂ a < ↑r
  -- hr_below : ↑r < 1 (in ℝ≥0∞)
  have hr_lt_one : r < 1 := ENNReal.coe_lt_coe.mp (by rwa [ENNReal.coe_one])
  -- Step 2: From Gelfand's formula, eventually ‖a^n‖₊^(1/n) < r in ℝ≥0∞
  have gelfand := spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius a
  have hev := gelfand.eventually (eventually_lt_nhds hr_above)
  -- hev : ∀ᶠ n in atTop, (‖a ^ n‖₊ : ℝ≥0∞) ^ (1 / ↑n) < ↑r
  -- Step 3: Eventually ‖a^n‖₊ < r^n
  have hev2 : ∀ᶠ n in Filter.atTop, ‖a ^ n‖₊ < r ^ n := by
    filter_upwards [hev, Filter.eventually_gt_atTop 0] with n hn hn_pos
    have hn_pos_real : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
    rw [one_div, ENNReal.rpow_inv_lt_iff hn_pos_real] at hn
    rw [ENNReal.rpow_natCast] at hn
    exact_mod_cast hn
  -- Step 4: ‖a^n‖ ≤ (r : ℝ)^n eventually, and (r:ℝ)^n → 0
  apply squeeze_zero_norm' (a := fun n => (r : ℝ) ^ n)
  · filter_upwards [hev2] with n hn
    rw [← coe_nnnorm, ← NNReal.coe_pow]
    exact_mod_cast hn.le
  · exact tendsto_pow_atTop_nhds_zero_of_lt_one r.coe_nonneg (by exact_mod_cast hr_lt_one)

/-! ### Application to mixed transfer convergence -/

/-- **Mixed transfer iterates decay for distinct blocks.**

If `A` and `B` are injective MPS tensors from different gauge
equivalence classes, then for any matrix `X`, the iterates
`F_{AB}^n(X)` converge to zero as `n → ∞`.

This is the engine of block separation: cross-terms between distinct
blocks vanish in the large-`N` limit. -/
theorem mixedTransfer_pow_tendsto_zero
    (A B : MPSTensor d D)
    (hA : IsInjective A) (hB : IsInjective B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hAB : ¬ GaugePhaseEquiv A B)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    Filter.Tendsto (fun n => ((mixedTransferMap A B) ^ n) X)
      Filter.atTop (nhds 0) := by
  -- Step 1: Convert to continuous linear map via algebra equivalence.
  -- Module.End.toContinuousLinearMap : (V →ₗ[ℂ] V) ≃ₐ[ℂ] (V →L[ℂ] V)
  -- gives a NormedRing/NormedAlgebra structure needed for spectral theory.
  let V := Matrix (Fin D) (Fin D) ℂ
  let Φ : (V →ₗ[ℂ] V) ≃ₐ[ℂ] (V →L[ℂ] V) :=
    Module.End.toContinuousLinearMap V
  let F := mixedTransferMap A B
  let F' : V →L[ℂ] V := Φ F
  -- Step 2: spectralRadius ℂ F' < 1.
  -- By AlgEquiv.spectrum_eq, spectrum ℂ F' = spectrum ℂ F.
  -- By vectorization, spectrum ℂ F = spectrum ℂ (transferMatrix A B).
  -- Thus spectralRadius ℂ F' = mixedTransferSpectralRadius A B < 1.
  have h_sr : spectralRadius ℂ F' < 1 := by
    -- `mixedTransferSpectralRadius A B` is *defined* as `spectralRadius ℂ F'`,
    -- so this is exactly `spectralRadius_mixedTransfer_lt_one`.
    exact spectralRadius_mixedTransfer_lt_one A B hA hB hA_norm hB_norm hAB
  -- Step 3: Powers converge to zero in CLM operator norm.
  have h_clm_tendsto :
      Filter.Tendsto (fun n => F' ^ n) Filter.atTop (nhds 0) :=
    pow_tendsto_zero_of_spectralRadius_lt_one F' h_sr
  -- Step 4: Pointwise evaluation at X is continuous (via
  -- ContinuousLinearMap.apply), giving pointwise convergence.
  have h_eval_tendsto :
      Filter.Tendsto (fun n => (F' ^ n) X)
        Filter.atTop (nhds 0) := by
    have h_cont :=
      (ContinuousLinearMap.apply ℂ V X).continuous.tendsto
        (0 : V →L[ℂ] V)
    rw [map_zero] at h_cont
    exact h_cont.comp h_clm_tendsto
  -- Step 5: F^n(X) = F'^n(X) since Φ is an algebra equivalence
  -- that preserves the underlying function.
  suffices h_eq :
      ∀ n, ((mixedTransferMap A B) ^ n) X = (F' ^ n) X from by
    simp_rw [h_eq]; exact h_eval_tendsto
  intro n
  have h_pow : F' ^ n = Φ (F ^ n) := (map_pow Φ F n).symm
  simp only [h_pow]
  rfl

end SpectralConvergence

end MPSTensor
