/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Spectral.MixedTransfer
import TNLean.Spectral.FrobeniusNorm
import TNLean.QPF.Assembly
import TNLean.Channel.FixedPoint.CanonicalGauge
import TNLean.Channel.Schwarz.Basic
import TNLean.Algebra.MatrixAux
import Mathlib.Data.Matrix.Block
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

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

/-! ### Normed algebra structure on matrices -/

noncomputable scoped instance : NormedRing (Matrix (Fin D) (Fin D) ℂ) :=
  Matrix.linftyOpNormedRing

noncomputable scoped instance : NormedAlgebra ℂ (Matrix (Fin D) (Fin D) ℂ) :=
  Matrix.linftyOpNormedAlgebra

/-! ### Spectral radius of the mixed transfer operator -/

/-- The **spectral radius** of the mixed transfer operator. -/
noncomputable def mixedTransferSpectralRadius (A B : MPSTensor d D) : ENNReal :=
  spectralRadius ℂ
    ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) (mixedTransferMap A B))

theorem mixedTransferSpectralRadius_eq (A B : MPSTensor d D) :
    mixedTransferSpectralRadius A B =
      spectralRadius ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
          (mixedTransferMap A B)) := rfl

/-! ### Frobenius norm squared

The definition and basic API (`frobSq`, `frobSq_nonneg`, `frobSq_eq_zero_iff`,
`frobSq_pos_of_ne_zero`, `frobSq_smul`, `frobSq_trace`, `matToES`, …) are
provided by `TNLean.Spectral.FrobeniusNorm` for general rectangular matrices.
Below we add the square-matrix-specific lemma `frobSq_mul_le`. -/

/-- `frobSq X = ∑ i j, ‖X i j‖²` (definitional; kept for backward compatibility). -/
lemma frobSq_eq_sum (X : Matrix (Fin D) (Fin D) ℂ) :
    frobSq X = ∑ i : Fin D, ∑ j : Fin D, ‖X i j‖ ^ 2 := rfl


/-! ### Eigenvector iteration -/

/-- If `F(v) = μ • v`, then `F^n(v) = μ^n • v`. -/
lemma eigenvector_pow {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (F : V →ₗ[ℂ] V) (v : V) (μ : ℂ) (h : F v = μ • v) (n : ℕ) :
    (F ^ n) v = μ ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    change (F ^ n) (F v) = _
    rw [h, map_smul, ih, smul_smul, mul_comm]; ring_nf

/-! ### Helper lemmas for the HS contraction bound -/

/-- Iterated TP condition: `∑_σ evalWord(K,σ)† evalWord(K,σ) = I`. -/
lemma word_conjTranspose_mul_sum (K : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hK : ∑ i : Fin d, (K i)ᴴ * K i = 1) (n : ℕ) :
    ∑ σ : Fin n → Fin d,
      (evalWord K (List.ofFn σ))ᴴ * evalWord K (List.ofFn σ) = 1 := by
  induction n with
  | zero => simp [Finset.univ_unique]
  | succ n ih =>
    rw [sum_fin_succ_eq]
    simp_rw [List.ofFn_cons, evalWord, Matrix.conjTranspose_mul,
      show ∀ A B C D : Matrix (Fin D) (Fin D) ℂ,
        A * B * (C * D) = A * (B * C) * D from fun _ _ _ _ => by simp [Matrix.mul_assoc]]
    rw [Finset.sum_comm]
    simp_rw [Matrix.sum_mul_mul
      (M := fun i => (K i)ᴴ * K i), hK, Matrix.mul_one]
    exact ih

/-- The standard transfer map preserves trace (for TP tensors). -/
lemma trace_transferMap (A : MPSTensor d D) (Z : Matrix (Fin D) (Fin D) ℂ)
    (hA : ∑ i : Fin d, (A i)ᴴ * A i = 1) :
    Matrix.trace (transferMap (d := d) (D := D) A Z) = Matrix.trace Z := by
  rw [transferMap_apply, Matrix.trace_sum]
  conv_lhs => arg 2; ext i; rw [show Matrix.trace (A i * Z * (A i)ᴴ) =
    Matrix.trace ((A i)ᴴ * A i * Z) from by
      rw [Matrix.trace_mul_comm (A i * Z) _, Matrix.mul_assoc]]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, hA, one_mul]

/-! ### Hilbert–Schmidt contraction for the mixed transfer operator

The Euclidean-space embedding `matToES` and its basic API are imported from
`TNLean.Spectral.FrobeniusNorm`.  Below we add square-matrix submultiplicativity. -/

private lemma frobSq_mul_le (A B : Matrix (Fin D) (Fin D) ℂ) :
    frobSq (A * B) ≤ frobSq A * frobSq B := by
  simp only [frobSq, Matrix.mul_apply]
  calc ∑ i, ∑ j, ‖∑ k, A i k * B k j‖ ^ 2
      ≤ ∑ i, ∑ j, (∑ k, ‖A i k‖ ^ 2) * (∑ k, ‖B k j‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => norm_sq_sum_mul_le _ _
    _ = (∑ i, ∑ k, ‖A i k‖ ^ 2) * (∑ j, ∑ k, ‖B k j‖ ^ 2) := by
        simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    _ = _ := by congr 1; exact Finset.sum_comm

private lemma norm_matToES_mul_le (A B : Matrix (Fin D) (Fin D) ℂ) :
    ‖matToES (A * B)‖ ≤ ‖matToES A‖ * ‖matToES B‖ := by
  have h : ‖matToES (A * B)‖ ^ 2 ≤ (‖matToES A‖ * ‖matToES B‖) ^ 2 := by
    rw [norm_matToES_sq, mul_pow, norm_matToES_sq, norm_matToES_sq]; exact frobSq_mul_le A B
  nlinarith [Real.sqrt_le_sqrt h, Real.sqrt_sq (norm_nonneg (matToES (A * B))),
    Real.sqrt_sq (mul_nonneg (norm_nonneg (matToES A)) (norm_nonneg (matToES B)))]

private lemma trace_cycle_for_frobSq (w v : Matrix (Fin D) (Fin D) ℂ) :
    (w * vᴴ * (v * wᴴ)).trace = (wᴴ * w * (vᴴ * v)).trace := by
  rw [Matrix.mul_assoc w vᴴ _, ← Matrix.mul_assoc vᴴ v wᴴ,
      ← Matrix.mul_assoc w (vᴴ * v) wᴴ,
      Matrix.trace_mul_comm (w * (vᴴ * v)) wᴴ,
      ← Matrix.mul_assoc wᴴ w (vᴴ * v)]

private lemma sum_frobSq_right (B : MPSTensor d D) (hB : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (v : Matrix (Fin D) (Fin D) ℂ) (n : ℕ) :
    ∑ σ : Fin n → Fin d, frobSq (v * (evalWord B (List.ofFn σ))ᴴ) = frobSq v := by
  simp only [frobSq_trace, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  conv_lhs => arg 2; ext σ; rw [trace_cycle_for_frobSq (evalWord B (List.ofFn σ)) v]
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul,
      word_conjTranspose_mul_sum B hB n, Matrix.one_mul]

private lemma sum_frobSq_words (K : MPSTensor d D) (hK : ∑ i : Fin d, (K i)ᴴ * K i = 1)
    (n : ℕ) :
    ∑ σ : Fin n → Fin d, frobSq (evalWord K (List.ofFn σ)) = (D : ℝ) := by
  simp only [frobSq_trace]
  rw [← Complex.re_sum, ← Matrix.trace_sum, word_conjTranspose_mul_sum K hK n]
  simp [Matrix.trace_one, Fintype.card_fin]

/-- **Uniform Frobenius-norm bound**: `‖F_{AB}^n(X)‖_F² ≤ D² · ‖X‖_F²`. -/
private lemma hs_contraction_mixedTransfer [NeZero D]
    (A B : MPSTensor d D) (X : Matrix (Fin D) (Fin D) ℂ)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1) (n : ℕ) :
    frobSq (((mixedTransferMap A B) ^ n) X) ≤ (D : ℝ) ^ 2 * frobSq X := by
  rw [mixedTransferMap_pow_apply, show (∑ σ : Fin n → Fin d,
    evalWord A (List.ofFn σ) * X * (evalWord B (List.ofFn σ))ᴴ) =
    (∑ σ : Fin n → Fin d,
    evalWord A (List.ofFn σ) * (X * (evalWord B (List.ofFn σ))ᴴ)) from by
    congr 1; ext σ; rw [Matrix.mul_assoc]]
  rw [show frobSq (∑ σ : Fin n → Fin d,
    evalWord A (List.ofFn σ) * (X * (evalWord B (List.ofFn σ))ᴴ)) =
    ‖matToES (∑ σ : Fin n → Fin d,
    evalWord A (List.ofFn σ) * (X * (evalWord B (List.ofFn σ))ᴴ))‖ ^ 2 from
    (norm_matToES_sq _).symm]
  set fA := fun σ : Fin n → Fin d => ‖matToES (evalWord A (List.ofFn σ))‖ with hfA_def
  set fB := fun σ : Fin n → Fin d => ‖matToES (X * (evalWord B (List.ofFn σ))ᴴ)‖ with hfB_def
  have h_chain : ‖matToES (∑ σ : Fin n → Fin d,
    evalWord A (List.ofFn σ) * (X * (evalWord B (List.ofFn σ))ᴴ))‖ ≤
    ∑ σ : Fin n → Fin d, fA σ * fB σ :=
    ((by rw [matToES_finset_sum]; exact norm_sum_le _ _) : ‖matToES _‖ ≤ _).trans
      (Finset.sum_le_sum fun σ _ => norm_matToES_mul_le _ _)
  have h_A : ∑ σ : Fin n → Fin d, fA σ ^ 2 = (D : ℝ) := by
    simp_rw [hfA_def, norm_matToES_sq]; exact sum_frobSq_words A hA_norm n
  have h_B : ∑ σ : Fin n → Fin d, fB σ ^ 2 = frobSq X := by
    simp_rw [hfB_def, norm_matToES_sq]; exact sum_frobSq_right B hB_norm X n
  calc ‖matToES _‖ ^ 2
      ≤ (∑ σ : Fin n → Fin d, fA σ * fB σ) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h_chain 2
    _ ≤ (∑ σ, fA σ ^ 2) * (∑ σ, fB σ ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ fA fB
    _ = (D : ℝ) * frobSq X := by rw [h_A, h_B]
    _ ≤ (D : ℝ) ^ 2 * frobSq X := by
        nlinarith [sq_nonneg ((D : ℝ) - 1), frobSq_nonneg X,
          show (1 : ℝ) ≤ D from by exact_mod_cast NeZero.one_le (n := D)]

/-! ### Eigenvalue bound -/

/-- **Every eigenvalue of the mixed transfer operator has modulus ≤ 1.** -/
theorem eigenvalue_norm_le_one [NeZero D]
    (A B : MPSTensor d D)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (μ : ℂ) (hμ : Module.End.HasEigenvalue (mixedTransferMap A B) μ) :
    ‖μ‖ ≤ 1 := by
  obtain ⟨v, hv_mem, hv_ne⟩ := hμ.exists_hasEigenvector
  have hFv := Module.End.mem_eigenspace_iff.mp hv_mem
  by_contra h_gt; push Not at h_gt
  have h_pos := frobSq_pos_of_ne_zero v hv_ne
  have h_bound : ∀ n : ℕ, ‖μ‖ ^ (2 * n) ≤ (D : ℝ) ^ 2 := fun n => by
    have h1 := hs_contraction_mixedTransfer A B v hA_norm hB_norm n
    rw [eigenvector_pow _ v μ hFv n, frobSq_smul, norm_pow] at h1
    calc ‖μ‖ ^ (2 * n) = (‖μ‖ ^ n) ^ 2 := by ring
    _ ≤ _ := le_of_mul_le_mul_right (by linarith) h_pos
  have htend := tendsto_pow_atTop_atTop_of_one_lt (by nlinarith : 1 < ‖μ‖ ^ 2)
  rw [Filter.tendsto_atTop_atTop] at htend
  obtain ⟨n, hn⟩ := htend ((D : ℝ) ^ 2 + 1)
  linarith [h_bound n, show (‖μ‖ ^ 2) ^ n = ‖μ‖ ^ (2 * n) from by ring, hn n le_rfl]

/-- **Spectral radius bound**: `ρ(F_{AB}) ≤ 1` for normalized tensors. -/
theorem spectralRadius_mixedTransfer_le_one
    (A B : MPSTensor d D)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1) :
    mixedTransferSpectralRadius A B ≤ 1 := by
  rw [mixedTransferSpectralRadius_eq]
  rcases eq_or_ne D 0 with rfl | hD
  · have : Subsingleton (Matrix (Fin 0) (Fin 0) ℂ) := ⟨fun a b => by ext i; exact i.elim0⟩
    have : Subsingleton (Matrix (Fin 0) (Fin 0) ℂ →L[ℂ] Matrix (Fin 0) (Fin 0) ℂ) :=
      ContinuousLinearMap.uniqueOfLeft.instSubsingleton
    rw [spectrum.SpectralRadius.of_subsingleton]; exact zero_le _
  · haveI : NeZero D := ⟨hD⟩
    have h_spec := AlgEquiv.spectrum_eq (Module.End.toContinuousLinearMap
      (Matrix (Fin D) (Fin D) ℂ)) (mixedTransferMap A B)
    apply iSup₂_le; intro k hk
    rw [ENNReal.coe_le_one_iff]
    exact_mod_cast eigenvalue_norm_le_one A B hA_norm hB_norm k
      (Module.End.hasEigenvalue_iff_mem_spectrum.mpr (h_spec ▸ hk))

/-! ### Helper lemmas for the eigenvalue rigidity theorem -/

/-
**Eigenvector implies gauge** (the algebraic core of eigenvalue rigidity).

If `∑ A_i X B_i† = μX` where `X ≠ 0`, `|μ| = 1`, both tensors are injective
and normalized, then `A` and `B` are gauge-phase equivalent.

Proof strategy:

1. **X is invertible**: The kernel of X is invariant under all B_i†
   (from `∑ A_i X B_i† = μX` and `∑ A_i† A_i = I`). By injectivity of B,
   the B_i† span all matrices, so ker(X) is invariant under everything.
   If ker(X) ≠ {0}, then X = 0, contradiction.

2. **Per-index relation**: Set `C_i = X⁻¹ A_i X`. From the eigenvector equation,
   `∑ C_i B_i† = μI`. By Cauchy-Schwarz on the Hilbert-Schmidt inner product:
   `D² = |tr(∑ C_i B_i†)|² = |∑⟨B_i, C_i⟩|² ≤ (∑‖C_i‖²)(∑‖B_i‖²) = tr(∑C_i†C_i)·D`.
   So `tr(∑ C_i†C_i) ≥ D`. Also `∑(C_i - μB_i)†(C_i - μB_i) = ∑C_i†C_i - I ≥ 0`
   (the trace computation uses `∑B_i†B_i = I` and `∑C_iB_i† = μI`).
   Together with `E_A(XX†) = XX†` (which follows from QPF theory applied to
   the unique PD fixed point of the transfer map), one obtains
   `tr(∑C_i†C_i) = D`, so the PSD matrix `∑(C_i - μB_i)†(C_i - μB_i)` has
   trace 0, forcing `C_i = μB_i` for each i, i.e., `B_i = μ⁻¹X⁻¹A_iX`.

References:
* Pérez-García et al., Matrix Product State Representations (2007), Lemma 5
* Wolf, Quantum Channels & Operations (2012), §6.2
-/

/-- If `ker X` is invariant under all generators `(B k)ᴴ` and `B` is injective, then `ker X`
is invariant under every matrix of the source dimension. -/
theorem ker_all_of_inj {D₁ D₂ : ℕ}
    (B : MPSTensor d D₂) (hB : IsInjective B)
    (X : Matrix (Fin D₁) (Fin D₂) ℂ)
    (h : ∀ k : Fin d, ∀ v, X *ᵥ v = 0 → X *ᵥ ((B k)ᴴ *ᵥ v) = 0) :
    ∀ (M : Matrix (Fin D₂) (Fin D₂) ℂ) (v : Fin D₂ → ℂ),
      X *ᵥ v = 0 → X *ᵥ (M *ᵥ v) = 0 := by
  intro M v hv
  suffices ∀ N : Matrix (Fin D₂) (Fin D₂) ℂ, X *ᵥ (Nᴴ *ᵥ v) = 0 by
    specialize this Mᴴ
    rwa [Matrix.conjTranspose_conjTranspose] at this
  intro N
  have hN : N ∈ Submodule.span ℂ (Set.range B) := hB ▸ Submodule.mem_top
  induction hN using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    exact h k v hv
  | zero => simp
  | add a b _ _ ha hb =>
    rw [Matrix.conjTranspose_add, Matrix.add_mulVec, Matrix.mulVec_add, ha, hb, add_zero]
  | smul c a _ ha =>
    rw [Matrix.conjTranspose_smul, Matrix.smul_mulVec, Matrix.mulVec_smul, ha, smul_zero]

/-- If X ≠ 0 and ker(X) is invariant under all matrices, then det(X) ≠ 0.

The idea: pick v ≠ 0 with Xv = 0, map v to
any w via a rank-1 matrix M with Mv = w, then Xw = X(Mv) = 0, so X = 0. -/
private lemma det_ne_zero_of_ker_all [NeZero D]
    (X : Matrix (Fin D) (Fin D) ℂ)
    (hX : X ≠ 0)
    (h_all : ∀ M : Matrix (Fin D) (Fin D) ℂ, ∀ v, X *ᵥ v = 0 → X *ᵥ (M *ᵥ v) = 0) :
    X.det ≠ 0 := by
  by_contra h_det
  rw [Matrix.exists_mulVec_eq_zero_iff.symm] at h_det
  obtain ⟨v, hv_ne, hv⟩ := h_det
  -- v ≠ 0 and Xv = 0; we'll show Xw = 0 for all w, hence X = 0
  have h_surj : ∀ w : Fin D → ℂ, X *ᵥ w = 0 := by
    intro w
    -- find some k with v k ≠ 0
    have ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
      by_contra h_all_zero; push Not at h_all_zero
      exact hv_ne (funext h_all_zero)
    let c : Fin D → ℂ := fun j => if j = k then (v k)⁻¹ else 0
    have hMv : (Matrix.vecMulVec w c) *ᵥ v = w := by
      ext i
      simp only [Matrix.mulVec, Matrix.vecMulVec, Matrix.of_apply, dotProduct]
      conv_lhs => arg 2; ext j; rw [mul_assoc]
      rw [Finset.sum_eq_single k]
      · simp [c, hk]
      · intro j _ hjk; simp [c, hjk]
      · intro hk_abs; exact absurd (Finset.mem_univ k) hk_abs
    rw [← hMv]; exact h_all _ v hv
  have h_X_zero : X = 0 := by
    ext i j
    have h_ej := h_surj (fun k => if k = j then 1 else 0)
    have : (X *ᵥ (fun k => if k = j then 1 else 0)) i = X i j := by
      simp only [Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hbj; simp [hbj]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    rw [show (0 : Matrix (Fin D) (Fin D) ℂ) i j = 0 from rfl]
    rw [← this]; exact congr_fun h_ej i
  exact hX h_X_zero

-- From hFX and X invertible, derive ∑ (X⁻¹ A_i X) * B_i† = μ • 1
-- Algebraic conjugation step used below.
private lemma sum_conj_mul_conjTranspose [NeZero D]
    (A B : MPSTensor d D) (X : Matrix (Fin D) (Fin D) ℂ) (μ : ℂ)
    (hFX : mixedTransferMap A B X = μ • X)
    (hdet : X.det ≠ 0) :
    ∑ i : Fin d, (X⁻¹ * A i * X) * (B i)ᴴ = μ • 1 := by
  have hFX' : ∑ i : Fin d, A i * X * (B i)ᴴ = μ • X := by
    rw [← mixedTransferMap_apply]; exact hFX
  have hXinv : X⁻¹ * X = 1 := Matrix.nonsing_inv_mul X (Ne.isUnit hdet)
  have key : X⁻¹ * (∑ i : Fin d, A i * X * (B i)ᴴ) = μ • 1 := by
    rw [hFX', Matrix.mul_smul, hXinv]
  rw [Finset.mul_sum] at key
  convert key using 1; congr 1; ext i; simp [Matrix.mul_assoc]

-- If ∑ Rᵢ† Rᵢ = 0 then each Rᵢ = 0.
-- Uses the PSD trace argument to show each summand vanishes.
private lemma each_zero_of_sum_conjTranspose_mul_self_zero
    (R : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (h : ∑ i : Fin d, (R i)ᴴ * R i = 0) :
    ∀ i : Fin d, R i = 0 := by
  intro i
  have h_psd_i := Matrix.posSemidef_conjTranspose_mul_self (R i)
  have h_each_nonneg : ∀ j, 0 ≤ ((R j)ᴴ * R j).trace.re :=
    fun j => (Complex.le_def.mp (Matrix.posSemidef_conjTranspose_mul_self (R j)).trace_nonneg).1
  have h_tr_sum_re : (∑ j : Fin d, ((R j)ᴴ * R j).trace.re) = 0 := by
    rw [← Complex.re_sum, ← Matrix.trace_sum, h]; simp
  have h_tr_re : ((R i)ᴴ * R i).trace.re = 0 :=
    le_antisymm
      (by linarith [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => h_each_nonneg j)
            |>.mp h_tr_sum_re i (Finset.mem_univ i)])
      (h_each_nonneg i)
  have h_tr_zero : ((R i)ᴴ * R i).trace = 0 :=
    Complex.ext h_tr_re (Complex.le_def.mp h_psd_i.trace_nonneg).2.symm
  exact Matrix.conjTranspose_mul_self_eq_zero.mp (h_psd_i.trace_eq_zero_iff.mp h_tr_zero)

-- (The old auxiliary lemmas `eigenvector_det_ne_zero` / `per_index_from_eigenvector`
-- were based on a too-strong per-index statement for the raw eigenvector.
-- The new proof establishes invertibility + intertwining directly inside
-- `eigenvector_gives_gauge` using left-canonical gauge + weighted KS equality.)

section
open scoped MatrixOrder

/-- **Eigenvector implies gauge equivalence** (PGVWC 2007, Lemma 5; Wolf 2012, §6.2).

If `F_{AB}(X) = μ • X` with `X ≠ 0` and `‖μ‖ = 1`, then injective normalized tensors
`A` and `B` are gauge-phase equivalent.

The proof passes to the left-canonical gauge, uses the equality case of the Hilbert--Schmidt
contraction to obtain Kraus-level intertwining, shows that the resulting intertwiner is
invertible, and then upgrades the intertwining relation to gauge equivalence. -/
private lemma eigenvector_gives_gauge [NeZero D]
    (A B : MPSTensor d D) (X : Matrix (Fin D) (Fin D) ℂ) (μ : ℂ)
    (hA : IsInjective A) (hB : IsInjective B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hFX : mixedTransferMap A B X = μ • X)
    (hμ : ‖μ‖ = 1) (hX : X ≠ 0) :
    GaugePhaseEquiv A B := by
  classical
  /-
  Outline of the algebraic core:
  1. Obtain QPF positive definite fixed points `ρA, ρB` for the transfer maps of `A, B`.
  2. Gauge both tensors to left-canonical form (unital Kraus families `A', B'`).
  3. Embed the mixed transfer eigenvector as an off-diagonal block matrix `M` for a unital
     Kraus map on `Fin D ⊕ Fin D`.
  4. Use the weighted KS equality + multiplicative domain lemma from `Channel/Schwarz` to obtain
     Kraus-level intertwining identities.
  5. Kernel invariance ⇒ `det X' ≠ 0` ⇒ per-index gauge-phase relation.
  -/

  -- QPF fixed points for `transferMap A` and `transferMap B`.
  obtain ⟨ρA, hρA⟩ := injective_transfer_unique_fixed_point' (A := A) hA hA_norm
  obtain ⟨ρB, hρB⟩ := injective_transfer_unique_fixed_point' (A := B) hB hB_norm
  have hρA_fix : transferMap (d := d) (D := D) A ρA = ρA := hρA.fixed
  have hρB_fix : transferMap (d := d) (D := D) B ρB = ρB := hρB.fixed
  have hρA_pd : ρA.PosDef := hρA.pos_def
  have hρB_pd : ρB.PosDef := hρB.pos_def
  -- Factor `ρA = S0Aᴴ * S0A` and set `SA := S0Aᴴ` so that `SA * SAᴴ = ρA`.
  rcases (CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self).1 hρA_pd.isStrictlyPositive with
    ⟨S0A, hS0A_unit, hρA_eq⟩
  let SA : Matrix (Fin D) (Fin D) ℂ := S0Aᴴ
  have hSA_unit : IsUnit SA := by
    simpa [SA, Matrix.star_eq_conjTranspose] using (IsUnit.star hS0A_unit)
  have hSA_det : SA.det ≠ 0 := by
    have hdet_unit : IsUnit SA.det := (Matrix.isUnit_iff_isUnit_det (A := SA)).1 hSA_unit
    exact hdet_unit.ne_zero
  have hSA_isUnitdet : IsUnit SA.det := Ne.isUnit hSA_det
  have hSA_mul : SA * SAᴴ = ρA := by
    calc
      SA * SAᴴ = S0Aᴴ * (S0Aᴴ)ᴴ := by rfl
      _ = S0Aᴴ * S0A := by simp
      _ = ρA := by simpa [Matrix.star_eq_conjTranspose] using hρA_eq.symm
  -- Factor `ρB = S0Bᴴ * S0B` and set `SB := S0Bᴴ` so that `SB * SBᴴ = ρB`.
  rcases (CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self).1 hρB_pd.isStrictlyPositive with
    ⟨S0B, hS0B_unit, hρB_eq⟩
  let SB : Matrix (Fin D) (Fin D) ℂ := S0Bᴴ
  have hSB_unit : IsUnit SB := by
    simpa [SB, Matrix.star_eq_conjTranspose] using (IsUnit.star hS0B_unit)
  have hSB_det : SB.det ≠ 0 := by
    have hdet_unit : IsUnit SB.det := (Matrix.isUnit_iff_isUnit_det (A := SB)).1 hSB_unit
    exact hdet_unit.ne_zero
  have hSB_isUnitdet : IsUnit SB.det := Ne.isUnit hSB_det
  have hSB_mul : SB * SBᴴ = ρB := by
    calc
      SB * SBᴴ = S0Bᴴ * (S0Bᴴ)ᴴ := by rfl
      _ = S0Bᴴ * S0B := by simp
      _ = ρB := by simpa [Matrix.star_eq_conjTranspose] using hρB_eq.symm
  have hSBh_det : (SBᴴ).det ≠ 0 := by
    simpa [Matrix.det_conjTranspose] using star_ne_zero.mpr hSB_det
  have hSBh_isUnitdet : IsUnit (SBᴴ).det := Ne.isUnit hSBh_det
  -- Useful inverse-cancellation lemmas.
  have hSA_inv_mul : SA⁻¹ * SA = (1 : Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.nonsing_inv_mul SA hSA_isUnitdet
  have hSA_mul_inv : SA * SA⁻¹ = (1 : Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.mul_nonsing_inv SA hSA_isUnitdet
  have hSB_inv_mul : SB⁻¹ * SB = (1 : Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.nonsing_inv_mul SB hSB_isUnitdet
  have hSB_mul_inv : SB * SB⁻¹ = (1 : Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.mul_nonsing_inv SB hSB_isUnitdet
  have hSBh_inv_mul : (SBᴴ)⁻¹ * SBᴴ = (1 : Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.nonsing_inv_mul SBᴴ hSBh_isUnitdet
  have hSBh_mul_inv : SBᴴ * (SBᴴ)⁻¹ = (1 : Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.mul_nonsing_inv SBᴴ hSBh_isUnitdet
  have hSAh_det : (SAᴴ).det ≠ 0 := by
    simpa [Matrix.det_conjTranspose] using star_ne_zero.mpr hSA_det
  have hSAh_isUnitdet : IsUnit (SAᴴ).det := Ne.isUnit hSAh_det
  -- Left-canonical-gauged tensors.
  let A' : MPSTensor d D := fun i => SA⁻¹ * A i * SA
  let B' : MPSTensor d D := fun i => SB⁻¹ * B i * SB
  have hA'unital : ∑ i : Fin d, (A' i) * (A' i)ᴴ = 1 := by
    simpa [A'] using
      (gauged_unital (A := A) (S := SA) (ρ := ρA)
        (hS_inv := hSA_det) (hSS := hSA_mul) (hfix := hρA_fix))
  have hB'unital : ∑ i : Fin d, (B' i) * (B' i)ᴴ = 1 := by
    simpa [B'] using
      (gauged_unital (A := B) (S := SB) (ρ := ρB)
        (hS_inv := hSB_det) (hSS := hSB_mul) (hfix := hρB_fix))
  -- Gauged eigenvector.
  let X' : Matrix (Fin D) (Fin D) ℂ := SA⁻¹ * X * (SBᴴ)⁻¹
  have hX'ne : X' ≠ 0 := by
    intro h0
    have hXeq : X = SA * X' * SBᴴ := by
      -- Cancel the gauge factors explicitly (simp does not reassociate in the needed direction).
      have hXinv_mul : (SBᴴ)⁻¹ * SBᴴ = (1 : Matrix (Fin D) (Fin D) ℂ) := hSBh_inv_mul
      have hXmul_inv : SA * SA⁻¹ = (1 : Matrix (Fin D) (Fin D) ℂ) := hSA_mul_inv
      have : SA * X' * SBᴴ = X := by
        -- expand `X' = SA⁻¹ * X * (SBᴴ)⁻¹` and reassociate to expose cancellable factors
        calc
          SA * X' * SBᴴ = SA * (SA⁻¹ * X * (SBᴴ)⁻¹) * SBᴴ := by rfl
          _ = (SA * SA⁻¹) * X * ((SBᴴ)⁻¹ * SBᴴ) := by
            -- reassociate step-by-step (we need the *reverse* associativity direction)
            -- `mul_assoc` is oriented as `((a*b)*c) = a*(b*c)`, so we use `symm` where needed.
            -- Start by peeling off the rightmost factor.
            -- (This is intentionally explicit to avoid simp getting stuck.)
            --
            -- SA * (SA⁻¹ * X * (SBᴴ)⁻¹) * SBᴴ
            --   = (SA * (SA⁻¹ * X * (SBᴴ)⁻¹)) * SBᴴ
            --   = ((SA * SA⁻¹) * X * (SBᴴ)⁻¹) * SBᴴ
            --   = (SA * SA⁻¹) * X * ((SBᴴ)⁻¹ * SBᴴ)
            --
            -- We let Lean do the associativity bookkeeping.

            -- First, reassociate the left part:
            -- SA * (SA⁻¹ * X * (SBᴴ)⁻¹) = (SA * SA⁻¹) * X * (SBᴴ)⁻¹
            have hleft : SA * (SA⁻¹ * X * (SBᴴ)⁻¹) = (SA * SA⁻¹) * X * (SBᴴ)⁻¹ := by
              -- `simp` will right-associate; we want left-associated form.
              --
              -- SA * (SA⁻¹ * X * (SBᴴ)⁻¹)
              --   = (SA * SA⁻¹) * X * (SBᴴ)⁻¹
              calc
                SA * (SA⁻¹ * X * (SBᴴ)⁻¹) = (SA * SA⁻¹) * (X * (SBᴴ)⁻¹) := by
                  -- regroup as (SA*SA⁻¹) * (X*(SBᴴ)⁻¹)
                  simp [mul_assoc]
                _ = ((SA * SA⁻¹) * X) * (SBᴴ)⁻¹ := by
                  simp [mul_assoc]
                _ = (SA * SA⁻¹) * X * (SBᴴ)⁻¹ := by
                  simp [mul_assoc]
            -- Now tack on the final `* SBᴴ` and reassociate once.
            calc
              SA * (SA⁻¹ * X * (SBᴴ)⁻¹) * SBᴴ
                  = ((SA * SA⁻¹) * X * (SBᴴ)⁻¹) * SBᴴ := by
                      simp [mul_assoc]
              _ = (SA * SA⁻¹) * X * ((SBᴴ)⁻¹ * SBᴴ) := by
                  -- reassociate the last two factors
                  simp [mul_assoc]
          _ = (1 : Matrix (Fin D) (Fin D) ℂ) * X * (1 : Matrix (Fin D) (Fin D) ℂ) := by
            simp [hXmul_inv, hXinv_mul]
          _ = X := by simp
      simpa using this.symm
    have : X = 0 := by simpa [h0] using hXeq
    exact hX this
  have hFXsum : ∑ i : Fin d, A i * X * (B i)ᴴ = μ • X := by
    simpa [mixedTransferMap_apply] using hFX
  have hFX' : mixedTransferMap A' B' X' = μ • X' := by
    have hterm :
        ∀ i : Fin d,
          (A' i) * X' * (B' i)ᴴ = SA⁻¹ * (A i * X * (B i)ᴴ) * (SBᴴ)⁻¹ := by
      intro i
      -- Expand `A'`, `B'`, `X'` and cancel the gauge factors explicitly.
      -- (Relying on `simp` alone tends to get stuck because it will not reassociate in the
      -- direction needed to expose subproducts like `SA * SA⁻¹`.)

      -- First simplify the adjoint of `B' i`.
      have hBstar : (B' i)ᴴ = SBᴴ * (B i)ᴴ * (SBᴴ)⁻¹ := by
        -- `(SB⁻¹)ᴴ = (SBᴴ)⁻¹` holds for the nonsingular inverse.
        simp [B', Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, mul_assoc]
      -- Now do a straightforward reassociation + cancellation computation.
      calc
        (A' i) * X' * (B' i)ᴴ
            = (SA⁻¹ * A i * SA) * (SA⁻¹ * X * (SBᴴ)⁻¹) * (SBᴴ * (B i)ᴴ * (SBᴴ)⁻¹) := by
                simp [A', X', hBstar, mul_assoc]
        _ = SA⁻¹ * (A i * X * (B i)ᴴ) * (SBᴴ)⁻¹ := by
                -- Cancel the middle `SA * SA⁻¹` and `SBᴴ⁻¹ * SBᴴ` factors.
                -- We do this by rewriting `SA * (SA⁻¹ * Z)` and `SBᴴ⁻¹ * (SBᴴ * Z)` explicitly.

                -- Now apply the cancellations inside the big product.
                -- We work from the inside outward.
                --
                -- Starting point (after previous simp):
                --   SA⁻¹ * (A i * (SA * (SA⁻¹ * (X * (SBᴴ⁻¹ * (SBᴴ * ((B i)ᴴ * SBᴴ⁻¹)))))))
                --
                -- Cancel `SA * (SA⁻¹ * …)` and `SBᴴ⁻¹ * (SBᴴ * …)`.

                -- First cancel the `SBᴴ` pair.
                have hSBstep :
                    X * ((SBᴴ)⁻¹ * (SBᴴ * ((B i)ᴴ * (SBᴴ)⁻¹))) =
                      X * ((B i)ᴴ * (SBᴴ)⁻¹) := by
                  -- rewrite the inner parenthesis using `hSBh_cancel'`
                  simpa [mul_assoc] using
                    congrArg (fun T => X * T)
                      (Matrix.nonsing_inv_mul_cancel_left SBᴴ
                        (((B i)ᴴ) * (SBᴴ)⁻¹) hSBh_isUnitdet)
                -- Now cancel the `SA` pair.
                have hSAstep :
                    A i * (SA * (SA⁻¹ * (X * ((B i)ᴴ * (SBᴴ)⁻¹)))) =
                      A i * (X * ((B i)ᴴ * (SBᴴ)⁻¹)) := by
                  simpa [mul_assoc] using
                    congrArg (fun T => A i * T)
                      (Matrix.mul_nonsing_inv_cancel_left SA
                        (X * ((B i)ᴴ * (SBᴴ)⁻¹)) hSA_isUnitdet)
                -- Put it together.
                -- (The left `SA⁻¹` is common on both sides, so `simp` can finish.)
                simpa [mul_assoc, hSBstep] using congrArg (fun T => SA⁻¹ * T) hSAstep
    calc
      mixedTransferMap A' B' X' = ∑ i : Fin d, (A' i) * X' * (B' i)ᴴ := by
        simp [mixedTransferMap_apply]
      _ = ∑ i : Fin d, SA⁻¹ * (A i * X * (B i)ᴴ) * (SBᴴ)⁻¹ := by
        simp [hterm]
      _ = SA⁻¹ * (∑ i : Fin d, A i * X * (B i)ᴴ) * (SBᴴ)⁻¹ := by
        simpa using
          (Matrix.sum_mul_mul
            (L := SA⁻¹) (M := fun i : Fin d => A i * X * (B i)ᴴ)
            (R := (SBᴴ)⁻¹))
      _ = SA⁻¹ * (μ • X) * (SBᴴ)⁻¹ := by rw [hFXsum]
      _ = μ • (SA⁻¹ * X * (SBᴴ)⁻¹) := by
        simp [Matrix.mul_assoc]
      _ = μ • X' := rfl
  -- Block embedding into a unital Kraus map on `Fin D ⊕ Fin D`.
  let K : Fin d → Matrix (Fin D ⊕ Fin D) (Fin D ⊕ Fin D) ℂ :=
    fun i => Matrix.fromBlocks (A' i) 0 0 (B' i)
  let M : Matrix (Fin D ⊕ Fin D) (Fin D ⊕ Fin D) ℂ :=
    Matrix.fromBlocks (0 : Matrix (Fin D) (Fin D) ℂ) X' 0 0
  have hK_unital : Kraus.IsUnital K := by
    unfold Kraus.IsUnital
    have hsum :
        (∑ i : Fin d, K i * (K i)ᴴ) =
          Matrix.fromBlocks (∑ i : Fin d, (A' i) * (A' i)ᴴ)
            (0 : Matrix (Fin D) (Fin D) ℂ) (0 : Matrix (Fin D) (Fin D) ℂ)
            (∑ i : Fin d, (B' i) * (B' i)ᴴ) := by
      -- Prove equality entrywise; explicitly push application through the sum.
      ext a b
      -- split into the four block cases
      rcases a with (a | a) <;> rcases b with (b | b)
      · -- (1,1) block
        -- push the entrywise application through the sum, then evaluate the block entry
        simp [Matrix.sum_apply, K, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose]
      · -- (1,2) block
        simp [Matrix.sum_apply, K, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose]
      · -- (2,1) block
        simp [Matrix.sum_apply, K, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose]
      · -- (2,2) block
        simp [Matrix.sum_apply, K, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose]
    calc
      (∑ i : Fin d, K i * (K i)ᴴ)
          = Matrix.fromBlocks (∑ i : Fin d, (A' i) * (A' i)ᴴ)
              (0 : Matrix (Fin D) (Fin D) ℂ) (0 : Matrix (Fin D) (Fin D) ℂ)
              (∑ i : Fin d, (B' i) * (B' i)ᴴ) := hsum
      _ = Matrix.fromBlocks (1 : Matrix (Fin D) (Fin D) ℂ) 0 0 (1 : Matrix (Fin D) (Fin D) ℂ) := by
        simp [hA'unital, hB'unital]
      _ = (1 : Matrix (Fin D ⊕ Fin D) (Fin D ⊕ Fin D) ℂ) := by
        simp
  have hEigM : Kraus.map K M = μ • M := by
    have hmap :
        Kraus.map K M =
          Matrix.fromBlocks (0 : Matrix (Fin D) (Fin D) ℂ)
            (∑ i : Fin d, A' i * X' * (B' i)ᴴ)
            (0 : Matrix (Fin D) (Fin D) ℂ)
            (0 : Matrix (Fin D) (Fin D) ℂ) := by
      ext a b
      rcases a with (a | a) <;> rcases b with (b | b)
      · -- (1,1) block
        simp [Kraus.map, K, M, Matrix.sum_apply,
          Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose, mul_assoc]
      · -- (1,2) block
        simp [Kraus.map, K, M, Matrix.sum_apply,
          Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose, mul_assoc]
      · -- (2,1) block
        simp [Kraus.map, K, M, Matrix.sum_apply,
          Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose, mul_assoc]
      · -- (2,2) block
        simp [Kraus.map, K, M, Matrix.sum_apply,
          Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose, mul_assoc]
    calc
      Kraus.map K M =
          Matrix.fromBlocks (0 : Matrix (Fin D) (Fin D) ℂ)
            (∑ i : Fin d, A' i * X' * (B' i)ᴴ)
            (0 : Matrix (Fin D) (Fin D) ℂ)
            (0 : Matrix (Fin D) (Fin D) ℂ) := hmap
      _ = Matrix.fromBlocks (0 : Matrix (Fin D) (Fin D) ℂ) (μ • X')
            (0 : Matrix (Fin D) (Fin D) ℂ)
            (0 : Matrix (Fin D) (Fin D) ℂ) := by
        simpa [mixedTransferMap_apply] using
          congrArg
            (fun Y : Matrix (Fin D) (Fin D) ℂ =>
              Matrix.fromBlocks
                (0 : Matrix (Fin D) (Fin D) ℂ)
                Y
                (0 : Matrix (Fin D) (Fin D) ℂ)
                (0 : Matrix (Fin D) (Fin D) ℂ))
            hFX'
      _ = μ • M := by
        simp [M, Matrix.fromBlocks_smul]
  -- Positive definite fixed point for the adjoint Kraus map.
  let rhoT : Matrix (Fin D ⊕ Fin D) (Fin D ⊕ Fin D) ℂ :=
    Matrix.fromBlocks (SAᴴ * SA) 0 0 (SBᴴ * SB)
  have hrhoT_pd : rhoT.PosDef := by
    let Sblock : Matrix (Fin D ⊕ Fin D) (Fin D ⊕ Fin D) ℂ :=
      Matrix.fromBlocks SA 0 0 SB
    let SblockInv : Matrix (Fin D ⊕ Fin D) (Fin D ⊕ Fin D) ℂ :=
      Matrix.fromBlocks SA⁻¹ 0 0 SB⁻¹
    have hSblock_unit : IsUnit Sblock := by
      refine (isUnit_iff_exists_inv).2 ?_
      refine ⟨SblockInv, ?_⟩
      simp [Sblock, SblockInv, Matrix.fromBlocks_multiply, hSA_mul_inv, hSB_mul_inv]
    have hrhoT_strict : IsStrictlyPositive rhoT := by
      refine (CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self).2 ?_
      refine ⟨Sblock, hSblock_unit, ?_⟩
      simp [rhoT, Sblock, Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
        Matrix.fromBlocks_multiply]
    exact (Matrix.IsStrictlyPositive.posDef hrhoT_strict)
  have hrhoT_fix : Kraus.adjointMap K rhoT = rhoT := by
    have hAblock : ∑ i : Fin d, (A' i)ᴴ * (SAᴴ * SA) * (A' i) = SAᴴ * SA := by
      have htermA : ∀ i : Fin d,
          (A' i)ᴴ * (SAᴴ * SA) * (A' i) = SAᴴ * ((A i)ᴴ * A i) * SA := by
        intro i
        -- Expand and cancel the gauge factors explicitly.
        -- We use `SA * SA⁻¹ = 1` and `(SAᴴ)⁻¹ * SAᴴ = 1`.
        -- First compute the adjoint of `A' i`.
        have hAstar : (A' i)ᴴ = SAᴴ * (A i)ᴴ * (SAᴴ)⁻¹ := by
          simp [A', Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, mul_assoc]
        -- Now expand and cancel.
        calc
          (A' i)ᴴ * (SAᴴ * SA) * (A' i)
              = (SAᴴ * (A i)ᴴ * (SAᴴ)⁻¹) * (SAᴴ * SA) * (SA⁻¹ * A i * SA) := by
                  -- make sure simp sees `(SA⁻¹)ᴴ = (SAᴴ)⁻¹`
                  simp [A', Matrix.conjTranspose_nonsing_inv, mul_assoc]
          _ = SAᴴ * ((A i)ᴴ * A i) * SA := by
                  -- cancel `(SAᴴ)⁻¹ * (SAᴴ * …)` and `SA * (SA⁻¹ * …)`
                  -- step 1: collapse the middle `(SAᴴ)⁻¹ * (SAᴴ * SA)` to `SA`
                  -- step 2: collapse `SA * (SA⁻¹ * (A i * SA))` to `A i * SA`

                  -- rewrite `(SAᴴ)⁻¹ * (SAᴴ * SA)`
                  have hmid : (SAᴴ)⁻¹ * (SAᴴ * SA) = SA :=
                    Matrix.nonsing_inv_mul_cancel_left SAᴴ SA hSAh_isUnitdet
                  -- rewrite `SA * (SA⁻¹ * (A i * SA))`
                  have hright : SA * (SA⁻¹ * (A i * SA)) = A i * SA := by
                    simpa using
                      Matrix.mul_nonsing_inv_cancel_left SA (A i * SA) hSA_isUnitdet
                  -- now finish by reassociation
                  -- (we keep it mostly in simp form after providing the two key rewrites)
                  simp [mul_assoc, hmid, hright]
      calc
        ∑ i : Fin d, (A' i)ᴴ * (SAᴴ * SA) * (A' i)
            = ∑ i : Fin d, SAᴴ * ((A i)ᴴ * A i) * SA := by
                simp [htermA]
        _ = SAᴴ * (∑ i : Fin d, (A i)ᴴ * A i) * SA := by
                simp [Matrix.sum_mul_mul
                    (L := SAᴴ) (M := fun i : Fin d => (A i)ᴴ * A i) (R := SA)]
        _ = SAᴴ * 1 * SA := by rw [hA_norm]
        _ = SAᴴ * SA := by simp
    have hBblock : ∑ i : Fin d, (B' i)ᴴ * (SBᴴ * SB) * (B' i) = SBᴴ * SB := by
      have htermB : ∀ i : Fin d,
          (B' i)ᴴ * (SBᴴ * SB) * (B' i) = SBᴴ * ((B i)ᴴ * B i) * SB := by
        intro i
        -- Same computation as `htermA`, but for `SB`.
        have hBstar : (B' i)ᴴ = SBᴴ * (B i)ᴴ * (SBᴴ)⁻¹ := by
          simp [B', Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, mul_assoc]
        calc
          (B' i)ᴴ * (SBᴴ * SB) * (B' i)
              = (SBᴴ * (B i)ᴴ * (SBᴴ)⁻¹) * (SBᴴ * SB) * (SB⁻¹ * B i * SB) := by
                  simp [B', Matrix.conjTranspose_nonsing_inv, mul_assoc]
          _ = SBᴴ * ((B i)ᴴ * B i) * SB := by
                  have hmid : (SBᴴ)⁻¹ * (SBᴴ * SB) = SB :=
                    Matrix.nonsing_inv_mul_cancel_left SBᴴ SB hSBh_isUnitdet
                  have hright : SB * (SB⁻¹ * (B i * SB)) = B i * SB := by
                    simpa using
                      Matrix.mul_nonsing_inv_cancel_left SB (B i * SB) hSB_isUnitdet
                  simp [mul_assoc, hmid, hright]
      calc
        ∑ i : Fin d, (B' i)ᴴ * (SBᴴ * SB) * (B' i)
            = ∑ i : Fin d, SBᴴ * ((B i)ᴴ * B i) * SB := by
                simp [htermB]
        _ = SBᴴ * (∑ i : Fin d, (B i)ᴴ * B i) * SB := by
                simp [Matrix.sum_mul_mul
                    (L := SBᴴ) (M := fun i : Fin d => (B i)ᴴ * B i) (R := SB)]
        _ = SBᴴ * 1 * SB := by rw [hB_norm]
        _ = SBᴴ * SB := by simp
    have hAdj :
        Kraus.adjointMap K rhoT =
          Matrix.fromBlocks (∑ i : Fin d, (A' i)ᴴ * (SAᴴ * SA) * (A' i))
            (0 : Matrix (Fin D) (Fin D) ℂ) (0 : Matrix (Fin D) (Fin D) ℂ)
            (∑ i : Fin d, (B' i)ᴴ * (SBᴴ * SB) * (B' i)) := by
      ext a b
      rcases a with (a | a) <;> rcases b with (b | b)
      · -- (1,1)
        simp [Kraus.adjointMap, K, rhoT, Matrix.sum_apply, Matrix.fromBlocks_multiply,
          Matrix.fromBlocks_conjTranspose, mul_assoc]
      · -- (1,2)
        simp [Kraus.adjointMap, K, rhoT, Matrix.sum_apply, Matrix.fromBlocks_multiply,
          Matrix.fromBlocks_conjTranspose, mul_assoc]
      · -- (2,1)
        simp [Kraus.adjointMap, K, rhoT, Matrix.sum_apply, Matrix.fromBlocks_multiply,
          Matrix.fromBlocks_conjTranspose, mul_assoc]
      · -- (2,2)
        simp [Kraus.adjointMap, K, rhoT, Matrix.sum_apply, Matrix.fromBlocks_multiply,
          Matrix.fromBlocks_conjTranspose, mul_assoc]
    calc
      Kraus.adjointMap K rhoT =
          Matrix.fromBlocks (∑ i : Fin d, (A' i)ᴴ * (SAᴴ * SA) * (A' i))
            (0 : Matrix (Fin D) (Fin D) ℂ) (0 : Matrix (Fin D) (Fin D) ℂ)
            (∑ i : Fin d, (B' i)ᴴ * (SBᴴ * SB) * (B' i)) := hAdj
      _ = Matrix.fromBlocks (SAᴴ * SA) 0 0 (SBᴴ * SB) := by
        simp [hAblock, hBblock]
      _ = rhoT := rfl
  -- Weighted KS equality gives multiplicative-domain commutation.
  have hKS_M :
      Kraus.map K (Mᴴ * M) = (Kraus.map K M)ᴴ * Kraus.map K M :=
    Kraus.ks_equality_of_peripheral_eigenvector_of_fixedPoint
      (K := K) hK_unital (ρ := rhoT) hrhoT_pd hrhoT_fix M μ hEigM hμ
  have hComm_M : ∀ i : Fin d, M * (K i)ᴴ = (K i)ᴴ * Kraus.map K M :=
    Kraus.kraus_commute_of_ks_equality (K := K) hK_unital M hKS_M
  have hInter1 : ∀ i : Fin d, X' * (B' i)ᴴ = μ • (A' i)ᴴ * X' := by
    intro i
    have h' : M * (K i)ᴴ = (K i)ᴴ * (μ • M) := by
      rw [hComm_M i, hEigM]
    have hL : M * (K i)ᴴ =
        Matrix.fromBlocks (0 : Matrix (Fin D) (Fin D) ℂ) (X' * (B' i)ᴴ)
          (0 : Matrix (Fin D) (Fin D) ℂ) (0 : Matrix (Fin D) (Fin D) ℂ) := by
      simp [M, K, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose]
    have hR : (K i)ᴴ * (μ • M) =
        Matrix.fromBlocks (0 : Matrix (Fin D) (Fin D) ℂ) (μ • ((A' i)ᴴ * X'))
          (0 : Matrix (Fin D) (Fin D) ℂ) (0 : Matrix (Fin D) (Fin D) ℂ) := by
      simp [M, K, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose,
        Matrix.fromBlocks_smul]
    have h_eq := hL ▸ hR ▸ h'
    rw [smul_mul_assoc]
    exact (Matrix.fromBlocks_inj.1 h_eq).2.1
  have hμ_conj : ‖(starRingEnd ℂ) μ‖ = 1 := by
    simpa [Complex.norm_conj] using hμ
  have hEigMstar : Kraus.map K Mᴴ = (starRingEnd ℂ μ) • Mᴴ := by
    calc
      Kraus.map K Mᴴ = (Kraus.map K M)ᴴ := by
        simpa using (Kraus.map_conjTranspose (K := K) M).symm
      _ = (μ • M)ᴴ := by
        rw [hEigM]
      _ = (starRingEnd ℂ μ) • Mᴴ := by
        simp
  have hKS_Mstar :
      Kraus.map K (Mᴴᴴ * Mᴴ) = (Kraus.map K Mᴴ)ᴴ * Kraus.map K Mᴴ :=
    Kraus.ks_equality_of_peripheral_eigenvector_of_fixedPoint
      (K := K) hK_unital (ρ := rhoT) hrhoT_pd hrhoT_fix Mᴴ (starRingEnd ℂ μ) hEigMstar hμ_conj
  have hComm_Mstar : ∀ i : Fin d, Mᴴ * (K i)ᴴ = (K i)ᴴ * Kraus.map K Mᴴ :=
    Kraus.kraus_commute_of_ks_equality (K := K) hK_unital Mᴴ hKS_Mstar
  have hInter2h : ∀ i : Fin d,
      X'ᴴ * (A' i)ᴴ = (starRingEnd ℂ μ) • ((B' i)ᴴ * X'ᴴ) := by
    intro i
    have h' : Mᴴ * (K i)ᴴ = (K i)ᴴ * ((starRingEnd ℂ μ) • Mᴴ) := by
      rw [hComm_Mstar i, hEigMstar]
    have hL : Mᴴ * (K i)ᴴ =
        Matrix.fromBlocks (0 : Matrix (Fin D) (Fin D) ℂ) (0 : Matrix (Fin D) (Fin D) ℂ)
          (X'ᴴ * (A' i)ᴴ) (0 : Matrix (Fin D) (Fin D) ℂ) := by
      simp [M, K, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose]
    have hR : (K i)ᴴ * ((starRingEnd ℂ μ) • Mᴴ) =
        Matrix.fromBlocks (0 : Matrix (Fin D) (Fin D) ℂ) (0 : Matrix (Fin D) (Fin D) ℂ)
          ((starRingEnd ℂ μ) • ((B' i)ᴴ * X'ᴴ)) (0 : Matrix (Fin D) (Fin D) ℂ) := by
      simp [M, K, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose,
        Matrix.fromBlocks_smul]
    have h_eq := hL ▸ hR ▸ h'
    exact (Matrix.fromBlocks_inj.1 h_eq).2.2.1
  have hInter2 : ∀ i : Fin d, A' i * X' = μ • X' * B' i := by
    intro i
    have h22 := congrArg Matrix.conjTranspose (hInter2h i)
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_smul, starRingEnd_apply, star_star] at h22
    simpa [smul_mul_assoc] using h22
  -- Kernel invariance under `(B' i)ᴴ`.
  have hker : ∀ k : Fin d, ∀ v, X' *ᵥ v = 0 → X' *ᵥ ((B' k)ᴴ *ᵥ v) = 0 := by
    intro k v hv
    have hmul : X' * (B' k)ᴴ = μ • (A' k)ᴴ * X' := hInter1 k
    have hmul2 : X' * (B' k)ᴴ = μ • ((A' k)ᴴ * X') := by rw [smul_mul_assoc] at hmul; exact hmul
    have h1 : X' *ᵥ ((B' k)ᴴ *ᵥ v) = (X' * (B' k)ᴴ) *ᵥ v := by
      simp [Matrix.mulVec_mulVec]
    rw [h1, hmul2, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, smul_zero]
  -- `B'` is injective: conjugation by an invertible matrix preserves spanning.
  have hB' : IsInjective B' := by
    -- Conjugation linear map ϕ(M) = SB⁻¹ M SB
    let φ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
      (LinearMap.mulLeft ℂ SB⁻¹).comp (LinearMap.mulRight ℂ SB)
    have hφ_surj : Function.Surjective φ := by
      intro N
      refine ⟨SB * N * SB⁻¹, ?_⟩
      simp only [φ, LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply,
        Matrix.mul_assoc]
      rw [Matrix.nonsing_inv_mul _ hSB_isUnitdet, mul_one,
        Matrix.nonsing_inv_mul_cancel_left _ _ hSB_isUnitdet]
    have hφ_range : φ.range = (⊤ : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ)) :=
      LinearMap.range_eq_top.2 hφ_surj
    have himage : (⇑φ '' Set.range B) = Set.range B' := by
      ext Y; constructor
      · rintro ⟨X0, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, by simp [B', φ, Matrix.mul_assoc]⟩
      · rintro ⟨i, rfl⟩
        refine ⟨B i, ⟨i, rfl⟩, by simp [B', φ, Matrix.mul_assoc]⟩
    -- Map the spanning statement through `φ`.
    have hmap :
        Submodule.map φ (Submodule.span ℂ (Set.range B)) =
          Submodule.span ℂ (Set.range B') := by
      -- `map_span` gives the RHS as `span (φ '' range B)`.
      simp [himage, Submodule.map_span]
    -- Now `span (range B') = map φ (span (range B)) = map φ ⊤ = φ.range = ⊤`.
    have : Submodule.span ℂ (Set.range B') = (⊤ : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ)) := by
      calc
        Submodule.span ℂ (Set.range B')
            = Submodule.map φ (Submodule.span ℂ (Set.range B)) := by
                simp [hmap]
        _ = Submodule.map φ ⊤ := by rw [hB]
        _ = φ.range := by simp [Submodule.map_top]
        _ = ⊤ := hφ_range
    exact this
  -- Kernel invariance under all matrices, hence `det X' ≠ 0`.
  have h_all :
      ∀ (M0 : Matrix (Fin D) (Fin D) ℂ) (v : Fin D → ℂ),
        X' *ᵥ v = 0 → X' *ᵥ (M0 *ᵥ v) = 0 :=
    ker_all_of_inj (B := B') hB' X' hker
  have hdetX' : X'.det ≠ 0 := det_ne_zero_of_ker_all (X := X') hX'ne h_all
  have hX'isUnitdet : IsUnit X'.det := Ne.isUnit hdetX'
  -- Per-index relation in the gauged setting.
  have hμ_ne0 : μ ≠ 0 := by
    intro h0
    have : (‖μ‖ : ℝ) = 0 := by simp [h0]
    linarith [hμ, this]
  have hper : ∀ i : Fin d, B' i = μ⁻¹ • (X'⁻¹ * A' i * X') := by
    intro i
    have hAX : A' i * X' = μ • X' * B' i := hInter2 i
    -- multiply on the left by `X'⁻¹`
    have : X'⁻¹ * (A' i * X') = X'⁻¹ * (μ • X' * B' i) := by simp [hAX]
    -- simplify
    have : X'⁻¹ * A' i * X' = μ • B' i := by
      -- reassociate and cancel `X'⁻¹ * X' = 1`
      rw [← Matrix.mul_assoc] at this
      rw [this, smul_mul_assoc, mul_smul_comm, Matrix.nonsing_inv_mul_cancel_left _ _ hX'isUnitdet]
    -- solve for `B' i`
    -- `μ ≠ 0` since `‖μ‖ = 1`
    have hμinv : μ⁻¹ * μ = (1 : ℂ) := by simp [hμ_ne0]
    -- multiply both sides by `μ⁻¹`
    calc
      B' i = μ⁻¹ • (μ • B' i) := by
        simp [smul_smul, hμinv]
      _ = μ⁻¹ • (X'⁻¹ * A' i * X') := by
        simp [this]
  -- Gauge back to the original tensors.
  let Ymat : Matrix (Fin D) (Fin D) ℂ := SB * X'⁻¹ * SA⁻¹
  let Yinv : Matrix (Fin D) (Fin D) ℂ := SA * X' * SB⁻¹
  have hYmul : Ymat * Yinv = 1 := by
    have h1 : SA⁻¹ * (SA * X' * SB⁻¹) = X' * SB⁻¹ := by
      rw [Matrix.mul_assoc SA X' SB⁻¹, Matrix.nonsing_inv_mul_cancel_left _ _ hSA_isUnitdet]
    have h2 : X'⁻¹ * (X' * SB⁻¹) = SB⁻¹ := by
      rw [Matrix.nonsing_inv_mul_cancel_left _ _ hX'isUnitdet]
    have h3 : SB * SB⁻¹ = 1 := by
      exact Matrix.mul_nonsing_inv _ hSB_isUnitdet
    calc Ymat * Yinv = SB * X'⁻¹ * SA⁻¹ * (SA * X' * SB⁻¹) := rfl
      _ = SB * X'⁻¹ * (SA⁻¹ * (SA * X' * SB⁻¹)) := by rw [Matrix.mul_assoc]
      _ = SB * X'⁻¹ * (X' * SB⁻¹) := by rw [h1]
      _ = SB * (X'⁻¹ * (X' * SB⁻¹)) := by rw [Matrix.mul_assoc]
      _ = SB * SB⁻¹ := by rw [h2]
      _ = 1 := h3
  have hYinv_mul : Yinv * Ymat = 1 := by
    have h1 : SB⁻¹ * (SB * X'⁻¹ * SA⁻¹) = X'⁻¹ * SA⁻¹ := by
      rw [Matrix.mul_assoc SB X'⁻¹ SA⁻¹, Matrix.nonsing_inv_mul_cancel_left _ _ hSB_isUnitdet]
    have h2 : X' * (X'⁻¹ * SA⁻¹) = SA⁻¹ := by
      rw [Matrix.mul_nonsing_inv_cancel_left _ _ hX'isUnitdet]
    have h3 : SA * SA⁻¹ = 1 := by
      exact Matrix.mul_nonsing_inv _ hSA_isUnitdet
    calc Yinv * Ymat = SA * X' * SB⁻¹ * (SB * X'⁻¹ * SA⁻¹) := rfl
      _ = SA * X' * (SB⁻¹ * (SB * X'⁻¹ * SA⁻¹)) := by rw [Matrix.mul_assoc]
      _ = SA * X' * (X'⁻¹ * SA⁻¹) := by rw [h1]
      _ = SA * (X' * (X'⁻¹ * SA⁻¹)) := by rw [Matrix.mul_assoc]
      _ = SA * SA⁻¹ := by rw [h2]
      _ = 1 := h3
  let Ygl : GL (Fin D) ℂ := ⟨Ymat, Yinv, hYmul, hYinv_mul⟩
  refine ⟨Ygl, μ⁻¹, inv_ne_zero (norm_ne_zero_iff.mp (by rw [hμ]; norm_num)), ?_⟩
  intro i
  -- Expand definitions and use the per-index relation for `B'`.
  have : B i = μ⁻¹ • (Ymat * A i * Yinv) := by
    -- From `hper i : B' i = μ⁻¹ • (X'⁻¹ * A' i * X')`
    -- We have `B' i = SB⁻¹ * B i * SB`, so `B i = SB * B' i * SB⁻¹`.
    have hBi : B i = SB * (B' i) * SB⁻¹ := by
      have : SB * (SB⁻¹ * B i * SB) * SB⁻¹ = B i := by
        simp only [Matrix.mul_assoc]
        rw [Matrix.mul_nonsing_inv _ hSB_isUnitdet, mul_one,
          Matrix.mul_nonsing_inv_cancel_left _ _ hSB_isUnitdet]
      exact this.symm
    rw [hBi, hper i]
    -- Now: SB * (μ⁻¹ • (X'⁻¹ * A' i * X')) * SB⁻¹ = μ⁻¹ • (Ymat * A i * Yinv)
    simp only [smul_mul_assoc, mul_smul_comm]
    congr 1
    -- Both sides are reassociations of SB * X'⁻¹ * SA⁻¹ * A i * SA * X' * SB⁻¹
    simp only [A', Ymat, Yinv, Matrix.mul_assoc]
  simpa [Ygl] using this

end

/-- **Eigenvalue rigidity** (Pérez-García et al. 2007, Lemma 5):
if the mixed transfer spectral radius is ≥ 1, then A and B are
gauge-phase equivalent. -/
theorem modulus_one_eigenvalue_implies_gauge
    (A B : MPSTensor d D)
    (hA : IsInjective A) (hB : IsInjective B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hsr : mixedTransferSpectralRadius A B ≥ 1) :
    GaugePhaseEquiv A B := by
  -- Edge case: D = 0
  rcases eq_or_ne D 0 with rfl | hD
  · -- For D = 0, all matrices are trivially equal; any GL element works
    exact ⟨1, 1, one_ne_zero, fun i => by ext a; exact a.elim0⟩
  haveI : NeZero D := ⟨hD⟩
  -- Step 1: Extract eigenvalue with |μ| = 1 and eigenvector X ≠ 0
  -- The spectral radius equals 1 (≥ 1 from hypothesis, ≤ 1 already proved)
  set V := Matrix (Fin D) (Fin D) ℂ
  let Φ : (V →ₗ[ℂ] V) ≃ₐ[ℂ] (V →L[ℂ] V) := Module.End.toContinuousLinearMap V
  let F' : V →L[ℂ] V := Φ (mixedTransferMap A B)
  haveI : Nontrivial V := by
    haveI : Nonempty (Fin D) := ⟨⟨0, NeZero.pos D⟩⟩
    exact Matrix.nonempty
  haveI : Nontrivial (V →L[ℂ] V) := ContinuousLinearMap.instNontrivialId
  -- Spectral radius is achieved
  obtain ⟨μ, hμ_spec, hμ_norm⟩ := spectrum.exists_nnnorm_eq_spectralRadius F'
  -- Transfer to eigenvalue of the linear map
  have h_spec_eq := AlgEquiv.spectrum_eq Φ (mixedTransferMap A B)
  have hμ_spec_end : μ ∈ spectrum ℂ (mixedTransferMap A B) := h_spec_eq ▸ hμ_spec
  have hμ_ev : Module.End.HasEigenvalue (mixedTransferMap A B) μ :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμ_spec_end
  obtain ⟨X, hX_mem, hX_ne⟩ := hμ_ev.exists_hasEigenvector
  have hFX : mixedTransferMap A B X = μ • X := Module.End.mem_eigenspace_iff.mp hX_mem
  -- Step 2: Show |μ| = 1
  have hμ_le : ‖μ‖ ≤ 1 := eigenvalue_norm_le_one A B hA_norm hB_norm μ hμ_ev
  have hμ_ge : (1 : ℝ≥0∞) ≤ ‖μ‖₊ := by rw [hμ_norm]; exact hsr
  have hμ_eq : ‖μ‖ = 1 := le_antisymm hμ_le (by
    rw [ENNReal.one_le_coe_iff] at hμ_ge; exact_mod_cast hμ_ge)
  -- Step 3: Apply the core algebraic lemma
  exact eigenvector_gives_gauge A B X μ hA hB hA_norm hB_norm hFX hμ_eq hX_ne

/-- **Spectral gap for distinct blocks**: `ρ(F_{AB}) < 1` when `A ≇ B`. -/
theorem spectralRadius_mixedTransfer_lt_one
    (A B : MPSTensor d D)
    (hA : IsInjective A) (hB : IsInjective B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hAB : ¬ GaugePhaseEquiv A B) :
    mixedTransferSpectralRadius A B < 1 :=
  lt_of_le_of_ne (spectralRadius_mixedTransfer_le_one A B hA_norm hB_norm)
    fun h => hAB (modulus_one_eigenvalue_implies_gauge A B hA hB hA_norm hB_norm h.ge)

/-! ### Power convergence from spectral radius bound -/

/-- **Powers tend to zero when spectral radius < 1.** -/
theorem pow_tendsto_zero_of_spectralRadius_lt_one
    {A : Type*} [NormedRing A] [CompleteSpace A] [NormedAlgebra ℂ A]
    (a : A) (h : spectralRadius ℂ a < 1) :
    Filter.Tendsto (fun n => a ^ n) Filter.atTop (nhds 0) := by
  obtain ⟨r, hr_above, hr_below⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
  have hr_lt_one : r < 1 := ENNReal.coe_lt_coe.mp (by rwa [ENNReal.coe_one])
  have hev2 : ∀ᶠ n in Filter.atTop, ‖a ^ n‖₊ < r ^ n := by
    have gelfand := spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius a
    filter_upwards [gelfand.eventually (eventually_lt_nhds hr_above),
      Filter.eventually_gt_atTop 0] with n hn hn_pos
    rw [one_div, ENNReal.rpow_inv_lt_iff (Nat.cast_pos.mpr hn_pos)] at hn
    rw [ENNReal.rpow_natCast] at hn
    exact_mod_cast hn
  apply squeeze_zero_norm' (a := fun n => (r : ℝ) ^ n)
  · filter_upwards [hev2] with n hn
    rw [← coe_nnnorm, ← NNReal.coe_pow]; exact_mod_cast hn.le
  · exact tendsto_pow_atTop_nhds_zero_of_lt_one r.coe_nonneg (by exact_mod_cast hr_lt_one)

/-! ### Application to mixed transfer convergence -/

/-- **Mixed transfer iterates decay for distinct blocks**: `F_{AB}^n(X) → 0`. -/
theorem mixedTransfer_pow_tendsto_zero
    (A B : MPSTensor d D)
    (hA : IsInjective A) (hB : IsInjective B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hAB : ¬ GaugePhaseEquiv A B)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    Filter.Tendsto (fun n => ((mixedTransferMap A B) ^ n) X)
      Filter.atTop (nhds 0) := by
  let V := Matrix (Fin D) (Fin D) ℂ
  let Φ : (V →ₗ[ℂ] V) ≃ₐ[ℂ] (V →L[ℂ] V) := Module.End.toContinuousLinearMap V
  let F' : V →L[ℂ] V := Φ (mixedTransferMap A B)
  have h_clm : Filter.Tendsto (fun n => F' ^ n) Filter.atTop (nhds 0) :=
    pow_tendsto_zero_of_spectralRadius_lt_one F'
      (spectralRadius_mixedTransfer_lt_one A B hA hB hA_norm hB_norm hAB)
  have h_eval := (ContinuousLinearMap.apply ℂ V X).continuous.tendsto (0 : V →L[ℂ] V)
  rw [map_zero] at h_eval
  suffices ∀ n, ((mixedTransferMap A B) ^ n) X = (F' ^ n) X by
    simp_rw [this]; exact h_eval.comp h_clm
  intro n
  have h_pow : F' ^ n = Φ ((mixedTransferMap A B) ^ n) := (map_pow Φ _ n).symm
  simp only [h_pow]; rfl

end SpectralConvergence

end MPSTensor

/-! ## Uniform spectral gap from finite eigenvalue set -/

/-- **Uniform spectral gap from finitely many eigenvalues with modulus < 1.**

If an endomorphism has finitely many eigenvalues, and every eigenvalue `μ ≠ 1` satisfies
`‖μ‖ < 1`, then there exists a uniform gap `δ > 0` such that `‖μ‖ ≤ 1 - δ` for all
non-unit eigenvalues. This is a general finite-dimensional argument via `Finset.max'`. -/
theorem uniform_spectral_gap_of_finite_lt_one
    {K V : Type*} [NormedField K] [AddCommGroup V] [Module K V]
    {E : V →ₗ[K] V}
    (hfin : Set.Finite {μ : K | Module.End.HasEigenvalue E μ})
    (hlt : ∀ μ, Module.End.HasEigenvalue E μ → μ ≠ 1 → ‖μ‖ < 1) :
    ∃ δ > 0, ∀ μ, Module.End.HasEigenvalue E μ → μ ≠ 1 → ‖μ‖ ≤ 1 - δ := by
  classical
  let S := {μ : K | Module.End.HasEigenvalue E μ ∧ μ ≠ 1}
  have hSfin : S.Finite := hfin.subset fun μ hμ => hμ.1
  by_cases hS : S.Nonempty
  · -- Nonempty: take δ = 1 - max{‖μ‖ | μ ∈ S}
    let norms := hSfin.toFinset.image (fun μ => ‖μ‖)
    have hnorms_ne : norms.Nonempty := by
      obtain ⟨μ₀, hμ₀⟩ := hS
      exact ⟨‖μ₀‖, Finset.mem_image.mpr ⟨μ₀, hSfin.mem_toFinset.mpr hμ₀, rfl⟩⟩
    set r := norms.max' hnorms_ne with r_def
    have hr_lt : r < 1 := by
      rw [r_def, Finset.max'_lt_iff]
      intro x hx
      obtain ⟨μ, hμS, rfl⟩ := Finset.mem_image.mp hx
      exact hlt μ (hSfin.mem_toFinset.mp hμS).1 (hSfin.mem_toFinset.mp hμS).2
    refine ⟨1 - r, by linarith, fun μ hμ hne => ?_⟩
    have hμS : μ ∈ S := ⟨hμ, hne⟩
    have hμ_norm_mem : ‖μ‖ ∈ norms :=
      Finset.mem_image.mpr ⟨μ, hSfin.mem_toFinset.mpr hμS, rfl⟩
    linarith [Finset.le_max' norms ‖μ‖ hμ_norm_mem]
  · -- Empty: no non-1 eigenvalues, δ = 1 works vacuously
    exact ⟨1, one_pos, fun μ hμ hne => absurd ⟨μ, hμ, hne⟩ hS⟩
