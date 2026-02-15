/-
Scratch file: proving nnnorm_pow_mixedTransferCLM_bounded
Strategy: entry-wise bound via Cauchy-Schwarz on word sums
-/
import MPSLean.MPS.QuantumPerronFrobenius
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped Matrix ComplexOrder BigOperators NNReal ENNReal

namespace MPSTensor

variable {d D : ℕ}

-- Install linftyOp instances locally
noncomputable scoped instance : NormedRing (Matrix (Fin D) (Fin D) ℂ) :=
  Matrix.linftyOpNormedRing
noncomputable scoped instance : NormedAlgebra ℂ (Matrix (Fin D) (Fin D) ℂ) :=
  Matrix.linftyOpNormedAlgebra

-- ============================================================
-- Helper: PSD diagonal entry ≤ trace
-- ============================================================

-- For a PSD matrix P, each diagonal entry is nonneg and ≤ trace
lemma PosSemidef.diag_le_trace {P : Matrix (Fin D) (Fin D) ℂ}
    (hP : P.PosSemidef) (i : Fin D) :
    (P.diag i).re ≤ P.trace.re := by
  -- P.diag i = P i i, and trace = ∑ P j j
  -- Since P is PSD, each P j j has nonneg real part
  -- So P i i . re ≤ ∑ j, (P j j).re = trace.re
  have h_diag_nonneg : ∀ j, 0 ≤ (P j j).re := fun j => by
    have := hP.apply_eq_inner_conjTranspose (EuclideanSpace.single j 1)
    simp [Matrix.IsHermitian.apply_re_eq_inner hP.isHermitian] at this ⊢
    sorry -- TODO: diagonal of PSD is nonneg
  rw [Matrix.trace, Matrix.diag]
  simp only [Complex.re_sum]
  exact Finset.single_le_sum (fun j _ => h_diag_nonneg j) (Finset.mem_univ i)

-- ============================================================
-- Helper: trace-preserving under iteration
-- ============================================================

-- The transfer map preserves trace when ∑ A_i† A_i = I
lemma trace_transferMap_eq (A : MPSTensor d D)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1) (X : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.trace (transferMap (d := d) (D := D) A X) = Matrix.trace X :=
  (transferMap_isChannel A hA_norm).tp X

-- Trace is preserved under iteration
lemma trace_transferMap_pow_eq (A : MPSTensor d D)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (X : Matrix (Fin D) (Fin D) ℂ) (n : ℕ) :
    Matrix.trace ((transferMap (d := d) (D := D) A ^ n) X) = Matrix.trace X := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change Matrix.trace (transferMap A ((transferMap A ^ n) X)) = _
    rw [trace_transferMap_eq A hA_norm, ih]

-- ============================================================
-- Helper: PSD preserved under transfer map iteration
-- ============================================================

lemma posSemidef_transferMap_pow (A : MPSTensor d D)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : X.PosSemidef) (n : ℕ) :
    ((transferMap (d := d) (D := D) A ^ n) X).PosSemidef := by
  induction n with
  | zero => simpa
  | succ n ih =>
    rw [pow_succ']
    change (transferMap A ((transferMap A ^ n) X)).PosSemidef
    exact (transferMap_isChannel A hA_norm).pos _ ih

-- ============================================================
-- Helper: stdBasisMatrix is PSD
-- ============================================================

lemma stdBasisMatrix_posSemidef (k : Fin D) :
    (Matrix.stdBasisMatrix k k (1 : ℂ)).PosSemidef := by
  constructor
  · -- Hermitian
    ext i j
    simp [Matrix.stdBasisMatrix, Matrix.IsHermitian]
    intro hij
    by_cases hi : i = k <;> by_cases hj : j = k <;> simp_all
  · -- ⟨v, P v⟩ ≥ 0
    intro v
    simp [Matrix.dotProduct, Matrix.mulVec, Matrix.stdBasisMatrix]
    sorry  -- show ∑ i, star (v i) * (if i = k then v k else 0) = ‖v k‖² ≥ 0

-- ============================================================
-- Helper: trace of stdBasisMatrix
-- ============================================================

lemma trace_stdBasisMatrix (k : Fin D) :
    Matrix.trace (Matrix.stdBasisMatrix k k (1 : ℂ)) = 1 := by
  simp [Matrix.trace, Matrix.diag, Matrix.stdBasisMatrix]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ k) h

-- ============================================================
-- Core bound: ∑_σ |w_A(σ)_{ak}|² ≤ 1
-- ============================================================

-- This is the entry (a,a) of E_A^n(|ek⟩⟨ek|), which is PSD with trace 1.
-- So each diagonal entry is ≤ 1.
lemma word_entry_sq_sum_le_one (A : MPSTensor d D)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1) (n : ℕ)
    (a k : Fin D) :
    ∑ σ : Fin n → Fin d,
      ‖(evalWord A (List.ofFn σ) : Matrix (Fin D) (Fin D) ℂ) a k‖₊ ^ 2 ≤ 1 := by
  -- Relate to E_A^n(stdBasisMatrix k k 1) at entry (a,a)
  -- Using transferMap_pow_apply' (self-transfer iteration formula)
  sorry

-- ============================================================
-- Core: entry bound for mixed transfer
-- ============================================================

-- For each entry (a,b) of F^n(X): |[F^n(X)]_{ab}| ≤ entryL1NNNorm X
-- where entryL1NNNorm X = ∑_{kl} |X_{kl}|.
--
-- Proof sketch:
-- [F^n(X)]_{ab} = ∑_σ [w_A(σ) X w_B(σ)†]_{ab}
-- = ∑_σ ∑_k ∑_l w_A(σ)_{ak} X_{kl} conj(w_B(σ)_{bl})
-- |[F^n(X)]_{ab}| ≤ ∑_k ∑_l |X_{kl}| ∑_σ |w_A(σ)_{ak}| |w_B(σ)_{bl}|
-- By AM-GM: |a||b| ≤ (|a|² + |b|²)/2
-- ∑_σ |w_A(σ)_{ak}| |w_B(σ)_{bl}| ≤ (∑_σ |w_A(σ)_{ak}|² + ∑_σ |w_B(σ)_{bl}|²)/2 ≤ 1
-- So |[F^n(X)]_{ab}| ≤ ∑_k ∑_l |X_{kl}| = entryL1NNNorm X.

noncomputable def entryL1NNNorm (M : Matrix (Fin D) (Fin D) ℂ) : ℝ≥0 :=
  ∑ i : Fin D, ∑ j : Fin D, ‖M i j‖₊

lemma entryL1NNNorm_le_D_mul_nnnorm (M : Matrix (Fin D) (Fin D) ℂ) :
    entryL1NNNorm M ≤ D * ‖M‖₊ := by
  unfold entryL1NNNorm
  rw [Matrix.linfty_opNNNorm_def]
  calc ∑ i, ∑ j, ‖M i j‖₊
      ≤ ∑ _i : Fin D, (Finset.univ.sup fun i => ∑ j, ‖M i j‖₊) := by
        gcongr with i; exact Finset.le_sup (Finset.mem_univ i)
    _ = D * (Finset.univ.sup fun i => ∑ j, ‖M i j‖₊) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

lemma linftyOp_nnnorm_le_D_mul_maxEntry {K : ℝ≥0}
    (M : Matrix (Fin D) (Fin D) ℂ)
    (h : ∀ i j : Fin D, ‖M i j‖₊ ≤ K) :
    ‖M‖₊ ≤ D * K := by
  rw [Matrix.linfty_opNNNorm_def]
  apply Finset.sup_le
  intro i _
  calc ∑ j, ‖M i j‖₊ ≤ ∑ _j : Fin D, K := Finset.sum_le_sum (fun j _ => h i j)
    _ = D * K := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

private lemma entry_bound_of_mixedTransfer_pow [NeZero D]
    (A B : MPSTensor d D)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (X : Matrix (Fin D) (Fin D) ℂ) (n : ℕ)
    (a b : Fin D) :
    ‖(((mixedTransferMap A B) ^ n) X) a b‖₊ ≤ entryL1NNNorm X := by
  -- Expand using mixedTransferMap_pow_apply
  rw [mixedTransferMap_pow_apply]
  -- Goal: ‖(∑ σ, evalWord A σ * X * (evalWord B σ)ᴴ) a b‖₊ ≤ entryL1NNNorm X
  sorry

-- Main result
private lemma nnnorm_pow_mixedTransferCLM_bounded' [NeZero D]
    (A B : MPSTensor d D)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1) :
    ∃ C : ℝ≥0, ∀ n : ℕ,
      ‖((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
          (mixedTransferMap A B)) ^ n‖₊ ≤ C := by
  use (D : ℝ≥0) ^ 2
  intro n
  have h_eq : ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
      (mixedTransferMap A B)) ^ n =
    (Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
      ((mixedTransferMap A B) ^ n) := by rw [map_pow]
  rw [h_eq, ContinuousLinearMap.opNNNorm_le_iff]
  intro X
  calc ‖(Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)
          ((mixedTransferMap A B) ^ n)) X‖₊
      = ‖((mixedTransferMap A B) ^ n) X‖₊ := by rfl
    _ ≤ D * entryL1NNNorm X := by
        apply linftyOp_nnnorm_le_D_mul_maxEntry
        intro a b
        exact entry_bound_of_mixedTransfer_pow A B hA_norm hB_norm X n a b
    _ ≤ D * (D * ‖X‖₊) := by
        gcongr; exact entryL1NNNorm_le_D_mul_nnnorm X
    _ = (D : ℝ≥0) ^ 2 * ‖X‖₊ := by ring

end MPSTensor
