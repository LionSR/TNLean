/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ListProduct
import TNLean.MPS.Chain.OneSidedInverse
import TNLean.MPS.Core.Blocking
import TNLean.MPS.Core.TracePairing
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# The mixed-bond cross matrix in the MPS reduction proof

This file formalizes the algebra before the Jordan--Chevalley step in the proof
of Proposition 20 of Molnár--Ge--Schuch--Cirac.  For an injective blocked target
`A`, its coefficient-dual inverse `C` is chosen from `Kraus.decompositionMap`.
For a blocked source `B`, the paper's matrix is literally

\[
  K=\sum_i B^i\otimes(C^i)^T.
\]

The ordinary transpose and the reversal of the `C` word in powers of `K` are
load-bearing.  No conjugate transpose or same-bond Fundamental Theorem is used.

Source: arXiv:1706.07329v2, proof of Proposition 20,
`cornerproblem.tex` lines 3815--3866 and 3866--3936.

**Scope restriction (equality-only local fix):** The trace-power and source
open-boundary results below assume `SameMPV₂Pos`, so they treat the `λ = 1`
specialization of the proportional premise printed in Proposition 20.  The
unscaled conclusion is false for unrestricted `λ ≠ 1`; see
`docs/paper-gaps/mgsc18_reduction_proportionality_scalar.tex`.
-/

open scoped Matrix Kronecker BigOperators

namespace MPSTensor

variable {d D_A D_B : ℕ}

/-- The coefficient-dual inverse tensor of an injective target tensor.
Its upper virtual indices are ordered so that
`coefficientDualInverse A hA i a' a` is the coefficient of `A i` in the
chosen expansion of the matrix unit `|a⟩⟨a'|`.

Source: the left inverse \(\widetilde A^{-1}\) in arXiv:1706.07329v2,
`cornerproblem.tex` lines 3817--3823. -/
noncomputable def coefficientDualInverse (A : MPSTensor d D_A)
    (hA : Kraus.IsInjective A) : MPSTensor d D_A :=
  fun i a' a =>
    Kraus.decompositionMap (A := A) hA (Matrix.single a a' (1 : ℂ)) i

/-- Exact matrix-unit coefficient identity for the chosen dual inverse:
\[
  \sum_i A^i_{xy} C^i_{a'a}=\delta_{x,a}\delta_{y,a'}.
\]
The reversed pair `(a',a)` is the upper-leg convention in the source diagram.

Source: arXiv:1706.07329v2, `cornerproblem.tex` lines 3817--3823. -/
theorem coefficientDualInverse_sum_entry (A : MPSTensor d D_A)
    (hA : Kraus.IsInjective A) (x y a a' : Fin D_A) :
    ∑ i : Fin d, A i x y * coefficientDualInverse A hA i a' a =
      (if x = a then 1 else 0) * (if y = a' then 1 else 0) := by
  calc
    ∑ i : Fin d, A i x y * coefficientDualInverse A hA i a' a =
        ∑ i : Fin d, coefficientDualInverse A hA i a' a * A i x y := by
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_comm]
    _ = (∑ i : Fin d,
          Kraus.decompositionMap (A := A) hA (Matrix.single a a' (1 : ℂ)) i • A i) x y := by
      simp only [coefficientDualInverse, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    _ = Matrix.single a a' (1 : ℂ) x y := by
      rw [Kraus.decompositionMap_sum]
    _ = (if x = a then 1 else 0) * (if y = a' then 1 else 0) := by
      simp only [Matrix.single_apply]
      split_ifs <;> simp_all

/-- The source reduction cross matrix
`K = ∑ i, B i ⊗ (C i)ᵀ`, on the genuinely mixed bond index
`Fin D_B × Fin D_A`.

Source: arXiv:1706.07329v2, `cornerproblem.tex` lines 3824--3838. -/
noncomputable def reductionCrossMatrix (B : MPSTensor d D_B)
    (C : MPSTensor d D_A) :
    Matrix (Fin D_B × Fin D_A) (Fin D_B × Fin D_A) ℂ :=
  ∑ i : Fin d, B i ⊗ₖ (C i)ᵀ

/-- Exact entry formula for the reduction cross matrix.  In particular, the
upper inverse-tensor entry is `C i a' a`, not a conjugated entry.

Source: arXiv:1706.07329v2, `cornerproblem.tex` lines 3824--3838. -/
@[simp] theorem reductionCrossMatrix_apply (B : MPSTensor d D_B)
    (C : MPSTensor d D_A) (b b' : Fin D_B) (a a' : Fin D_A) :
    reductionCrossMatrix B C (b, a) (b', a') =
      ∑ i : Fin d, B i b b' * C i a' a := by
  simp only [reductionCrossMatrix, Matrix.sum_apply,
    Matrix.kroneckerMap_apply, Matrix.transpose_apply]

private theorem listProd_kronecker_transpose
    (B : MPSTensor d D_B) (C : MPSTensor d D_A) (w : List (Fin d)) :
    (w.map fun i => B i ⊗ₖ (C i)ᵀ).prod =
      Kraus.evalWord B w ⊗ₖ (Kraus.evalWord C w.reverse)ᵀ := by
  have hprod :
      (w.map fun i => B i ⊗ₖ (C i)ᵀ).prod =
        Kraus.evalWord B w ⊗ₖ Kraus.evalWord (fun i => (C i)ᵀ) w := by
    induction w with
    | nil => simp [Kraus.evalWord]
    | cons i w ih =>
        simp only [List.map_cons, List.prod_cons, Kraus.evalWord_cons, ih]
        exact (Matrix.mul_kronecker_mul (B i) (Kraus.evalWord B w)
          (C i)ᵀ (Kraus.evalWord (fun j => (C j)ᵀ) w)).symm
  rw [hprod]
  congr 1
  simpa using (Kraus.evalWord_transpose C w.reverse).symm

private theorem sum_family_pow_eq_sum_listProd
    {m : Type*} [Fintype m] [DecidableEq m]
    (F : Fin d → Matrix m m ℂ) (n : ℕ) :
    (∑ i : Fin d, F i) ^ n =
      ∑ σ : Fin n → Fin d, (List.ofFn fun k => F (σ k)).prod := by
  rw [← List.prod_replicate, ← List.ofFn_const]
  exact List.prod_ofFn_sum (fun _ : Fin n => F)

/-- Power expansion of the mixed-bond cross matrix.  The theorem freezes the
source orientation explicitly: the lower `B` word is in site order while the
upper `C` word is reversed before taking its ordinary transpose.

Source: arXiv:1706.07329v2, `cornerproblem.tex` lines 3839--3865. -/
theorem reductionCrossMatrix_pow_eq_sum (B : MPSTensor d D_B)
    (C : MPSTensor d D_A) (n : ℕ) :
    reductionCrossMatrix B C ^ n =
      ∑ σ : Fin n → Fin d,
        Kraus.evalWord B (List.ofFn σ) ⊗ₖ
          (Kraus.evalWord C (List.ofFn σ).reverse)ᵀ := by
  rw [reductionCrossMatrix, sum_family_pow_eq_sum_listProd]
  apply Finset.sum_congr rfl
  intro σ _
  simpa only [List.map_ofFn, Function.comp_def] using
    listProd_kronecker_transpose B C (List.ofFn σ)

/-- Entrywise power formula, with the source's reversed upper-leg order
visible in the statement.

Source: arXiv:1706.07329v2, `cornerproblem.tex` lines 3839--3865. -/
theorem reductionCrossMatrix_pow_apply (B : MPSTensor d D_B)
    (C : MPSTensor d D_A) (n : ℕ)
    (b b' : Fin D_B) (a a' : Fin D_A) :
    (reductionCrossMatrix B C ^ n) (b, a) (b', a') =
      ∑ σ : Fin n → Fin d,
        Kraus.evalWord B (List.ofFn σ) b b' *
          Kraus.evalWord C (List.ofFn σ).reverse a' a := by
  have h := congrArg
    (fun M : Matrix (Fin D_B × Fin D_A) (Fin D_B × Fin D_A) ℂ =>
      M (b, a) (b', a'))
    (reductionCrossMatrix_pow_eq_sum B C n)
  simpa only [Matrix.sum_apply, Matrix.kroneckerMap_apply,
    Matrix.transpose_apply] using h

private def diagonalBondVector (D : ℕ) : Fin D × Fin D → ℂ :=
  fun p => if p.1 = p.2 then 1 else 0

private theorem diagonalBondVector_dotProduct (D : ℕ) :
    diagonalBondVector D ⬝ᵥ diagonalBondVector D = (D : ℂ) := by
  classical
  rw [dotProduct, Fintype.sum_prod_type]
  simp [diagonalBondVector]

/-- Pairing an injective tensor with its coefficient dual gives the rank-one
matrix supported on equal lower/upper bond indices.

Source: arXiv:1706.07329v2, `cornerproblem.tex` lines 3817--3838. -/
theorem reductionCrossMatrix_coefficientDualInverse
    (A : MPSTensor d D_A) (hA : Kraus.IsInjective A) :
    reductionCrossMatrix A (coefficientDualInverse A hA) =
      Matrix.vecMulVec (diagonalBondVector D_A) (diagonalBondVector D_A) := by
  ext p q
  rcases p with ⟨x, a⟩
  rcases q with ⟨y, a'⟩
  rw [reductionCrossMatrix_apply, coefficientDualInverse_sum_entry]
  simp [Matrix.vecMulVec_apply, diagonalBondVector]

private theorem coefficientDualCross_pow
    (A : MPSTensor d D_A) (hA : Kraus.IsInjective A)
    (n : ℕ) (hn : 0 < n) :
    reductionCrossMatrix A (coefficientDualInverse A hA) ^ n =
      ((D_A : ℂ) ^ (n - 1)) •
        reductionCrossMatrix A (coefficientDualInverse A hA) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ih (Nat.zero_lt_succ k), Matrix.smul_mul,
        reductionCrossMatrix_coefficientDualInverse,
        Matrix.vecMulVec_mul_vecMulVec, diagonalBondVector_dotProduct]
      ext p q
      simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
      rw [Nat.succ_sub (Nat.zero_lt_succ k), pow_succ]
      ring

/-- Under positive-length MPV equality, the trace of every positive power of
the source cross matrix is exactly `(D_A : ℂ)^n`.

This is the algebraic form of the closed diagram at
`cornerproblem.tex` lines 3839--3865. -/
theorem trace_reductionCrossMatrix_pow_of_sameMPV₂Pos
    (A : MPSTensor d D_A) (B : MPSTensor d D_B)
    (hA : Kraus.IsInjective A) (hSame : SameMPV₂Pos B A)
    (n : ℕ) (hn : 0 < n) :
    Matrix.trace (reductionCrossMatrix B (coefficientDualInverse A hA) ^ n) =
      (D_A : ℂ) ^ n := by
  rw [reductionCrossMatrix_pow_eq_sum, Matrix.trace_sum]
  simp_rw [Matrix.trace_kronecker, Matrix.trace_transpose]
  have hword (σ : Fin n → Fin d) :
      Matrix.trace (Kraus.evalWord B (List.ofFn σ)) =
        Matrix.trace (Kraus.evalWord A (List.ofFn σ)) := by
    exact hSame.trace_evalWord (List.ofFn σ) (by
      intro hnil
      exact (Nat.ne_of_gt hn) (List.ofFn_eq_nil_iff.mp hnil))
  simp_rw [hword]
  change (∑ σ : Fin n → Fin d,
      Matrix.trace (Kraus.evalWord A (List.ofFn σ)) *
        Matrix.trace
          (Kraus.evalWord (coefficientDualInverse A hA) (List.ofFn σ).reverse)) = _
  calc
    _ = Matrix.trace
        (reductionCrossMatrix A (coefficientDualInverse A hA) ^ n) := by
      rw [reductionCrossMatrix_pow_eq_sum, Matrix.trace_sum]
      simp only [Matrix.trace_kronecker, Matrix.trace_transpose]
    _ = _ := by
      rw [coefficientDualCross_pow A hA n hn, Matrix.trace_smul,
        reductionCrossMatrix_coefficientDualInverse,
        Matrix.trace_vecMulVec, diagonalBondVector_dotProduct]
      change (D_A : ℂ) ^ (n - 1) * (D_A : ℂ) = (D_A : ℂ) ^ n
      rw [← pow_succ,
        Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn))]

/-- The source open-boundary contraction with an arbitrary lower tail matrix.
This form permits the inverse sites to be blocked while the tail remains an
unblocked word, as in `cornerproblem.tex` lines 3866--3887. -/
noncomputable def reductionOpenBoundaryMatrixContraction
    (B : MPSTensor d D_B) (C : MPSTensor d D_A)
    (n : ℕ) (X : Matrix (Fin D_B) (Fin D_B) ℂ) (a' a : Fin D_A) : ℂ :=
  ∑ σ : Fin n → Fin d,
    Matrix.trace (Kraus.evalWord B (List.ofFn σ) * X) *
      Kraus.evalWord C (List.ofFn σ).reverse a' a

/-- The same-alphabet specialization whose lower tail is the word `B^w`. -/
noncomputable def reductionOpenBoundaryContraction
    (B : MPSTensor d D_B) (C : MPSTensor d D_A)
    (n : ℕ) (w : List (Fin d)) (a' a : Fin D_A) : ℂ :=
  reductionOpenBoundaryMatrixContraction B C n (Kraus.evalWord B w) a' a

private theorem trace_mul_eq_sum_entries {D : ℕ}
    (M X : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.trace (M * X) = ∑ x : Fin D, ∑ y : Fin D, M x y * X y x := by
  rw [Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_apply]

/-- The open-boundary matrix contraction is the pairing of the boundary matrix
`X` with the corresponding entries of the cross-matrix power.  This is the
exact cross-sum expansion used before the rank-one reduction in the source's
open padded contraction.

Source: arXiv:1706.07329v2, `cornerproblem.tex` lines 3866--3887. -/
theorem reductionOpenBoundaryMatrixContraction_eq_cross_sum
    (B : MPSTensor d D_B) (C : MPSTensor d D_A)
    (n : ℕ) (X : Matrix (Fin D_B) (Fin D_B) ℂ) (a' a : Fin D_A) :
    reductionOpenBoundaryMatrixContraction B C n X a' a =
      ∑ x : Fin D_B, ∑ y : Fin D_B,
        (reductionCrossMatrix B C ^ n) (x, a) (y, a') * X y x := by
  classical
  simp only [reductionOpenBoundaryMatrixContraction]
  simp_rw [trace_mul_eq_sum_entries]
  simp_rw [reductionCrossMatrix_pow_apply]
  have hleft (σ : Fin n → Fin d) :
      (∑ x : Fin D_B, ∑ y : Fin D_B,
          Kraus.evalWord B (List.ofFn σ) x y * X y x) *
          Kraus.evalWord C (List.ofFn σ).reverse a' a =
        ∑ x : Fin D_B, ∑ y : Fin D_B,
          (Kraus.evalWord B (List.ofFn σ) x y * X y x) *
            Kraus.evalWord C (List.ofFn σ).reverse a' a := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_mul]
  have hright (x y : Fin D_B) :
      (∑ σ : Fin n → Fin d,
          Kraus.evalWord B (List.ofFn σ) x y *
            Kraus.evalWord C (List.ofFn σ).reverse a' a) * X y x =
        ∑ σ : Fin n → Fin d,
          (Kraus.evalWord B (List.ofFn σ) x y *
            Kraus.evalWord C (List.ofFn σ).reverse a' a) * X y x := by
    rw [Finset.sum_mul]
  simp_rw [hleft, hright]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro σ _
  ring

/-- Exact target evaluation with an arbitrary lower tail matrix. -/
theorem reductionOpenBoundaryMatrixContraction_self
    (A : MPSTensor d D_A) (hA : Kraus.IsInjective A)
    (n : ℕ) (hn : 0 < n) (X : Matrix (Fin D_A) (Fin D_A) ℂ)
    (a' a : Fin D_A) :
    reductionOpenBoundaryMatrixContraction
        A (coefficientDualInverse A hA) n X a' a =
      (D_A : ℂ) ^ (n - 1) * X a' a := by
  rw [reductionOpenBoundaryMatrixContraction_eq_cross_sum,
    coefficientDualCross_pow A hA n hn]
  simp [reductionCrossMatrix_coefficientDualInverse,
    Matrix.vecMulVec_apply, diagonalBondVector]

/-- Exact same-alphabet target evaluation of the open-boundary contraction. -/
theorem reductionOpenBoundaryContraction_self
    (A : MPSTensor d D_A) (hA : Kraus.IsInjective A)
    (n : ℕ) (hn : 0 < n) (w : List (Fin d)) (a' a : Fin D_A) :
    reductionOpenBoundaryContraction A (coefficientDualInverse A hA) n w a' a =
      (D_A : ℂ) ^ (n - 1) * Kraus.evalWord A w a' a := by
  exact reductionOpenBoundaryMatrixContraction_self A hA n hn
    (Kraus.evalWord A w) a' a

/-- Source open-boundary formula used immediately after the closed trace-power
calculation in Proposition 20.  Positive-length MPV equality replaces each
closed `B` word followed by the tail by the corresponding `A` word; the
coefficient dual then opens the target tail with the source's reversed upper
leg order.

Source: arXiv:1706.07329v2, `cornerproblem.tex` lines 3866--3887; compare the
rank-one rewrite and final reduction equation at lines 3907--3938. -/
theorem reductionOpenBoundaryContraction_of_sameMPV₂Pos
    (A : MPSTensor d D_A) (B : MPSTensor d D_B)
    (hA : Kraus.IsInjective A) (hSame : SameMPV₂Pos B A)
    (n : ℕ) (hn : 0 < n) (w : List (Fin d)) (a' a : Fin D_A) :
    reductionOpenBoundaryContraction B (coefficientDualInverse A hA) n w a' a =
      (D_A : ℂ) ^ (n - 1) * Kraus.evalWord A w a' a := by
  have hterm (σ : Fin n → Fin d) :
      Matrix.trace
          (Kraus.evalWord B (List.ofFn σ) * Kraus.evalWord B w) =
        Matrix.trace
          (Kraus.evalWord A (List.ofFn σ) * Kraus.evalWord A w) := by
    rw [← Kraus.evalWord_append, ← Kraus.evalWord_append]
    exact hSame.trace_evalWord (List.ofFn σ ++ w) (by
      intro hnil
      have hleft : List.ofFn σ = [] := (List.append_eq_nil_iff.mp hnil).1
      exact (Nat.ne_of_gt hn) (List.ofFn_eq_nil_iff.mp hleft))
  unfold reductionOpenBoundaryContraction reductionOpenBoundaryMatrixContraction
  simp_rw [hterm]
  exact reductionOpenBoundaryContraction_self A hA n hn w a' a

/-- The literal padded source contraction: the `n` inverse sites use the
`p`-blocked tensors, while the lower open tail is an arbitrary unblocked word.
The reversed upper dual word is unchanged.  This is the mixed blocked/unblocked
formula drawn in `cornerproblem.tex` lines 3866--3887. -/
theorem reductionOpenBoundaryMatrixContraction_blockTensor_of_sameMPV₂Pos
    (A : MPSTensor d D_A) (B : MPSTensor d D_B)
    (hSame : SameMPV₂Pos B A) (p : ℕ) (hp : 0 < p)
    (hA : Kraus.IsInjective (blockTensor (d := d) (D := D_A) A p))
    (n : ℕ) (hn : 0 < n) (w : List (Fin d)) (a' a : Fin D_A) :
    reductionOpenBoundaryMatrixContraction
        (blockTensor (d := d) (D := D_B) B p)
        (coefficientDualInverse (blockTensor (d := d) (D := D_A) A p) hA)
        n (Kraus.evalWord B w) a' a =
      (D_A : ℂ) ^ (n - 1) * Kraus.evalWord A w a' a := by
  have hflat (σ : Fin n → Fin (blockPhysDim d p)) :
      flattenBlockedWord d p (List.ofFn σ) ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [length_flattenBlockedWord]
    simp only [List.length_ofFn]
    exact Nat.mul_pos hn hp
  have hterm (σ : Fin n → Fin (blockPhysDim d p)) :
      Matrix.trace
          (Kraus.evalWord (blockTensor (d := d) (D := D_B) B p) (List.ofFn σ) *
            Kraus.evalWord B w) =
        Matrix.trace
          (Kraus.evalWord (blockTensor (d := d) (D := D_A) A p) (List.ofFn σ) *
            Kraus.evalWord A w) := by
    rw [evalWord_blockTensor, evalWord_blockTensor,
      ← Kraus.evalWord_append, ← Kraus.evalWord_append]
    exact hSame.trace_evalWord (flattenBlockedWord d p (List.ofFn σ) ++ w) (by
      intro hnil
      exact hflat σ (List.append_eq_nil_iff.mp hnil).1)
  unfold reductionOpenBoundaryMatrixContraction
  simp_rw [hterm]
  exact reductionOpenBoundaryMatrixContraction_self
    (blockTensor (d := d) (D := D_A) A p) hA n hn (Kraus.evalWord A w) a' a

end MPSTensor
