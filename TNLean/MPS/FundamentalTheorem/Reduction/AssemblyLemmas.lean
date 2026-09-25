/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.FundamentalTheorem.Reduction.MultiBlockTrace

/-!
# Assembly lemmas for worked compression examples

**Source.** None: this is infrastructure of this development for the worked examples of the
multi-block asymmetric compression theorem, and no paper states it.

**Formalized here.** Three general facts to which the worked examples reduce their
verifications as finite decisions.

* A tensor all of whose products of three letters vanish evaluates every word of length at
  least three to zero. This is the form in which the sharp nilpotency order of a remainder is
  certified.
* The sitewise intertwining equations `B^i X = X C^i` of a source with a block are a linear
  system in the entries of `X`. A selection of the equations whose coefficient matrix has an
  explicit left inverse up to a nonzero scalar forces `X = 0`. This is the form in which the
  absence of sitewise intertwiners, that is, the failure of the extension of a compression to
  split into sitewise fusion pairs, is certified.
* A tensor whose letters are a common reindexing of block-diagonal matrices evaluates words
  block by block, so its word traces are the sums of the word traces of the blocks. This is
  how a condensation defect `⊕_g U_g` and its stacked square are assembled from their summands.

## Main definitions

* `MPSTensor.sitewiseEqMatrix`: the coefficient matrix of the sitewise intertwining equations.

## Main results

* `MPSTensor.evalWord_eq_zero_of_triple_mul_eq_zero`,
  `MPSTensor.triple_mul_eq_zero_of_support`: vanishing of long words from vanishing triple
  products, decided on the support of the family.
* `MPSTensor.right_intertwiner_eq_zero_of_certificate`,
  `MPSTensor.left_intertwiner_eq_zero_of_certificate`: vanishing of the sitewise intertwiner
  spaces from an explicit certificate.
* `MPSTensor.evalWord_blockDiagonal'_submatrix`,
  `MPSTensor.trace_evalWord_blockDiagonal'_submatrix`: word evaluation and word traces of a
  reindexed block-diagonal tensor.

## Provenance

The compression theorem is Theorem 7.7 (`thm:p5-asymmetric-compression`, §7.5) of
`Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`, lines 495–569.
-/

open scoped Matrix

namespace MPSTensor

/-! ### Nilpotency from vanishing triple products -/

/-- If every product of three letters of a tensor vanishes, then so does every word of length at
least three. -/
theorem evalWord_eq_zero_of_triple_mul_eq_zero {d D : ℕ} (A : MPSTensor d D)
    (h : ∀ a b c, A a * A b * A c = 0) (w : List (Fin d)) (hw : 3 ≤ w.length) :
    Kraus.evalWord A w = 0 := by
  rcases w with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp at hw
  · simp at hw
  · simp at hw
  · change A a * (A b * (A c * Kraus.evalWord A rest)) = 0
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Matrix.zero_mul]

/-- If every letter of a family is zero or one of finitely many listed letters, and every
product of three listed letters vanishes, then every product of three letters vanishes. This
restricts the finite decision of the triple products to the support of a remainder. -/
theorem triple_mul_eq_zero_of_support {ι κ M : Type*} [MulZeroClass M] (A : ι → M)
    (nz : κ → ι) (hsupp : ∀ a, A a = 0 ∨ ∃ j, nz j = a)
    (h : ∀ i j l, A (nz i) * A (nz j) * A (nz l) = 0) (a b c : ι) : A a * A b * A c = 0 := by
  rcases hsupp a with ha | ⟨i, rfl⟩
  · simp [ha]
  rcases hsupp b with hb | ⟨j, rfl⟩
  · simp [hb]
  rcases hsupp c with hc | ⟨l, rfl⟩
  · simp [hc]
  exact h i j l

/-! ### Certificates for the absence of sitewise intertwiners -/

/-- The coefficient matrix of the sitewise intertwining equations `B^i X = X C^i`: the row
`(i, p, q)` is the equation for the entry `(p, q)` of `B^i X - X C^i`, read as a linear form in
the entries `(r, s)` of `X`. -/
def sitewiseEqMatrix {R : Type*} [Ring R] {d m n : ℕ} (B : Fin d → Matrix (Fin m) (Fin m) R)
    (C : Fin d → Matrix (Fin n) (Fin n) R) :
    Matrix (Fin d × Fin m × Fin n) (Fin m × Fin n) R :=
  Matrix.of fun x y =>
    B x.1 x.2.1 y.1 * (if x.2.2 = y.2 then 1 else 0) -
      (if x.2.1 = y.1 then 1 else 0) * C x.1 y.2 x.2.2

theorem sitewiseEqMatrix_map {R S : Type*} [Ring R] [Ring S] (f : R →+* S) {d m n : ℕ}
    (B : Fin d → Matrix (Fin m) (Fin m) R) (C : Fin d → Matrix (Fin n) (Fin n) R) :
    (sitewiseEqMatrix B C).map f =
      sitewiseEqMatrix (fun i => (B i).map f) (fun i => (C i).map f) := by
  ext x y
  simp [sitewiseEqMatrix, apply_ite f]

/-- Applying the coefficient matrix to the vector of entries of `X` computes the entries of
`B^i X - X C^i`. -/
theorem sitewiseEqMatrix_mulVec {R : Type*} [CommRing R] {d m n : ℕ}
    (B : Fin d → Matrix (Fin m) (Fin m) R) (C : Fin d → Matrix (Fin n) (Fin n) R)
    (X : Matrix (Fin m) (Fin n) R) (x : Fin d × Fin m × Fin n) :
    (sitewiseEqMatrix B C *ᵥ fun y => X y.1 y.2) x = (B x.1 * X - X * C x.1) x.2.1 x.2.2 := by
  obtain ⟨i, p, q⟩ := x
  simp only [Matrix.mulVec, dotProduct, sitewiseEqMatrix, Matrix.of_apply, Matrix.sub_apply,
    Matrix.mul_apply, sub_mul, Finset.sum_sub_distrib, mul_ite, ite_mul, mul_one, mul_zero,
    one_mul, zero_mul]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp [Finset.sum_ite_eq, mul_comm]

/-- **No nonzero right sitewise intertwiner from a certificate.** If a selection `rows` of the
sitewise intertwining equations has a coefficient matrix with a left inverse `N` up to the
nonzero scalar `c`, then the only solution of `B^i X = X C^i` for all `i` is `X = 0`. -/
theorem right_intertwiner_eq_zero_of_certificate {d m n k : ℕ}
    (B : Fin d → Matrix (Fin m) (Fin m) ℂ) (C : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (rows : Fin k → Fin d × Fin m × Fin n) (N : Matrix (Fin m × Fin n) (Fin k) ℂ) {c : ℂ}
    (hc : c ≠ 0) (hN : N * (sitewiseEqMatrix B C).submatrix rows id = c • 1)
    (X : Matrix (Fin m) (Fin n) ℂ) (hX : ∀ i, B i * X = X * C i) : X = 0 := by
  set v : Fin m × Fin n → ℂ := fun y => X y.1 y.2 with hv
  have hMv : sitewiseEqMatrix B C *ᵥ v = 0 := by
    funext x
    rw [hv, sitewiseEqMatrix_mulVec, hX, sub_self]
    rfl
  have hsub : (sitewiseEqMatrix B C).submatrix rows id *ᵥ v = 0 :=
    funext fun j => congrFun hMv (rows j)
  have hcv : c • v = 0 := by
    have h := congrArg (fun M => M *ᵥ v) hN
    simp only [← Matrix.mulVec_mulVec, hsub, Matrix.mulVec_zero, Matrix.smul_mulVec,
      Matrix.one_mulVec] at h
    exact h.symm
  have hv0 : v = 0 := (smul_eq_zero.1 hcv).resolve_left hc
  ext p q
  exact congrFun hv0 (p, q)

/-- **No nonzero left sitewise intertwiner from a certificate.** The transposed form of
`right_intertwiner_eq_zero_of_certificate`: a certificate for the transposed letters forces every
solution of `Y B^i = C^i Y` to vanish. -/
theorem left_intertwiner_eq_zero_of_certificate {d m n k : ℕ}
    (B : Fin d → Matrix (Fin m) (Fin m) ℂ) (C : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (rows : Fin k → Fin d × Fin m × Fin n) (N : Matrix (Fin m × Fin n) (Fin k) ℂ) {c : ℂ}
    (hc : c ≠ 0)
    (hN : N * (sitewiseEqMatrix (fun i => (B i)ᵀ) (fun i => (C i)ᵀ)).submatrix rows id = c • 1)
    (Y : Matrix (Fin n) (Fin m) ℂ) (hY : ∀ i, Y * B i = C i * Y) : Y = 0 := by
  have h := right_intertwiner_eq_zero_of_certificate (fun i => (B i)ᵀ) (fun i => (C i)ᵀ) rows N
    hc hN Yᵀ fun i => by rw [← Matrix.transpose_mul, hY, Matrix.transpose_mul]
  simpa using congrArg Matrix.transpose h

/-! ### Words of reindexed block-diagonal tensors -/

variable {κ : Type*} [DecidableEq κ] {n : κ → ℕ} {d DB : ℕ}

/-- A tensor whose letters are the block-diagonal matrices of a family of tensors, reindexed by
a common bijection, evaluates words block by block. -/
theorem evalWord_blockDiagonal'_submatrix [Finite κ] (e : (Σ k, Fin (n k)) ≃ Fin DB)
    (A : Fin d → ∀ k, Matrix (Fin (n k)) (Fin (n k)) ℂ) (w : List (Fin d)) :
    Kraus.evalWord (fun a => (Matrix.blockDiagonal' (A a)).submatrix e.symm e.symm) w =
      (Matrix.blockDiagonal' fun k => Kraus.evalWord (fun a => A a k) w).submatrix
        e.symm e.symm := by
  have := Fintype.ofFinite κ
  induction w with
  | nil =>
    simp only [Kraus.evalWord]
    rw [show (fun k => (1 : Matrix (Fin (n k)) (Fin (n k)) ℂ)) = 1 from rfl,
      Matrix.blockDiagonal'_one, Matrix.submatrix_one_equiv]
  | cons a w ih =>
    simp only [Kraus.evalWord]
    rw [ih, Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal'_mul]

/-- The word traces of a reindexed block-diagonal tensor are the sums of the word traces of
its blocks. -/
theorem trace_evalWord_blockDiagonal'_submatrix [Fintype κ] (e : (Σ k, Fin (n k)) ≃ Fin DB)
    (A : Fin d → ∀ k, Matrix (Fin (n k)) (Fin (n k)) ℂ) (w : List (Fin d)) :
    Matrix.trace
        (Kraus.evalWord (fun a => (Matrix.blockDiagonal' (A a)).submatrix e.symm e.symm) w) =
      ∑ k, Matrix.trace (Kraus.evalWord (fun a => A a k) w) := by
  have htr : ∀ X : Matrix (Σ k, Fin (n k)) (Σ k, Fin (n k)) ℂ,
      (X.submatrix e.symm e.symm).trace = X.trace := fun X => by
    simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
    exact Fintype.sum_equiv e.symm _ _ fun _ => rfl
  rw [evalWord_blockDiagonal'_submatrix, htr, trace_eq_sum_blockDiag']
  simp [Matrix.blockDiag'_blockDiagonal']

end MPSTensor
