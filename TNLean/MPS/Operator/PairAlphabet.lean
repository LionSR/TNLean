/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Operator.Product.OperatorProduct

/-!
# Operator tensors on the pair alphabet

An operator tensor `M : MPOTensor d D` is the tensor `MPTensor (Fin d × Fin d) (Fin D)` whose
physical basis is the pair alphabet of ket and bra indices, so every statement about tensors
applies to it with the letter `M (i, j)`. This file relates the tensor-level objects of `M` on
that alphabet (the word evaluation `Kraus.evalWord M`, the coefficients `MPTensor.mpv M`, the
transfer map `Kraus.transferMap M`) to the operator-level objects (`MPOTensor.evalWord` on a ket
word and a bra word, the periodic operator `MPOTensor.mpo`, `MPOTensor.transferMap`).

## Main results

* `MPOTensor.kraus_evalWord_ofFn`: a word over the pair alphabet evaluates as its ket and bra
  words.
* `MPOTensor.mpo_apply_eq_trace_kraus_evalWord`, `MPOTensor.trace_kraus_evalWord`: the matrix
  element `⟨σ|O_L(M)|τ⟩` is the trace of the word `k ↦ (σ k, τ k)`, and conversely.
* `MPOTensor.mpv_eq_mpo`, `MPOTensor.mpv_pair`: the coefficients of `M` on the pair alphabet are
  the matrix elements of its periodic operators.
* `MPOTensor.mpo_eq_of_forall_trace_evalWord`,
  `MPOTensor.mpo_eq_pow_smul_of_forall_trace_evalWord`: word-trace identities over the pair
  alphabet are identities of periodic operators at every positive length.
* `MPOTensor.mpo_mul_eq_of_forall_trace_evalWord`: the fusion form, for the stacked product of
  two tensors against a third.
* `MPOTensor.sameMPV₂Pos_iff_mpo_eq`: two operator tensors have the same positive-length
  coefficients on the pair alphabet exactly when they have the same periodic operators at every
  positive length.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608, Section 4, lines 962--967:
  the operator `O_L(M)` of a matrix product operator tensor.
-/

open scoped Matrix

namespace MPOTensor

variable {d D D₁ D₂ D₃ : ℕ}

/-- A word over the pair alphabet evaluates as the ket word and the bra word of its letters. -/
theorem kraus_evalWord_ofFn (M : MPOTensor d D) {N : ℕ} (w : Fin N → Fin d × Fin d) :
    Kraus.evalWord M (List.ofFn w) =
      evalWord M (List.ofFn fun k ↦ (w k).1) (List.ofFn fun k ↦ (w k).2) :=
  kraus_evalWord_ofFn_pair M (fun k ↦ (w k).1) (fun k ↦ (w k).2)

/-- The matrix element of a periodic operator is the trace of the word of paired letters.

Source: arXiv:1606.00608, lines 962--967. -/
theorem mpo_apply_eq_trace_kraus_evalWord (M : MPOTensor d D) {L : ℕ} (σ τ : Fin L → Fin d) :
    mpo M L σ τ = Matrix.trace (Kraus.evalWord M (List.ofFn fun k ↦ (σ k, τ k))) := by
  rw [mpo_apply, mpoMatrixEntry, kraus_evalWord_ofFn_pair]

/-- The trace of a word over the pair alphabet is a matrix element of the periodic operator of
its length. -/
theorem trace_kraus_evalWord (M : MPOTensor d D) (w : List (Fin d × Fin d)) :
    Matrix.trace (Kraus.evalWord M w) =
      mpo M w.length (fun k ↦ (w.get k).1) (fun k ↦ (w.get k).2) := by
  conv_lhs => rw [← List.ofFn_get w]
  rw [kraus_evalWord_ofFn]
  rfl

/-- The coefficient of an operator tensor on a configuration of the pair alphabet is the matrix
element of its periodic operator between the ket and bra configurations. -/
theorem mpv_eq_mpo (M : MPOTensor d D) {N : ℕ} (w : Fin N → Fin d × Fin d) :
    MPTensor.mpv M w = mpo M N (fun k ↦ (w k).1) (fun k ↦ (w k).2) := by
  rw [MPTensor.mpv_eq, MPTensor.coeff_eq, kraus_evalWord_ofFn, mpo_apply, mpoMatrixEntry]

/-- The coefficient of an operator tensor on the paired configuration `k ↦ (σ k, τ k)` is the
matrix element `⟨σ|O_N(M)|τ⟩`. -/
@[simp] theorem mpv_pair (M : MPOTensor d D) {N : ℕ} (σ τ : Fin N → Fin d) :
    MPTensor.mpv M (fun k ↦ (σ k, τ k)) = mpo M N σ τ :=
  mpv_eq_mpo M _

/-- The word of paired letters of two configurations of positive length is nonempty. -/
theorem ofFn_pair_ne_nil {L : ℕ} (hL : 0 < L) (σ τ : Fin L → Fin d) :
    (List.ofFn fun k ↦ (σ k, τ k)) ≠ [] := by
  simp only [ne_eq, List.ofFn_eq_nil_iff]
  omega

/-- **Equal word traces give equal periodic operators.** Two operator tensors with the same
word traces on every nonempty word of the pair alphabet have the same periodic operator at every
positive length. -/
theorem mpo_eq_of_forall_trace_evalWord {M : MPOTensor d D₁} {N : MPOTensor d D₂}
    (h : ∀ w : List (Fin d × Fin d), w ≠ [] →
      Matrix.trace (Kraus.evalWord M w) = Matrix.trace (Kraus.evalWord N w))
    {L : ℕ} (hL : 0 < L) : mpo M L = mpo N L := by
  ext σ τ
  rw [mpo_apply_eq_trace_kraus_evalWord, mpo_apply_eq_trace_kraus_evalWord]
  exact h _ (ofFn_pair_ne_nil hL σ τ)

/-- An operator tensor whose nonempty word traces over the pair alphabet are those of a second
tensor weighted by `c ^ L` has `c ^ L` times the periodic operator of the second tensor. -/
theorem mpo_eq_pow_smul_of_forall_trace_evalWord {M : MPOTensor d D₁} {N : MPOTensor d D₂}
    (c : ℂ) (h : ∀ w : List (Fin d × Fin d), w ≠ [] →
      Matrix.trace (Kraus.evalWord M w) = c ^ w.length * Matrix.trace (Kraus.evalWord N w))
    {L : ℕ} (hL : 0 < L) : mpo M L = c ^ L • mpo N L := by
  ext σ τ
  have hw := h _ (ofFn_pair_ne_nil hL σ τ)
  rw [List.length_ofFn, ← mpo_apply_eq_trace_kraus_evalWord,
    ← mpo_apply_eq_trace_kraus_evalWord] at hw
  rw [hw, Matrix.smul_apply, smul_eq_mul]

/-- **A fusion rule from a word-trace identity.** If the stacked product of two operator tensors
has the word traces of a third tensor on every nonempty word of the pair alphabet, then the
product of the two periodic operators is the periodic operator of the third at every positive
length. -/
theorem mpo_mul_eq_of_forall_trace_evalWord {M : MPOTensor d D₁} {N : MPOTensor d D₂}
    {P : MPOTensor d D₃}
    (h : ∀ w : List (Fin d × Fin d), w ≠ [] →
      Matrix.trace (Kraus.evalWord (mulTensor M N) w) = Matrix.trace (Kraus.evalWord P w))
    {L : ℕ} (hL : 0 < L) : mpo M L * mpo N L = mpo P L := by
  rw [← mpo_mulTensor]
  exact mpo_eq_of_forall_trace_evalWord h hL

/-- Two operator tensors have the same positive-length coefficients on the pair alphabet
exactly when they have the same periodic operators at every positive length. -/
theorem sameMPV₂Pos_iff_mpo_eq {M : MPOTensor d D₁} {M' : MPOTensor d D₂} :
    MPTensor.SameMPV₂Pos M M' ↔ ∀ N, 0 < N → mpo M N = mpo M' N := by
  constructor
  · intro h N hN
    ext σ τ
    rw [← mpv_pair, ← mpv_pair]
    exact h N hN _
  · intro h N hN w
    rw [mpv_eq_mpo, mpv_eq_mpo, h N hN]

end MPOTensor
