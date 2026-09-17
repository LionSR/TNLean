/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.MPDO.OperatorProduct

/-!
# Operator identities from word-trace identities

The matrix element `⟨σ|O_L(M)|τ⟩` of the periodic operator of a matrix product operator tensor
is the trace of the word of its pair-alphabet view along the configuration
`k ↦ (σ_k, τ_k)`, and every configuration of positive length gives a nonempty word. An identity
between the word traces of two pair-alphabet tensors on all nonempty words is therefore an
identity between the periodic operators at every positive length. This is how the word-trace
conclusion of a multi-block compression datum
(`MPSTensor.MultiBlockCompression.trace_evalWord_eq_sum`) becomes a fusion rule of operators,
`O_L(M) O_L(N) = O_L(P)`, in the worked examples.

## Main results

* `MPOTensor.mpo_apply_toMPSTensor`: the matrix element of a periodic operator as a word trace
  of the pair-alphabet tensor.
* `MPOTensor.mpo_eq_of_trace_evalWord`: equal nonempty word traces give equal periodic
  operators at every positive length.
* `MPOTensor.mpo_mul_eq_of_trace_evalWord`: the fusion form, for the stacked product of two
  tensors against a third.
-/

open scoped Matrix

namespace MPOTensor

variable {d D D₁ D₂ D₃ : ℕ}

/-- The configuration word of a pair of configurations of positive length is nonempty. -/
theorem ofFn_pairConfig_ne_nil {L : ℕ} (hL : 0 < L) (σ τ : Fin L → Fin d) :
    (List.ofFn fun k => finProdFinEquiv (σ k, τ k)) ≠ [] := by
  simp only [ne_eq, List.ofFn_eq_nil_iff]
  omega

/-- The matrix element of a periodic operator is the word trace of the pair-alphabet tensor
along the configuration word. -/
theorem mpo_apply_toMPSTensor (M : MPOTensor d D) {L : ℕ} (σ τ : Fin L → Fin d) :
    mpo M L σ τ =
      Matrix.trace
        (Kraus.evalWord M.toMPSTensor (List.ofFn fun k => finProdFinEquiv (σ k, τ k))) := by
  rw [mpo_apply, mpoMatrixEntry, evalWord_toMPSTensor_pairConfig]

/-- **Equal word traces give equal periodic operators.** Two tensors whose pair-alphabet views
have the same word traces on every nonempty word have the same periodic operator at every
positive length. -/
theorem mpo_eq_of_trace_evalWord (M : MPOTensor d D₁) (N : MPOTensor d D₂)
    (h : ∀ w : List (Fin (d * d)), w ≠ [] →
      Matrix.trace (Kraus.evalWord M.toMPSTensor w) = Matrix.trace (Kraus.evalWord N.toMPSTensor w))
    (L : ℕ) (hL : 0 < L) : mpo M L = mpo N L := by
  ext σ τ
  rw [mpo_apply_toMPSTensor, mpo_apply_toMPSTensor]
  exact h _ (ofFn_pairConfig_ne_nil hL σ τ)

/-- **A fusion rule from a word-trace identity.** If the stacked product of two tensors has the
word traces of a third tensor on every nonempty word, then the product of the two periodic
operators is the periodic operator of the third at every positive length. -/
theorem mpo_mul_eq_of_trace_evalWord (M : MPOTensor d D₁) (N : MPOTensor d D₂)
    (P : MPOTensor d D₃)
    (h : ∀ w : List (Fin (d * d)), w ≠ [] →
      Matrix.trace (Kraus.evalWord (mulTensor M N).toMPSTensor w) =
        Matrix.trace (Kraus.evalWord P.toMPSTensor w))
    (L : ℕ) (hL : 0 < L) : mpo M L * mpo N L = mpo P L := by
  rw [← mpo_mulTensor]
  exact mpo_eq_of_trace_evalWord _ _ h L hL

end MPOTensor
