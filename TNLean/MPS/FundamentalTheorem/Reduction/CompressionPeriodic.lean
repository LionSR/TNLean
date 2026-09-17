/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.FundamentalTheorem.Reduction.MultiBlockTrace
import TNLean.MPS.MPDO.ActionTensor

/-!
# Periodic-operator readings of a multi-block compression datum

The word-trace identity of a multi-block compression datum
(`MPSTensor.MultiBlockCompression.trace_evalWord_eq_sum`) has two readings on the periodic
operators of matrix product operators, converse to the existence theorems of
`TNLean/MPS/FundamentalTheorem/Reduction/MPOProduct.lean`: a compression of the stacked product
of two operator tensors onto the doubled-index views of a family of operator tensors gives the
product of the periodic operators as the sum of the periodic operators of the family, and a
compression of an action tensor onto a family of state tensors gives the periodic operator
applied to the periodic vector as the sum of the periodic vectors of the family (P5 note,
Theorem 7.12 and its action-tensor corollary, arXiv:2203.12563, equation `mpoMPSsten`).

## Main results

* `MPOTensor.mpo_mul_eq_sum_of_multiBlockCompression`: the product reading.
* `MPOTensor.mpo_mulVec_mpv_eq_sum_of_multiBlockCompression`: the action reading.
-/

open scoped Matrix

namespace MPOTensor

variable {d : ℕ} {ι : Type*} [DecidableEq ι]

/-- **A compression of a stacked product is a fusion rule of periodic operators.** If the
stacked product of `M` and `N` compresses onto the doubled-index views of the operator tensors
`C s`, then at every positive length the product of the periodic operators of `M` and `N` is the
sum of the periodic operators of the `C s` (P5 note, Theorem 7.12, converse direction). -/
theorem mpo_mul_eq_sum_of_multiBlockCompression {Dα Dβ : ℕ} {Dγ : ι → ℕ}
    {M : MPOTensor d Dα} {N : MPOTensor d Dβ} {S : Finset ι} {C : ∀ s, MPOTensor d (Dγ s)}
    (P : MPSTensor.MultiBlockCompression (mulTensor M N).toMPSTensor S
      fun s => (C s).toMPSTensor) (L : ℕ) (hL : 0 < L) :
    mpo M L * mpo N L = ∑ s ∈ S, mpo (C s) L := by
  rw [← mpo_mulTensor]
  ext σ τ
  have hw : (List.ofFn fun k => finProdFinEquiv (σ k, τ k)) ≠ [] := by
    simp only [ne_eq, List.ofFn_eq_nil_iff]
    omega
  have h := P.trace_evalWord_eq_sum _ hw
  simp only [evalWord_toMPSTensor_pairConfig] at h
  rw [Matrix.sum_apply]
  simpa only [mpo_apply, mpoMatrixEntry] using h

/-- **A compression of an action tensor is an action rule of periodic operators.** If the
action tensor of `T` on `A` compresses onto the state tensors `C s`, then at every positive
length the periodic operator of `T` carries the periodic vector of `A` to the sum of the
periodic vectors of the `C s` (arXiv:2203.12563, equation `mpoMPSsten`, converse
direction). -/
theorem mpo_mulVec_mpv_eq_sum_of_multiBlockCompression {D DA : ℕ} {Dy : ι → ℕ}
    {T : MPOTensor d D} {A : MPSTensor d DA} {S : Finset ι} {C : ∀ s, MPSTensor d (Dy s)}
    (P : MPSTensor.MultiBlockCompression (actTensor T A) S C) (L : ℕ) (hL : 0 < L) :
    mpo T L *ᵥ (fun τ : Fin L → Fin d => MPSTensor.mpv A τ) =
      fun σ : Fin L → Fin d => ∑ s ∈ S, MPSTensor.mpv (C s) σ := by
  rw [mpo_mulVec_mpv]
  funext σ
  exact P.mpv_eq_sum L hL σ

end MPOTensor
