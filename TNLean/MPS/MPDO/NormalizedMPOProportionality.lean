/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.AreaLaw
import TNLean.MPS.MPDO.VerticalCF

/-!
# Normalized MPOs under finite-chain proportionality

This file proves that a nonzero scalar relating two doubled-index matrix-product
vectors at a fixed chain length cancels upon trace normalization. Consequently
all reduced block states at that chain length agree. The same conclusion holds
eventually when the matrix-product vectors are eventually nonzero proportional.

## Main statements

* `MPOTensor.normalizedMPO_eq_of_nonzeroProportionalMPV₂_at`
* `MPOTensor.reducedBlockState_eq_of_nonzeroProportionalMPV₂_at`
* `MPSTensor.EventuallyNonzeroProportionalMPV₂.eventually_normalizedMPO_eq`
* `MPSTensor.EventuallyNonzeroProportionalMPV₂.eventually_reducedBlockState_eq`

## References

* arXiv:1606.00608, Theorem `thm1`, lines 1167--1182.
-/

open scoped Matrix

namespace MPOTensor

variable {d D₁ D₂ N L : ℕ}

/-- Two finite-chain MPOs have the same normalized MPO matrix when their doubled-index
matrix-product vectors differ by a nonzero scalar at that chain length.

No nonzero-trace hypothesis is needed: the traces are proportional, so if either
vanishes, both normalized MPO matrices are zero by definition.

Source context: arXiv:1606.00608, Theorem `thm1`, lines 1167--1182; this
transport is used in Appendix C.2, Proposition `4to2`, lines 1571--1619. -/
theorem normalizedMPO_eq_of_nonzeroProportionalMPV₂_at
    (M : MPOTensor d D₁) (K : MPOTensor d D₂)
    (h : ∃ c : ℂ, c ≠ 0 ∧ ∀ ρ : Fin N → Fin (d * d),
      MPSTensor.mpv M.toMPSTensor ρ = c * MPSTensor.mpv K.toMPSTensor ρ) :
    normalizedMPO M N = normalizedMPO K N := by
  obtain ⟨c, hc, hmpv⟩ := h
  have hmpo : mpo M N = c • mpo K N := by
    ext σ τ
    rw [← MPSTensor.mpv_toMPSTensor_pairConfig, hmpv,
      MPSTensor.mpv_toMPSTensor_pairConfig, Matrix.smul_apply, smul_eq_mul]
  rw [normalizedMPO, normalizedMPO, hmpo, Matrix.trace_smul, smul_smul, smul_eq_mul]
  congr 1
  field_simp

/-- Nonzero proportionality at one chain length identifies every reduced block
state obtained from that finite chain.

Source context: arXiv:1606.00608, Theorem `thm1`, lines 1167--1182; this
transport is used in Appendix C.2, Proposition `4to2`, lines 1571--1619. -/
theorem reducedBlockState_eq_of_nonzeroProportionalMPV₂_at
    (M : MPOTensor d D₁) (K : MPOTensor d D₂) (hL : L ≤ N)
    (h : ∃ c : ℂ, c ≠ 0 ∧ ∀ ρ : Fin N → Fin (d * d),
      MPSTensor.mpv M.toMPSTensor ρ = c * MPSTensor.mpv K.toMPSTensor ρ) :
    reducedBlockState M N L hL = reducedBlockState K N L hL := by
  unfold reducedBlockState
  rw [normalizedMPO_eq_of_nonzeroProportionalMPV₂_at M K h]

end MPOTensor

namespace MPSTensor

/-- Eventual nonzero proportionality of doubled-index matrix-product vectors
identifies the normalized MPO matrices at every sufficiently large length.

Source context: arXiv:1606.00608, Theorem `thm1`, lines 1167--1182; this
transport is used in Appendix C.2, Proposition `4to2`, lines 1571--1619. -/
theorem EventuallyNonzeroProportionalMPV₂.eventually_normalizedMPO_eq
    {d D₁ D₂ : ℕ} {M : MPOTensor d D₁} {K : MPOTensor d D₂}
    (h : EventuallyNonzeroProportionalMPV₂ M.toMPSTensor K.toMPSTensor) :
    ∀ᶠ N in Filter.atTop, MPOTensor.normalizedMPO M N = MPOTensor.normalizedMPO K N :=
  h.mono fun _ hN ↦ MPOTensor.normalizedMPO_eq_of_nonzeroProportionalMPV₂_at M K hN

/-- Eventual nonzero proportionality identifies every fixed-size reduced block
state once the total chain length is sufficiently large.

Source context: arXiv:1606.00608, Theorem `thm1`, lines 1167--1182; this
transport is used in Appendix C.2, Proposition `4to2`, lines 1571--1619. -/
theorem EventuallyNonzeroProportionalMPV₂.eventually_reducedBlockState_eq
    {d D₁ D₂ : ℕ} {M : MPOTensor d D₁} {K : MPOTensor d D₂}
    (h : EventuallyNonzeroProportionalMPV₂ M.toMPSTensor K.toMPSTensor)
    (L : ℕ) :
    ∀ᶠ N in Filter.atTop, ∀ hL : L ≤ N,
      MPOTensor.reducedBlockState M N L hL =
        MPOTensor.reducedBlockState K N L hL := by
  filter_upwards [h] with N hN
  exact fun hL ↦ MPOTensor.reducedBlockState_eq_of_nonzeroProportionalMPV₂_at
    M K hL hN

end MPSTensor
