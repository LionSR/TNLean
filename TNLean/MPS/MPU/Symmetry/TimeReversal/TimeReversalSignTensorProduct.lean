/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Symmetry.TimeReversal.TimeReversalBlockingParity
import TNLean.MPS.MPU.Symmetry.TimeReversal.TimeReversalTwistedTransfer
import TNLean.MPS.MPU.Index.TensorProductIndex

/-!
# The time-reversal sign of tensor products and ancillas

The intrinsic time-reversal sign is multiplicative under independent tensor products, and an
identity ancilla has sign `1`. Hence adjoining an identity ancilla, before or after blocking,
does not change the sign. This is the ancilla step of the corollary following Proposition
`prop:sigma1-and-sigma2-equal` of arXiv:1703.09188 (lines 1735--1743), with the equivalence of
Definition `def:equivalent-symmetry` (lines 1356--1366).

## Main results

* `MPOTensor.intrinsicTimeReversalSign_tensorProduct`: multiplicativity.
* `MPOTensor.intrinsicTimeReversalSign_blockTensor_tensorPhysicalId`: identity ancillas do not
  change the sign of any blocking.
-/

open scoped Matrix Kronecker

namespace MPOTensor

variable {d D e E : ℕ}

/-- The time-reversal trace of an independent tensor product is the product of the traces.

Source: arXiv:1703.09188, `eq:sigma-from-trace`, lines 1595--1603. -/
theorem timeReversalPeriodicTrace_tensorProduct (U : MPOTensor d D) (V : MPOTensor e E) :
    timeReversalPeriodicTrace (tensorProduct U V) =
      timeReversalPeriodicTrace U * timeReversalPeriodicTrace V := by
  have hletter : ∀ (i j : Fin d) (a b : Fin e),
      Matrix.trace (tensorProduct U V (finProdFinEquiv (i, a), finProdFinEquiv (j, b)) *
        tensorProduct U V (finProdFinEquiv (j, b), finProdFinEquiv (i, a))) =
        Matrix.trace (U (i, j) * U (j, i)) * Matrix.trace (V (a, b) * V (b, a)) := by
    intro i j a b
    simp only [tensorProduct, MPSTensor.finProdFinEquiv_divNat, MPSTensor.finProdFinEquiv_modNat,
      Matrix.reindex_apply, Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul]
    rw [← Matrix.reindex_apply, Matrix.trace_reindex, Matrix.trace_kronecker]
  rw [timeReversalPeriodicTrace_eq_sum, timeReversalPeriodicTrace_eq_sum,
    timeReversalPeriodicTrace_eq_sum, Finset.sum_mul_sum]
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun a _ ↦ ?_
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun b _ ↦ hletter i j a b

/-- **The intrinsic time-reversal sign is multiplicative** under independent tensor products.

Source: arXiv:1703.09188, `eq:sigma-from-trace`, lines 1595--1603. -/
theorem intrinsicTimeReversalSign_tensorProduct (U : MPOTensor d D) (V : MPOTensor e E) :
    intrinsicTimeReversalSign (tensorProduct U V) =
      intrinsicTimeReversalSign U * intrinsicTimeReversalSign V := by
  rw [intrinsicTimeReversalSign, intrinsicTimeReversalSign, intrinsicTimeReversalSign,
    timeReversalPeriodicTrace_tensorProduct, Nat.cast_mul, mul_inv]
  ring

/-- A tensor whose operator on a ring of two sites is the identity has sign `1`.

Source: arXiv:1703.09188, `eq:sigma-from-trace`, lines 1595--1603. -/
theorem intrinsicTimeReversalSign_eq_one_of_mpo_two_eq_one [NeZero d] {W : MPOTensor d D}
    (h : mpo W 2 = 1) : intrinsicTimeReversalSign W = 1 := by
  rw [intrinsicTimeReversalSign, timeReversalPeriodicTrace, h, Matrix.reindex_apply,
    Matrix.submatrix_one_equiv, Matrix.mul_one]
  have htr : (Matrix.swapMatrix d).trace = (d : ℂ) := by
    have hite : ∀ i j : Fin d,
        (if i = j ∧ j = i then (1 : ℂ) else 0) = if i = j then 1 else 0 := by
      intro i j
      by_cases hij : i = j <;> simp [hij]
    simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Matrix.swapMatrix_apply, hite,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [htr]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne d))

/-- **Identity ancillas do not change the sign.** Adjoining an identity ancilla of positive
dimension `x` and then blocking `k` sites gives the same intrinsic time-reversal sign as
blocking alone.

Source: arXiv:1703.09188, Definition `def:equivalent-symmetry`, lines 1356--1366, and the
corollary following Proposition `prop:sigma1-and-sigma2-equal`, lines 1735--1743. -/
theorem intrinsicTimeReversalSign_blockTensor_tensorPhysicalId (U : MPOTensor d D) {x : ℕ}
    (hx : 0 < x) {k : ℕ} (hk : 0 < k) :
    intrinsicTimeReversalSign (MPOTensor.blockTensor (tensorPhysicalId U x) k) =
      intrinsicTimeReversalSign (MPOTensor.blockTensor U k) := by
  have : NeZero (Kraus.blockPhysDim x k) := ⟨by
    rw [Kraus.blockPhysDim_eq_pow]
    exact pow_ne_zero _ hx.ne'⟩
  rw [← intrinsicTimeReversalSign_blockTensor_eq_of_mpo_eq
      (fun N _ ↦ mpo_tensorProduct_identityMPUTensor U x N) k hk,
    blockTensor_tensorProduct, intrinsicTimeReversalSign_reindexPhysical,
    intrinsicTimeReversalSign_tensorProduct,
    intrinsicTimeReversalSign_eq_one_of_mpo_two_eq_one
      (W := MPOTensor.blockTensor (identityMPUTensor x) k), mul_one]
  rw [mpo_blockTensor_eq_reindex, mpo_identityMPUTensor, Matrix.reindex_apply,
    Matrix.submatrix_one_equiv]

end MPOTensor
