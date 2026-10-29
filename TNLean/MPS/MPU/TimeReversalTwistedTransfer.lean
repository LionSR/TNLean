/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.TimeReversalSignIntrinsic
import TNLean.MPS.MPU.DoubleLayerContraction
import QICLean.Algebra.SwapTrace

/-!
# A twisted-transfer expression for the intrinsic blocked trace

The normalized physical diagonal of the actual product tensor `mulTensor U U`
has letters summed as `U i j ⊗ U j i`. Its powers, contracted with exchange
of the two bond factors, give the intrinsic time-reversal trace of every
physical block. This identity needs no symmetry, canonical form, supplied
standard form, or local certificate.

This is a prerequisite for intrinsic blocking parity, not the parity theorem
or the source's explicit blocked-gate construction. A virtual sign obtained
from even-family comparison is not identified with the first intrinsic sign.

Source: arXiv:1703.09188, `eq:sigma-from-trace` and
`prop:sigma1-and-sigma2-equal`, lines 1595--1610 and 1633--1733.
-/

open scoped Matrix Kronecker BigOperators

namespace MPOTensor

variable {d D : ℕ}

/-- The normalized physical diagonal of the actual square of an MPO tensor,
in product bond coordinates. This is the twisted transfer entering the
exchange-contracted blocked trace. Source: arXiv:1703.09188,
`eq:sigma-from-trace` and the blocking argument, lines 1595--1610 and 1633--1733. -/
noncomputable def timeReversalTwistedTransfer (U : MPOTensor d D) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
    (normalizedDiagonal (mulTensor U U))

/-- Exchange against the actual two-site periodic operator contracts the
two opposite physical letters, with no assumptions on the tensor.
Source: arXiv:1703.09188, `eq:sigma-from-trace`, lines 1595--1610. -/
theorem timeReversalPeriodicTrace_eq_sum (U : MPOTensor d D) :
    timeReversalPeriodicTrace U =
      ∑ i : Fin d, ∑ j : Fin d, Matrix.trace (U i j * U j i) := by
  classical
  have hentry (i j : Fin d) :
      (Matrix.swapMatrix d *
        Matrix.reindex (finTwoArrowEquiv (Fin d)) (finTwoArrowEquiv (Fin d))
          (mpo U 2)) (i, j) (i, j) = Matrix.trace (U j i * U i j) := by
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.swapMatrix_apply,
      Matrix.reindex_apply, finTwoArrowEquiv, mpoMatrixEntry, ite_and, ite_mul,
      List.ofFn_succ, List.ofFn_zero, evalWord]
  change (∑ x : Fin d × Fin d, _) = _
  simp only [Fintype.sum_prod_type, hentry]
  exact Finset.sum_congr rfl fun i _ ↦
    Finset.sum_congr rfl fun j _ ↦ Matrix.trace_mul_comm (U j i) (U i j)

/-- The intrinsic periodic trace of a physical block is the sum of the
oppositely contracted pairs of actual open words. The two words have exactly
the blocking length, not a further multiple of it.
Source: arXiv:1703.09188, `eq:sigma-from-trace` and blocking discussion,
lines 1595--1610 and 1633--1733. -/
theorem timeReversalPeriodicTrace_blockTensor (U : MPOTensor d D) (k : ℕ) :
    timeReversalPeriodicTrace (blockTensor U k) =
      ∑ σ : Fin k → Fin d, ∑ τ : Fin k → Fin d,
        Matrix.trace (evalWord U (List.ofFn σ) (List.ofFn τ) *
          evalWord U (List.ofFn τ) (List.ofFn σ)) := by
  classical
  rw [timeReversalPeriodicTrace_eq_sum]
  simp only [blockTensor_apply, Kraus.wordOfBlock]
  let e := Kraus.decodeBlockEquiv d k
  let f (σ τ : Fin k → Fin d) :=
    Matrix.trace (evalWord U (List.ofFn σ) (List.ofFn τ) *
      evalWord U (List.ofFn τ) (List.ofFn σ))
  change (∑ i, ∑ j, f (e i) (e j)) = ∑ σ, ∑ τ, f σ τ
  calc
    _ = ∑ i, ∑ τ, f (e i) τ := by
      exact Finset.sum_congr rfl fun i _ ↦ e.sum_comp (f (e i))
    _ = _ := e.sum_comp (fun σ ↦ ∑ τ, f σ τ)

/-- Powers of the actual twisted transfer are normalized sums of opposite
open-word Kronecker products. This uses the product-tensor word contraction,
with no prescribed spectral multiplier or source-factor premise.
Source: arXiv:1703.09188, blocking argument, lines 1633--1733. -/
theorem timeReversalTwistedTransfer_pow_eq_sum_evalWord
    (U : MPOTensor d D) (k : ℕ) :
    timeReversalTwistedTransfer U ^ k = ((d : ℂ)⁻¹) ^ k •
      ∑ σ : Fin k → Fin d, ∑ τ : Fin k → Fin d,
        evalWord U (List.ofFn σ) (List.ofFn τ) ⊗ₖ
          evalWord U (List.ofFn τ) (List.ofFn σ) := by
  classical
  let R := Matrix.reindexAlgEquiv ℂ ℂ (finProdFinEquiv (m := D) (n := D)).symm
  have hR (M : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) :
      R (M.submatrix finProdFinEquiv.symm finProdFinEquiv.symm) = M := by
    ext i j
    simp [R, Matrix.reindex_apply]
  change R (normalizedDiagonal (mulTensor U U)) ^ k = _
  rw [← map_pow, normalizedDiagonal_pow_eq_sum_evalWord]
  simp only [map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  rw [evalWord_mulTensor, hR]

private theorem swap_mul_kronecker
    (A B : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.swapMatrix D * (A ⊗ₖ B) = (B ⊗ₖ A) * Matrix.swapMatrix D := by
  classical
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.swapMatrix_apply,
    Matrix.kroneckerMap_apply, ite_and, ite_mul, mul_ite, mul_comm]

/-- The actual twisted transfer commutes with exchange of its two bond
factors. Exchanging them simply exchanges the two physical-word summation
variables. Source context: arXiv:1703.09188, `eq:sigma-from-trace` and the
blocking argument, lines 1595--1610 and 1633--1733. -/
theorem swapMatrix_commute_timeReversalTwistedTransfer (U : MPOTensor d D) :
    Commute (Matrix.swapMatrix D) (timeReversalTwistedTransfer U) := by
  classical
  have h := timeReversalTwistedTransfer_pow_eq_sum_evalWord U 1
  simp only [pow_one] at h
  change Matrix.swapMatrix D * timeReversalTwistedTransfer U =
    timeReversalTwistedTransfer U * Matrix.swapMatrix D
  simp only [h, Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul,
    swap_mul_kronecker]
  congr 1
  rw [Finset.sum_comm]

/-- The intrinsic sign expression of every physical block is an actual
finite-dimensional twisted-transfer trace. No canonical or time-reversal
assumption is needed for this identity, including at blocking length zero.
It does not by itself identify a virtual sign or prove blocking parity.

Source: arXiv:1703.09188, `eq:sigma-from-trace` and
`prop:sigma1-and-sigma2-equal`, lines 1595--1610 and 1633--1733. -/
theorem intrinsicTimeReversalSign_blockTensor_eq_twistedTransfer_trace
    (U : MPOTensor d D) (k : ℕ) :
    intrinsicTimeReversalSign (blockTensor U k) =
      Matrix.trace (Matrix.swapMatrix D * timeReversalTwistedTransfer U ^ k) := by
  classical
  rw [intrinsicTimeReversalSign, timeReversalPeriodicTrace_blockTensor,
    MPSTensor.blockPhysDim_eq_pow, Nat.cast_pow, inv_pow,
    timeReversalTwistedTransfer_pow_eq_sum_evalWord,
    Matrix.mul_smul, Matrix.trace_smul]
  simp only [Finset.mul_sum, Matrix.trace_sum,
    Matrix.trace_swapMatrix_mul_kronecker, smul_eq_mul]

end MPOTensor
