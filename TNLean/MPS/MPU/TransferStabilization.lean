/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixStabilization
import TNLean.MPS.MPU.TransferMatrix

/-!
# Stabilization of the normalized MPU transfer matrix

The exact characteristic polynomial of the normalized transfer matrix is
`X ^ (D * D - 1) * (X - 1)`. Cayley--Hamilton therefore makes its
`(D * D - 1)`-st and `D * D`-th powers equal. The stabilized power is an
idempotent of trace one, hence a rank-one projector with normalized left and
right fixed witnesses.

## Main definitions

* `MPOTensor.IsMPU.normalizedTransferStabilization` gives stabilized rank-one
  data for bond dimension greater than one.
* `MPOTensor.IsMPU.normalizedTransferStabilization_fin_one` gives the
  one-dimensional data at exponent one.

## Main results

* `MPOTensor.IsMPU.exists_normalized_transfer_stabilizes_to_rank_one` gives
  the source-shaped bounded stabilization theorem.
* `MPOTensor.IsMPU.normalized_transfer_matrix_eq_one_fin_one` proves that the
  one-dimensional normalized transfer matrix is the identity.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, "Matrix Product Unitaries: Structure,
  Symmetries, and Topological Invariants", lines 397--409.
-/

open scoped Matrix BigOperators
open Polynomial

namespace MPOTensor

/-! ### Normalized MPU transfer stabilization -/

variable {d D : ℕ}

/-- For an MPU of bond dimension `D > 1`, the normalized transfer matrix
stabilizes at the explicit positive exponent `J = D * D - 1`. Its stabilized
value is `|ρ)(Φ|`, with normalized left and right fixed witnesses, and every
power at least `J` has the same value.

Cayley--Hamilton applied to
`χ_E(X) = X^(D²-1)(X-1)` eliminates precisely the zero-primary component; no
ambient normality or diagonalizability is asserted.

Source: arXiv:1703.09188, lines 397--409. -/
noncomputable def IsMPU.normalizedTransferStabilization
    [NeZero d] [NeZero D] {U : MPOTensor d D} (hU : IsMPU U) (hD : 1 < D) :
    Matrix.StabilizedRankOneData
      (transferMatrix (MPSTensor.transferMap U.normalizedFlattening)) (D * D - 1) := by
  let E := transferMatrix (MPSTensor.transferMap U.normalizedFlattening)
  have hDD : 4 ≤ D * D :=
    Nat.mul_le_mul (by omega : 2 ≤ D) (by omega : 2 ≤ D)
  have hchar : E.charpoly = X ^ (Fintype.card (Fin D × Fin D) - 1) * (X - 1) := by
    simpa [E, Fintype.card_prod, Fintype.card_fin] using hU.normalizedFlattening_charpoly
  have hpow :=
    Matrix.pow_card_eq_pow_pred_of_charpoly_eq_X_pow_pred_mul_X_sub_one E hchar
  have hstep : E ^ ((D * D - 1) + 1) = E ^ (D * D - 1) := by
    simpa [Fintype.card_prod, Fintype.card_fin,
      Nat.sub_add_cancel (by omega : 1 ≤ D * D)] using hpow
  exact Matrix.StabilizedRankOneData.of_power_succ_eq (D * D - 1) (D * D - 1)
    (by omega) le_rfl hstep
    (hU.trace_transferMatrix_normalizedFlattening_pow_eq_one (by omega))

/-- Source-shaped unbundled form of normalized transfer stabilization:
there are normalized left/right fixed witnesses and a positive
`J ≤ D * D - 1` such that `E^J = |ρ)(Φ|` and all later powers equal this
rank-one projector.

The proof removes the zero-primary component by Cayley--Hamilton; it does not
infer ambient normality from bare `IsMPU`.

Source: arXiv:1703.09188, lines 397--409. -/
theorem IsMPU.exists_normalized_transfer_stabilizes_to_rank_one
    [NeZero d] [NeZero D] {U : MPOTensor d D} (hU : IsMPU U) (hD : 1 < D) :
    ∃ J : ℕ, 0 < J ∧ J ≤ D * D - 1 ∧
      ∃ ρ Φ : Fin D × Fin D → ℂ,
        Φ ⬝ᵥ ρ = 1 ∧
        transferMatrix (MPSTensor.transferMap U.normalizedFlattening) *ᵥ ρ = ρ ∧
        Matrix.vecMul Φ
          (transferMatrix (MPSTensor.transferMap U.normalizedFlattening)) = Φ ∧
        transferMatrix (MPSTensor.transferMap U.normalizedFlattening) ^ J =
          Matrix.vecMulVec ρ Φ ∧
        ∀ k, J ≤ k →
          transferMatrix (MPSTensor.transferMap U.normalizedFlattening) ^ k =
            transferMatrix (MPSTensor.transferMap U.normalizedFlattening) ^ J := by
  let data := hU.normalizedTransferStabilization hD
  refine ⟨data.exponent, data.exponent_pos, data.exponent_le,
    data.right, data.left, ?_, data.right_fixed, data.left_fixed,
    data.power_eq, data.stable⟩
  rw [dotProduct_comm]
  exact data.pairing_eq_one

/-- In bond dimension one, the normalized transfer matrix of an MPU is the identity.

Source: arXiv:1703.09188, lines 397--409, specialized to `D = 1`. -/
theorem IsMPU.normalized_transfer_matrix_eq_one_fin_one
    [NeZero d] {U : MPOTensor d 1} (hU : IsMPU U) :
    transferMatrix (MPSTensor.transferMap U.normalizedFlattening) = 1 := by
  let E := transferMatrix (MPSTensor.transferMap U.normalizedFlattening)
  have hchar : E.charpoly = X ^ (Fintype.card (Fin 1 × Fin 1) - 1) * (X - 1) := by
    simpa [E, Fintype.card_prod, Fintype.card_fin] using hU.normalizedFlattening_charpoly
  have hpow :=
    Matrix.pow_card_eq_pow_pred_of_charpoly_eq_X_pow_pred_mul_X_sub_one E hchar
  have hE : E = 1 := by
    simpa [Fintype.card_prod, Fintype.card_fin] using hpow
  simpa [E] using hE

/-- In bond dimension one, the normalized transfer matrix stabilizes at exponent one.
This separate definition is necessary because no positive exponent can satisfy
`J ≤ D * D - 1 = 0`.

Source: arXiv:1703.09188, lines 397--409, specialized to `D = 1`. -/
noncomputable def IsMPU.normalizedTransferStabilization_fin_one
    [NeZero d] {U : MPOTensor d 1} (hU : IsMPU U) :
    Matrix.StabilizedRankOneData
      (transferMatrix (MPSTensor.transferMap U.normalizedFlattening)) 1 := by
  have hE := hU.normalized_transfer_matrix_eq_one_fin_one
  apply Matrix.StabilizedRankOneData.of_power_succ_eq 1 1 Nat.zero_lt_one le_rfl
  · rw [hE]
    simp
  · rw [hE]
    simp

end MPOTensor
