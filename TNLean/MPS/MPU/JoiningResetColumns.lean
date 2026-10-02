/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.JoiningSpectatorColumns
import TNLean.MPS.MPU.BasisEncodingCoordinates

/-!
# Basis reset inside the actual output inclusion

Multiplication by the reset output columns selects the prescribed reset label
of the physical basis inclusion. Inserting an unchanged spectator respects
this reset, with its scalar phase retained.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5.
-/

open Matrix MPSPreparation MPSTensor
open scoped Kronecker

namespace MPUCircuit

/-- Reset columns select the designated output label of a basis inclusion.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem initializedBasisMatrix_mul_basisResetOutput {ι ρ κ μ : Type*}
    [Fintype ρ] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (E : (ρ × κ) ↪ ι) (z : κ) (V : Matrix ρ μ ℂ) :
    initializedBasisMatrix E * basisResetOutput V z =
      initializedBasisMatrix ((Function.Embedding.sectL ρ z).trans E) * V := by
  ext i b
  simp [Matrix.mul_apply, initializedBasisMatrix, Matrix.one_apply, basisResetOutput,
    Fintype.sum_prod_type, Pi.single_apply]

/-- A spectator identity commutes with the prescribed joining-pair reset.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem joiningSpectatorColumns_basisResetOutput
    {r : ℕ} {ρ μ τ : Type*} [DecidableEq τ]
    (V : Matrix ρ μ ℂ) (z : Fin r × Fin r) :
    joiningSpectatorColumns (τ := τ) (basisResetOutput V z) =
      basisResetOutput (V ⊗ₖ (1 : Matrix τ τ ℂ)) z := by
  ext p b
  simp only [joiningSpectatorColumns, basisResetOutput, Matrix.kroneckerMap_apply]
  ring

end MPUCircuit
