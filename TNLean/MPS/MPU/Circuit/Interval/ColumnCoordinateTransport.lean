/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Circuit.Interval.MinimalIntervalLeafColumns
import TNLean.MPS.MPU.Circuit.Interval.BasisEncodingCoordinates
import QICLean.Circuit.Model.CleanWorkspace

/-!
# Exact column identities under coordinate changes

Initialized column identities are transported along physical and input-output
coordinate bijections. A full clean implementation determines its logical
initialized columns by cancellation of the isometric workspace inclusion.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5.
-/

open Matrix MPSPreparation MPSTensor QuantumCircuit

namespace MPUCircuit

/-- Coordinate bijections transport the complete initialized column equation.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem matrix_columns_reindex {ι κ α β γ δ : Type*}
    [Fintype ι] [Fintype κ] [Fintype γ] [Fintype δ]
    [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (f : α ≃ β) (g : γ ≃ δ)
    (E : α ↪ ι) (G : γ ↪ ι) (F : β ↪ κ) (H : δ ↪ κ)
    (hE : ∀ b, e (E (f.symm b)) = F b)
    (hG : ∀ c, e (G (g.symm c)) = H c)
    (X : Matrix ι ι ℂ) (V : Matrix γ α ℂ)
    (h : X * basisInclusion E = basisInclusion G * V) :
    Matrix.reindex e e X * basisInclusion F =
      basisInclusion H * Matrix.reindex g f V := by
  rw [← basisInclusion_reindex_of_mapping e f E F hE,
    ← basisInclusion_reindex_of_mapping e g G H hG]
  change Matrix.reindexLinearEquiv ℂ ℂ e e X *
      Matrix.reindexLinearEquiv ℂ ℂ e f (basisInclusion E) =
    Matrix.reindexLinearEquiv ℂ ℂ e g (basisInclusion G) *
      Matrix.reindexLinearEquiv ℂ ℂ g f V
  rw [Matrix.reindexLinearEquiv_mul, Matrix.reindexLinearEquiv_mul, h]

/-- Reindexing input columns commutes with the normalized joining contraction.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem normalizedJoiningParent_submatrix_columns {r : ℕ} {ρ μ ν : Type*}
    [Fintype ρ] [DecidableEq ρ] (hr : 0 < r)
    (P : Matrix (Fin r) (Fin r) ℂ) (V : Matrix (ρ × (Fin r × Fin r)) μ ℂ)
    (f : ν → μ) :
    normalizedJoiningParent hr P (V.submatrix id f) =
      (normalizedJoiningParent hr P V).submatrix id f := rfl

end MPUCircuit
