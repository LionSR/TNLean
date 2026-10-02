/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.MinimalIntervalLeafColumns
import TNLean.MPS.MPU.BasisEncodingCoordinates

/-!
# Exact column identities under coordinate changes

Initialized column identities are transported along physical and input-output
coordinate bijections. A full clean implementation determines its logical
initialized columns by cancellation of the isometric workspace inclusion.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5.
-/

open Matrix MPSPreparation MPSTensor

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
    (h : X * initializedBasisMatrix E = initializedBasisMatrix G * V) :
    Matrix.reindex e e X * initializedBasisMatrix F =
      initializedBasisMatrix H * Matrix.reindex g f V := by
  rw [← initializedBasisMatrix_reindex_of_mapping e f E F hE,
    ← initializedBasisMatrix_reindex_of_mapping e g G H hG]
  change Matrix.reindexLinearEquiv ℂ ℂ e e X *
      Matrix.reindexLinearEquiv ℂ ℂ e f (initializedBasisMatrix E) =
    Matrix.reindexLinearEquiv ℂ ℂ e g (initializedBasisMatrix G) *
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

namespace MPSPreparation.IsCleanImplementation

/-- The ambient initialized columns determine the exact logical initialized columns.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem logical_columns_of_ambient {ι κ μ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    {J : Matrix ι κ ℂ} {C : Matrix ι ι ℂ} {Z : Matrix κ κ ℂ}
    (h : IsCleanImplementation J C Z) (hJ : J.IsIsometry)
    (E F : Matrix κ μ ℂ) (hc : C * (J * E) = J * F) : Z * E = F := by
  change C * J = J * Z at h
  change Jᴴ * J = 1 at hJ
  have hh : J * (Z * E) = J * F := by
    simpa only [← Matrix.mul_assoc, ← h] using hc
  have hcancel := congrArg (fun M ↦ Jᴴ * M) hh
  simpa only [← Matrix.mul_assoc, hJ, Matrix.one_mul] using hcancel

end MPSPreparation.IsCleanImplementation
