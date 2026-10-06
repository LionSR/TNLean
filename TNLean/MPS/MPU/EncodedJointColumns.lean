/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.ColumnCoordinateTransport
import TNLean.MPS.MPU.JoiningSpectatorColumns

/-!
# Joint child columns in the merger coordinates

Exact initialized columns are transported by physical and input-output
coordinate bijections. The active joining inclusion is then expressed
inside the compatible dilation inclusion.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5.
-/

open Matrix MPSPreparation MPSTensor
open scoped Kronecker

namespace MPUCircuit

/-- Exact individual child columns give the encoded joint columns after derived basis changes.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem encodedJointColumns_of_coordinate_identities
    {d r q a : ℕ} {ι α β γ ρ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype γ] [Fintype ρ] [DecidableEq ρ]
    (hd : 2 ≤ d) (f : ρ ↪ Cfg d a) (eb : Fin r ↪ Cfg d q)
    (ec : ι ≃ Cfg d (a + (2 * q + 2)))
    (u : α ≃ β) (g : γ ≃ (ρ × (Fin r × Fin r)))
    (E : α ↪ ι) (G : γ ↪ ι)
    (F : β ↪ Cfg d (a + (2 * q + 2)))
    (hE : ∀ b, ec (E (u.symm b)) = F b)
    (hG : ∀ p, ec (G (g.symm p)) =
      appendBasisEmbedding f ((joiningChildBasisEmbedding (r := r) hd).trans
        (compatibleBondDilationEmbedding hd eb)) p)
    (X Y : Matrix ι ι ℂ) (W : Matrix γ α ℂ)
    (V : Matrix (ρ × (Fin r × Fin r)) β ℂ)
    (hW : Matrix.reindex g u W = V)
    (h : (X * Y) * initializedBasisMatrix E = initializedBasisMatrix G * W) :
    (Matrix.reindex ec ec X * Matrix.reindex ec ec Y) * initializedBasisMatrix F =
      initializedBasisMatrix (appendBasisEmbedding f (compatibleBondDilationEmbedding hd eb)) *
        ((1 : Matrix ρ ρ ℂ) ⊗ₖ
          initializedBasisMatrix (joiningChildBasisEmbedding (r := r) hd)) * V := by
  have ht := matrix_columns_reindex ec u g E G F
    (appendBasisEmbedding f ((joiningChildBasisEmbedding (r := r) hd).trans
      (compatibleBondDilationEmbedding hd eb))) hE hG (X * Y) W h
  rw [hW, initializedBasisMatrix_append_joiningChild] at ht
  change Matrix.reindexLinearEquiv ℂ ℂ ec ec (X * Y) * initializedBasisMatrix F = _ at ht
  rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ ec ec ec X Y] at ht
  exact ht

/-- Reindexing the input of a normalized joining isometry preserves its Gram.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem normalizedJoiningParent_input_reindex_isIsometry
    {r : ℕ} {ρ μ ν : Type*} [Fintype ρ] [DecidableEq ρ]
    [DecidableEq μ] [DecidableEq ν]
    (hr : 0 < r) (P : Matrix (Fin r) (Fin r) ℂ)
    (V : Matrix (ρ × (Fin r × Fin r)) μ ℂ) (u : μ ≃ ν)
    (hV : (normalizedJoiningParent hr P V).IsIsometry) :
    (normalizedJoiningParent hr P (V.submatrix id u.symm)).IsIsometry := by
  rw [normalizedJoiningParent_submatrix_columns]
  exact hV.reindex _ (Equiv.refl _) u

/-- Spectator states and an input coordinate bijection preserve the normalized parent isometry.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem normalizedJoiningParent_spectator_reindex_isIsometry
    {r : ℕ} {ρ μ τ ν : Type*} [Fintype ρ] [DecidableEq ρ]
    [DecidableEq μ] [Fintype τ] [DecidableEq τ] [DecidableEq ν]
    (hr : 0 < r) (P : Matrix (Fin r) (Fin r) ℂ)
    (V : Matrix (ρ × (Fin r × Fin r)) μ ℂ) (u : (μ × τ) ≃ ν)
    (hV : (normalizedJoiningParent hr P V).IsIsometry) :
    (normalizedJoiningParent hr P
      ((joiningSpectatorColumns (τ := τ) V).submatrix id u.symm)).IsIsometry := by
  exact normalizedJoiningParent_input_reindex_isIsometry hr P _ u
    (normalizedJoiningParent_joiningSpectatorColumns_isIsometry hr P V hV)

end MPUCircuit
