/-
Copyright (c) 2026 Sirui Lu and TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Algebra.MatrixGramUnitary
import TNLean.Channel.RadonNikodym

/-!
# Unitary open-system representation

This file proves the unitary form of Wolf's open-system representation theorem
from the isometric Stinespring form.  The linear-algebra step is the rectangular
Gram theorem from `TNLean.Algebra.MatrixGramUnitary`: two maps with the same
Gram matrix differ by a unitary on the codomain.

## Main results

* `Matrix.firstEnvEmbedding` — the embedding of the system into the first
  coordinate of an environment.
* `IsChannel.exists_stinespring_open_system_unitary` — Wolf Theorem 2.5 in
  unitary open-system form.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 2.5]
  [Wolf2012QChannels]
-/

open scoped Matrix
open Matrix

variable {D : ℕ}

namespace Matrix

/-- The embedding `x ↦ x ⊗ e₀` into the first coordinate of an environment. -/
def firstEnvEmbedding (D r : ℕ) (hr : 0 < r) :
    Matrix (Fin D × Fin r) (Fin D) ℂ :=
  fun ik j =>
    if ik.2 = ⟨0, hr⟩ then (1 : Matrix (Fin D) (Fin D) ℂ) ik.1 j else 0

/-- `firstEnvEmbedding` embeds into the zero environment coordinate as the identity. -/
@[simp]
theorem firstEnvEmbedding_apply_zero (D r : ℕ) (hr : 0 < r)
    (i j : Fin D) :
    firstEnvEmbedding D r hr (i, ⟨0, hr⟩) j =
      (1 : Matrix (Fin D) (Fin D) ℂ) i j := by
  simp [firstEnvEmbedding]

/-- `firstEnvEmbedding` is zero away from the zero environment coordinate. -/
@[simp]
theorem firstEnvEmbedding_apply_ne (D r : ℕ) (hr : 0 < r)
    (i j : Fin D) {k : Fin r} (hk : k ≠ ⟨0, hr⟩) :
    firstEnvEmbedding D r hr (i, k) j = 0 := by
  simp [firstEnvEmbedding, hk]

/-- The first-coordinate environment embedding is an isometry. -/
theorem firstEnvEmbedding_conjTranspose_mul_self (D r : ℕ) (hr : 0 < r) :
    (firstEnvEmbedding D r hr)ᴴ * firstEnvEmbedding D r hr = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  by_cases hij : i = j
  · simp [firstEnvEmbedding, Matrix.one_apply, hij]
  · have hji : j ≠ i := fun h => hij h.symm
    simp [firstEnvEmbedding, Matrix.one_apply, hij, hji]

end Matrix

namespace IsChannel

private theorem stinespring_environment_pos [NeZero D]
    {r : ℕ} {V : Matrix (Fin D × Fin r) (Fin D) ℂ}
    (hV : Vᴴ * V = 1) :
    0 < r := by
  by_contra hr
  have hr0 : r = 0 := Nat.eq_zero_of_not_pos hr
  let j : Fin D := ⟨0, NeZero.pos D⟩
  have hdiag := congr_fun (congr_fun hV j) j
  subst r
  simp [Matrix.mul_apply] at hdiag

/-- **Wolf Theorem 2.5 (unitary open-system representation).**

For a nonzero finite-dimensional system, every quantum channel has a
system-plus-environment unitary realization.  The matrix
`Matrix.firstEnvEmbedding D r hr` inserts the system into the first
environment coordinate, so the middle factor is `ρ ⊗ |0⟩⟨0|` in matrix form. -/
theorem exists_stinespring_open_system_unitary [NeZero D]
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsChannel T) :
    ∃ (r : ℕ) (hr : 0 < r) (U : Matrix.unitaryGroup (Fin D × Fin r) ℂ),
      ∀ ρ : Matrix (Fin D) (Fin D) ℂ,
        T ρ =
          ((U : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) *
            (Matrix.firstEnvEmbedding D r hr * ρ *
              (Matrix.firstEnvEmbedding D r hr)ᴴ) *
            (U : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ)ᴴ).traceRight := by
  obtain ⟨r, V, hV, htrace⟩ := hT.exists_stinespring_open_system_traceRight
  have hr : 0 < r := stinespring_environment_pos (D := D) (V := V) hV
  let W : Matrix (Fin D × Fin r) (Fin D) ℂ := Matrix.firstEnvEmbedding D r hr
  have hW : Wᴴ * W = 1 :=
    Matrix.firstEnvEmbedding_conjTranspose_mul_self D r hr
  obtain ⟨U, hU⟩ := Matrix.exists_unitary_mul_eq_of_conjTranspose_mul_eq
    (B := V) (A := W) (by rw [hV, hW])
  refine ⟨r, hr, U, ?_⟩
  intro ρ
  rw [htrace ρ, hU]
  simp [W, Matrix.conjTranspose_mul, Matrix.mul_assoc]

end IsChannel
