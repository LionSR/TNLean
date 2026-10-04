/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Chain.VaryingBondOBC

/-!
# Zero padding of rectangular products

Rectangular bond matrices are represented in a common square matrix space
by extending their entries by zero. Multiplication is preserved whenever
the intermediate bond dimension fits in that space. The same identity for
matrix-vector multiplication allows successive bond-coordinate maps to
be evaluated in the existing open-boundary chain representation.

These are the coordinate identities used in the minimal representation
step of Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.
-/

namespace Matrix

variable {R : Type*} [Semiring R] {a b c D : ℕ}

/-- Zero padding preserves a rectangular matrix product when the intermediate
dimension is at most the padding dimension. The outer dimensions need not
be bounded. Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem zeroPad_mul (X : Matrix (Fin a) (Fin b) R)
    (Y : Matrix (Fin b) (Fin c) R) (hb : b ≤ D) :
    zeroPad D (X * Y) = zeroPad D X * zeroPad D Y := by
  ext i j
  by_cases hi : i.val < a
  · by_cases hj : j.val < c
    · rw [zeroPad_apply_of_lt _ hi hj, Matrix.mul_apply, Matrix.mul_apply]
      rw [Fin.sum_castLE_extend_zero _ hb]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k.val < b
      · simp [zeroPad, hi, hj, hk]
      · simp [zeroPad, hi, hk]
    · simp [zeroPad, Matrix.mul_apply, hj]
  · simp [zeroPad, Matrix.mul_apply, hi]

/-- Applying a zero-padded rectangular matrix to a zero-padded vector gives
the zero padding of their product. Source: the minimal representation step
in Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem zeroPad_mulVec (X : Matrix (Fin a) (Fin b) R) (v : Fin b → R) (hb : b ≤ D) :
    zeroPad D X *ᵥ (fun j : Fin D ↦ if h : j.val < b then v ⟨j.val, h⟩ else 0) =
      fun i : Fin D ↦ if h : i.val < a then (X *ᵥ v) ⟨i.val, h⟩ else 0 := by
  ext i
  by_cases hi : i.val < a
  · simp only [zeroPad, hi, dite_true, mulVec, dotProduct]
    rw [Fin.sum_castLE_extend_zero _ hb]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j.val < b <;> simp [hj]
  · simp [zeroPad, mulVec, dotProduct, hi]

end Matrix
