/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.Physical.Blocking
import QICLean.Kraus.Transfer
import QICLean.Kraus.BlockingTransfer
import QICLean.Kraus.MixedMap.Basic

import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Transfer maps under physical blocking

The transfer map of a physically blocked tensor is the corresponding iterate of the
original transfer map (`Kraus.transferMap_block`). As consequences,
`transferMap_block_quasi_idempotent` transports quasi-idempotence through blocking,
`transferMap_block_mul` compares iterated and direct blocking, and `mixedMapLM_block_apply`
computes blocked mixed transfer maps; fixed points are `Kraus.transferMap_block_fixedPoint`.
-/

open scoped Matrix ComplexOrder BigOperators

namespace MPSTensor

variable {α : Type*} [Fintype α] {D : ℕ}

/-- Quasi-idempotence propagates through physical blocking, with the scalar raised to the
blocking length. -/
theorem transferMap_block_quasi_idempotent
    (A : MPTensor α (Fin D)) (L : ℕ) (c : ℂ)
    (h : Kraus.transferMap A * Kraus.transferMap A = c • Kraus.transferMap A) :
    Kraus.transferMap (Kraus.block A L) * Kraus.transferMap (Kraus.block A L) =
      c ^ L • Kraus.transferMap (Kraus.block A L) := by
  rw [Kraus.transferMap_block]
  calc
    Kraus.transferMap A ^ L * Kraus.transferMap A ^ L = (Kraus.transferMap A ^ L) ^ 2 := by
      rw [pow_two]
    _ = (Kraus.transferMap A ^ 2) ^ L := by
      simpa only [pow_mul] using congrArg (fun n : ℕ => Kraus.transferMap A ^ n) (Nat.mul_comm L 2)
    _ = (c • Kraus.transferMap A) ^ L := by rw [pow_two, h]
    _ = c ^ L • Kraus.transferMap A ^ L := by rw [smul_pow]

/-- Iterated physical blocking is compatible with direct blocking by the multiplied period,
at the transfer-map level:
`Kraus.transferMap(block(block(A, m), n)) = Kraus.transferMap(block(A, m * n))`. -/
theorem transferMap_block_mul (A : MPTensor α (Fin D)) (m n : ℕ) :
    Kraus.transferMap (Kraus.block (Kraus.block A m) n) =
      Kraus.transferMap (Kraus.block A (m * n)) := by
  rw [Kraus.transferMap_block, Kraus.transferMap_block, Kraus.transferMap_block, pow_mul]

/-- The mixed transfer map of two `L`-site blocked tensors is the `L`-th power of the mixed
transfer map of the tensors. -/
theorem mixedMapLM_block_apply {D₁ D₂ : ℕ} (X : MPTensor α (Fin D₁)) (Y : MPTensor α (Fin D₂))
    (L : ℕ) (Z : Matrix (Fin D₁) (Fin D₂) ℂ) :
    Kraus.mixedMapLM (Kraus.block X L) (Kraus.block Y L) Z = (Kraus.mixedMapLM X Y ^ L) Z := by
  rw [Kraus.mixedMapLM_pow_apply, Kraus.mixedMapLM_apply]
  rfl

end MPSTensor
