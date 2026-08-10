/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SimpleBlocking

/-!
# Two-step reblocking of supplied MPU-simple witnesses

This file applies the shared supplied-witness reblocking machinery twice, preserving the
specified `simple2` witnesses at a direct block two sites longer, and combines the result with
`simple1` for the same witnesses.

Source: arXiv:1703.09188, corollary following Proposition III.3, lines
442--446.
-/

open scoped Matrix

namespace MPOTensor

private lemma blockTensor_add_two_simple2
    {d D : ℕ} {U : MPOTensor d D} {k : ℕ}
    (a b : Fin (D * D) → ℂ)
    (h₂ : ∀ i j m l : Fin (MPSTensor.blockPhysDim d k),
      doubleLayerTensor (blockTensor U k) i j *
          doubleLayerTensor (blockTensor U k) m l =
        doubleLayerTensor (blockTensor U k) i j * Matrix.vecMulVec b a *
          doubleLayerTensor (blockTensor U k) m l) :
    ∀ I J K L : Fin (MPSTensor.blockPhysDim d (k + 2)),
      doubleLayerTensor (blockTensor U (k + 2)) I J *
          doubleLayerTensor (blockTensor U (k + 2)) K L =
        doubleLayerTensor (blockTensor U (k + 2)) I J * Matrix.vecMulVec b a *
          doubleLayerTensor (blockTensor U (k + 2)) K L := by
  have h₂₁ := blockTensor_succ_simple2_of_supplied (a := a) (b := b) h₂
  have h₂₂ := blockTensor_succ_simple2_of_supplied (a := a) (b := b) h₂₁
  simpa only [Nat.add_assoc, Nat.reduceAdd] using h₂₂

/-- Exact supplied witnesses extend from a direct block of length $k$ to the
common overlapping-window block of length $k+2$, without replacing them by
existentially chosen witnesses.

Source: arXiv:1703.09188, corollary following Proposition III.3, lines
442--446. -/
theorem IsMPU.blockTensor_add_two_simple_contractions_of_supplied
    {d D : ℕ} {U : MPOTensor d D} (hU : IsMPU U) {k : ℕ}
    (a b : Fin (D * D) → ℂ)
    (h₂ : ∀ i j m l : Fin (MPSTensor.blockPhysDim d k),
      doubleLayerTensor (MPOTensor.blockTensor U k) i j *
          doubleLayerTensor (MPOTensor.blockTensor U k) m l =
        doubleLayerTensor (MPOTensor.blockTensor U k) i j * Matrix.vecMulVec b a *
          doubleLayerTensor (MPOTensor.blockTensor U k) m l) :
    (∀ I J : Fin (MPSTensor.blockPhysDim d (k + 2)),
      a ⬝ᵥ (doubleLayerTensor (MPOTensor.blockTensor U (k + 2)) I J *ᵥ b) =
        if I = J then 1 else 0) ∧
    (∀ I J K L : Fin (MPSTensor.blockPhysDim d (k + 2)),
      doubleLayerTensor (MPOTensor.blockTensor U (k + 2)) I J *
          doubleLayerTensor (MPOTensor.blockTensor U (k + 2)) K L =
        doubleLayerTensor (MPOTensor.blockTensor U (k + 2)) I J * Matrix.vecMulVec b a *
          doubleLayerTensor (MPOTensor.blockTensor U (k + 2)) K L) := by
  have h₂add := blockTensor_add_two_simple2 (a := a) (b := b) h₂
  exact ⟨IsMPU.simple1_of_simple2_supplied (hU.blockTensor (k + 2) (by omega)) a b h₂add,
    h₂add⟩

end MPOTensor
