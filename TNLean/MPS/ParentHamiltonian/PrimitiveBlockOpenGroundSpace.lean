/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockOpenGroundSpace
import TNLean.MPS.ParentHamiltonian.PrimitiveBlockWordSpan

/-!
# Open-chain ground spaces of primitive block sums

For a finite family of pairwise inequivalent normalized primitive blocks,
one interaction threshold identifies every longer open-chain ground space
with the space of boundary-condition vectors of the weighted direct sum.
This is the open-chain part of PGVWC07, arXiv:quant-ph/0608197, Theorem 12,
and the finite-volume ground-space input in Nachtergaele,
arXiv:cond-mat/9410110, equations (3.12)--(3.16).
-/

open scoped ComplexOrder

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ} [NeZero d] [∀ j, NeZero (dim j)]

/-- Every sufficiently long interaction gives the full boundary-condition
space as the open-chain kernel for a direct sum of inequivalent primitive
blocks. The threshold is independent of the chain length. This is the
open-segment conclusion of PGVWC07, Theorem 12, lines 1430--1454. -/
theorem exists_ker_openParentHamiltonianES_toTensorFromBlocks_eq_groundSpaceES_of_isPrimitiveMPS
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, IsPrimitiveMPS (A j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : dim j = dim i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i)) :
    ∃ L₀ : ℕ, 0 < L₀ ∧ ∀ L N : ℕ, L₀ ≤ L → L ≤ N →
      LinearMap.ker
          (openParentHamiltonianES (toTensorFromBlocks (d := d) (μ := μ) A) L N) =
        groundSpaceES (toTensorFromBlocks (d := d) (μ := μ) A) N := by
  exact (exists_eventually_wordTupleSpanTop_of_isPrimitiveMPS A ρ hP hρ hDistinct).elim
    fun L₀ hSpan ↦ ⟨L₀ + 1, Nat.succ_pos L₀, fun L N hL hLN ↦
      ker_openParentHamiltonianES_toTensorFromBlocks_eq_groundSpaceES
        μ A hμ (fun j ↦ (hP j).norm) hSpan hL hLN⟩

end MPSTensor
