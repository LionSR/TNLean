/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.Blocking
import TNLean.MPS.MPDO.BiCFDerivation.Core

/-!
# Pair separation under physical blocking

This file transports homogeneous pair trace separation through physical
blocking.  A blocked word of length `N` is identified with its flattened
ordinary word of length `N * p`.

The result is the finite-word transport used in the block-injectivity argument
of arXiv:1606.00608, lines 318--344.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

/-- Pair trace separation at original length `N * p` gives pair trace
separation at blocked length `N`.

This is the finite-word transport implicit in the passage from injective
representatives to block injectivity in arXiv:1606.00608, lines 318--344. -/
theorem pairTraceSeparatingAt_blockTensor
    {D₁ D₂ : ℕ} (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (p N : ℕ) (hSep : PairTraceSeparatingAt A B (N * p)) :
    PairTraceSeparatingAt
      (blockTensor (d := d) (D := D₁) A p)
      (blockTensor (d := d) (D := D₂) B p) N := by
  intro ΔA ΔB hΔ
  apply hSep ΔA ΔB
  intro τ
  let σ := (blockedConfigEquiv d N p).symm τ
  have hσ := hΔ σ
  simp only [evalWord_blockTensor] at hσ
  rw [← ofFn_blockedConfigEquiv] at hσ
  simpa [σ] using hσ

end MPSTensor
