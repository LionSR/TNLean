/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.PositiveMap

/-!
# Brouwer fixed point theorem on density matrices (assumed)

This file introduces an axiom asserting Brouwer's fixed point theorem, specialized to the
compact convex set of density matrices.

**Note**: A proof of Brouwer's fixed point theorem (or an equivalent finite-dimensional fixed
point theorem) is not currently available in Mathlib, so we assume it here.
-/

open scoped Matrix ComplexOrder MatrixOrder

variable {D : ℕ}

/-- **Brouwer fixed point theorem on density matrices** (axiom).

If `f` is continuous on the set of density matrices and maps density matrices to density matrices,
then it has a fixed point in the set of density matrices.

This is the only non-constructive/topological input needed for the Perron–Frobenius existence
step in `PerronFrobeniusExistence.lean`. -/
axiom brouwer_fixedPoint_densityMatrices
    {D : ℕ} [NeZero D]
    {f : Matrix (Fin D) (Fin D) ℂ → Matrix (Fin D) (Fin D) ℂ}
    (hf_cont : ContinuousOn f (densityMatrices D))
    (hf_map : Set.MapsTo f (densityMatrices D) (densityMatrices D)) :
    ∃ ρ ∈ densityMatrices D, f ρ = ρ
