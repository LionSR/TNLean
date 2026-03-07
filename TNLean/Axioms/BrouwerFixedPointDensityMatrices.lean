/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.PositiveMap

/-!
# Brouwer fixed-point input on density matrices

This module isolates the current trusted topological input used in the
Perron--Frobenius / TP-gauge existence pipeline: Brouwer's fixed-point theorem,
specialized to the compact convex set of density matrices.

A proof of Brouwer's fixed-point theorem (or an equivalent finite-dimensional
fixed-point theorem) is not currently available in Mathlib, so the specialized
statement is assumed here and imported explicitly by the downstream
Perron--Frobenius existence module.
-/

open scoped Matrix ComplexOrder MatrixOrder

variable {D : ℕ}

/-- **Brouwer fixed point theorem on density matrices** (axiom).

If `f` is continuous on the set of density matrices and maps density matrices to density matrices,
then it has a fixed point in the set of density matrices.

This is the only trusted topological input currently needed for the
Perron--Frobenius existence step in `TNLean.Channel.PerronFrobeniusExistence`. -/
axiom brouwer_fixedPoint_densityMatrices
    {D : ℕ} [NeZero D]
    {f : Matrix (Fin D) (Fin D) ℂ → Matrix (Fin D) (Fin D) ℂ}
    (hf_cont : ContinuousOn f (densityMatrices D))
    (hf_map : Set.MapsTo f (densityMatrices D) (densityMatrices D)) :
    ∃ ρ ∈ densityMatrices D, f ρ = ρ
