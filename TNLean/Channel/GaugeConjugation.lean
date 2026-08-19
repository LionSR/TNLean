/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Schwarz.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Gauge conjugation of Kraus families

The general trace-preserving normalisation: conjugating a Kraus family by an
invertible gauge whose Gram matrix is a fixed point of the conjugate-transposed
Kraus map yields a trace-preserving family. The `ρ^{1/2}` specialization lives
in `TNLean.Channel.KrausGauge`.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix Finset

namespace Kraus

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

/-- **TP normalisation from an adjoint fixed point, general gauge.**

If `S` is invertible with `Sᴴ * S = σ` and `σ` is fixed by the
conjugate-transposed Kraus map `X ↦ ∑ i, (K i)ᴴ * X * K i`, then the gauged
family `i ↦ S * K i * S⁻¹` is trace preserving. -/
theorem gauged_isTP_of_map_conjTranspose_fixedPoint
    (K : ι → Matrix n n ℂ) (S σ : Matrix n n ℂ)
    (hS_det : IsUnit S.det)
    (hStS : Sᴴ * S = σ)
    (hfix : map (fun i => (K i)ᴴ) σ = σ) :
    IsTP (fun i => S * K i * S⁻¹) := by
  have hSmul_inv : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hS_det
  have hdetT : IsUnit (Sᴴ.det) := by
    simpa [Matrix.det_conjTranspose] using (IsUnit.star hS_det)
  have hStinv_mul : (Sᴴ)⁻¹ * Sᴴ = 1 := Matrix.nonsing_inv_mul Sᴴ hdetT
  -- Rewrite each summand.
  have h_term : ∀ i : ι,
      (S * K i * S⁻¹)ᴴ * (S * K i * S⁻¹) =
        (Sᴴ)⁻¹ * ((K i)ᴴ * σ * K i) * S⁻¹ := by
    intro i
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv]
    simp [Matrix.mul_assoc, ← hStS]
  -- Identify the adjoint fixed point equation as a sum.
  have h_sum_eq : ∑ i : ι, (K i)ᴴ * σ * K i = σ := by
    simpa [map_apply, Matrix.mul_assoc] using hfix
  -- Compute the TP normalisation.
  change (∑ i : ι, (S * K i * S⁻¹)ᴴ * (S * K i * S⁻¹)) = 1
  simp_rw [h_term]
  rw [← Finset.sum_mul, ← Finset.mul_sum, h_sum_eq, ← hStS]
  simp [Matrix.mul_assoc, hStinv_mul, hSmul_inv]

end Kraus
