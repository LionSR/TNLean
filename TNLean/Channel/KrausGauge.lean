/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.MatrixSqrt
import TNLean.Channel.Schwarz.Basic

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# TP gauge for finite Kraus families

A positive definite fixed point of the adjoint Kraus map gives the standard
trace-preserving gauge normalization `K i ↦ ρ^{1/2} K i ρ^{-1/2}`.

The MPS transfer-map specialization (together with the unital gauge and the
gauge-equivalence statements) lives in `TNLean.MPS.Core.TPGauge`.

## Main declarations

* `Kraus.tpGauge`: the gauged Kraus family `i ↦ ρ^{1/2} K i ρ^{-1/2}`.
* `Kraus.tpGauge_isTP_of_map_conjTranspose_fixedPoint`: the gauged family is
  trace preserving when `ρ` is a positive definite fixed point of the
  conjugate-transposed Kraus map.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Section 6.2][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix Finset

namespace Kraus

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- Gauge-transformed Kraus family `B i = ρ^{1/2} K i ρ^{-1/2}`.

We implement `ρ^{1/2}` as `CFC.sqrt ρ`.
(For `ρ` positive definite, this is invertible.) -/
noncomputable def tpGauge (K : Fin d → Mat) (ρ : Mat) : Fin d → Mat :=
  fun i => (CFC.sqrt ρ) * K i * (CFC.sqrt ρ)⁻¹

/-- **TP normalisation from an adjoint fixed point.**

Assume `ρ` is positive definite and fixed by the conjugate-transposed Kraus map
`X ↦ ∑ i, (K i)ᴴ * X * K i`. Then the gauged family `tpGauge K ρ` is trace
preserving: `∑ i, (B i)ᴴ * B i = I`.

This is the standard "left-canonical" gauge construction. -/
theorem tpGauge_isTP_of_map_conjTranspose_fixedPoint
    (K : Fin d → Mat) (ρ : Mat)
    (hρ : ρ.PosDef)
    (hfix : map (fun i => (K i)ᴴ) ρ = ρ) :
    IsTP (tpGauge K ρ) := by
  classical
  -- Notation.
  set S : Mat := CFC.sqrt ρ
  have hS_mul : S * S = ρ := by
    simpa [S] using CFC.sqrt_mul_sqrt_self ρ hρ.posSemidef.nonneg
  have hS_herm : Sᴴ = S := by
    simpa [S] using Matrix.conjTranspose_cfc_sqrt (ρ := ρ)
  have hStS : Sᴴ * S = ρ := by
    simpa [hS_herm] using hS_mul
  -- Invertibility facts (in the `Matrix` ring inverse sense).
  have hdet : IsUnit S.det := by
    simpa [S] using hρ.isUnit_det_cfc_sqrt
  have hSmul_inv : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hdet
  have hdetT : IsUnit (Sᴴ.det) := by
    simpa [Matrix.det_conjTranspose] using (IsUnit.star hdet)
  have hStinv_mul : (Sᴴ)⁻¹ * Sᴴ = 1 := Matrix.nonsing_inv_mul Sᴴ hdetT
  -- Rewrite each summand.
  have h_term : ∀ i : Fin d,
      (S * K i * S⁻¹)ᴴ * (S * K i * S⁻¹) = (Sᴴ)⁻¹ * ((K i)ᴴ * ρ * K i) * S⁻¹ := by
    intro i
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv]
    simp [Matrix.mul_assoc, ← hStS]
  -- Identify the adjoint fixed point equation as a sum.
  have h_sum_eq : ∑ i : Fin d, (K i)ᴴ * ρ * K i = ρ := by
    simpa [map_apply, Matrix.mul_assoc] using hfix
  -- Compute the TP normalisation.
  change (∑ i : Fin d, (S * K i * S⁻¹)ᴴ * (S * K i * S⁻¹)) = 1
  simp_rw [h_term]
  rw [← Finset.sum_mul, ← Finset.mul_sum, h_sum_eq, ← hStS]
  simp [Matrix.mul_assoc, hStinv_mul, hSmul_inv]

end Kraus
