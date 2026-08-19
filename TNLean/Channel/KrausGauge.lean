/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.MatrixSqrt
import TNLean.Channel.GaugeConjugation
import TNLean.Channel.Schwarz.Basic

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# TP gauge for finite Kraus families

A positive definite fixed point of the adjoint Kraus map gives the standard
trace-preserving gauge normalization `K i ↦ ρ^{1/2} K i ρ^{-1/2}`.

`TNLean.MPS.Core.TPGauge` restates this construction in transfer-map notation
(since `MPSTensor d D` is definitionally a finite matrix family, the two
constructions coincide) and adds the unital gauge and the gauge-equivalence
statements.

## Main declarations

* `Kraus.tpGauge`: the gauged Kraus family `i ↦ ρ^{1/2} K i ρ^{-1/2}`.
* `Kraus.tpGauge_isTP_of_map_conjTranspose_fixedPoint`: the gauged family is
  trace preserving when `ρ` is a positive definite fixed point of the
  conjugate-transposed Kraus map.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Section 6.2][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators

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

This is the standard "left-canonical" gauge construction, the specialization
`S = ρ^{1/2}` of `gauged_isTP_of_map_conjTranspose_fixedPoint`. -/
theorem tpGauge_isTP_of_map_conjTranspose_fixedPoint
    (K : Fin d → Mat) (ρ : Mat)
    (hρ : ρ.PosDef)
    (hfix : map (fun i => (K i)ᴴ) ρ = ρ) :
    IsTP (tpGauge K ρ) := by
  have hS_herm : (CFC.sqrt ρ)ᴴ = CFC.sqrt ρ := Matrix.conjTranspose_cfc_sqrt (ρ := ρ)
  have hStS : (CFC.sqrt ρ)ᴴ * CFC.sqrt ρ = ρ := by
    rw [hS_herm]
    simpa using CFC.sqrt_mul_sqrt_self ρ hρ.posSemidef.nonneg
  exact gauged_isTP_of_map_conjTranspose_fixedPoint K (CFC.sqrt ρ) ρ
    hρ.isUnit_det_cfc_sqrt hStS hfix

end Kraus
