/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Axioms.BrouwerFixedPoint
import TNLean.Channel.Basic

/-!
# Stationary states for continuous positive trace-preserving maps

This file proves the existence of stationary states for continuous (not
necessarily linear) positive trace-preserving maps on `M_D(ℂ)`, following
Wolf Theorem 6.11 (Stationary states).

## Main definitions

* `IsPositive` — a map (not necessarily linear) that sends PSD matrices to PSD matrices.
* `IsTracePreserving` — a map (not necessarily linear) that preserves the trace.
* `IsStationaryMap` — the conjunction of continuity, positivity, and trace preservation.

## Main results

* `IsStationaryMap.maps_densityMatrices` — a stationary map sends density matrices
  to density matrices, so it restricts to a continuous self-map of the compact
  convex set of density matrices.
* `IsStationaryMap.exists_stationaryState` — existence of a density-matrix fixed
  point (Wolf Theorem 6.11).

## Source

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 6.11; local source
  `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1152--1159.

-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

variable {D : ℕ}

/-- A map `T : M_D(ℂ) → M_D(ℂ)` is **positive** if it sends positive semidefinite
matrices to positive semidefinite matrices.  This predicate is independent of
linearity. -/
def IsPositive (T : Matrix (Fin D) (Fin D) ℂ → Matrix (Fin D) (Fin D) ℂ) : Prop :=
  ∀ X : Matrix (Fin D) (Fin D) ℂ, X.PosSemidef → (T X).PosSemidef

/-- A map `T : M_D(ℂ) → M_D(ℂ)` is **trace-preserving** if it preserves the
trace of every matrix.  This predicate is independent of linearity. -/
def IsTracePreserving (T : Matrix (Fin D) (Fin D) ℂ → Matrix (Fin D) (Fin D) ℂ) : Prop :=
  ∀ X : Matrix (Fin D) (Fin D) ℂ, Matrix.trace (T X) = Matrix.trace X

/-- A map is a **stationary map** (terminology of Wolf Theorem 6.11) if it is
continuous, positive, and trace-preserving.  Linearity is not required; this
matches the source statement that T is ``continuous, trace-preserving, positive
(not necessarily linear)''.

Source: Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 6.11; local
source `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1152--1159. -/
structure IsStationaryMap
    (T : Matrix (Fin D) (Fin D) ℂ → Matrix (Fin D) (Fin D) ℂ) : Prop where
  continuous : Continuous T
  positive : IsPositive T
  trace_preserving : IsTracePreserving T

namespace IsStationaryMap

variable (T : Matrix (Fin D) (Fin D) ℂ → Matrix (Fin D) (Fin D) ℂ)

/-- A stationary map sends density matrices to density matrices.

If `ρ` is PSD with trace 1, then so is `T(ρ)` — positivity gives PSD, and trace
preservation gives trace 1. -/
lemma maps_densityMatrices (hT : IsStationaryMap T) :
    Set.MapsTo T (densityMatrices D) (densityMatrices D) := by
  intro ρ hρ
  rcases hρ with ⟨hρ_psd, hρ_tr⟩
  refine ⟨hT.positive ρ hρ_psd, ?_⟩
  rw [hT.trace_preserving ρ, hρ_tr]

/-- A stationary map is continuous on the set of density matrices.

This follows from global continuity. -/
lemma continuousOn_densityMatrices (hT : IsStationaryMap T) :
    ContinuousOn T (densityMatrices D) :=
  hT.continuous.continuousOn

/-- **Wolf Theorem 6.11 (Stationary states).**

Every continuous, trace-preserving, positive (not necessarily linear) map
`T : M_D(ℂ) → M_D(ℂ)` has at least one stationary state: a density matrix `ρ`
such that `T(ρ) = ρ`.

The proof is the one given by Wolf: the density matrices form a nonempty compact
convex set, positivity + trace preservation implies `T` restricts to a
continuous self-map of this set, and Brouwer's fixed point theorem (already
proved for density matrices) yields a fixed point.

Source: Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 6.11; local
source `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1152--1159. -/
theorem exists_stationaryState [NeZero D] (hT : IsStationaryMap T) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ, ρ ∈ densityMatrices D ∧ T ρ = ρ :=
  brouwer_fixedPoint_densityMatrices (hT.continuousOn_densityMatrices) (hT.maps_densityMatrices)

/-- **Wolf Theorem 6.11**, alternative formulation: the fixed point is a
density matrix (PSD, trace 1) satisfying `T ρ = ρ`. -/
theorem exists_stationaryState' [NeZero D] (hT : IsStationaryMap T) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ,
      ρ.PosSemidef ∧ Matrix.trace ρ = 1 ∧ T ρ = ρ := by
  obtain ⟨ρ, hρ, hTx⟩ := hT.exists_stationaryState
  exact ⟨ρ, hρ.1, hρ.2, hTx⟩

/-- Compatibility lemma: a linear positive trace-preserving map (in the sense of
`IsPositiveMap` / `IsTracePreservingMap`) is a stationary map, because linear maps
on finite-dimensional spaces are automatically continuous. -/
lemma of_linear (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hPos : IsPositiveMap E) (hTP : IsTracePreservingMap E) :
    IsStationaryMap (fun X => E X) := by
  refine
    { continuous := by
        -- Linear maps on finite-dimensional spaces are continuous
        exact LinearMap.continuous_of_finiteDimensional E
      positive := hPos
      trace_preserving := hTP }

/-- Wolf Theorem 6.11 for a linear positive trace-preserving map (the linear
case that is the setting for Proposition 6.8 and the later fixed-point theory). -/
theorem exists_stationaryState_of_linear [NeZero D]
    (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hPos : IsPositiveMap E) (hTP : IsTracePreservingMap E) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ, ρ ∈ densityMatrices D ∧ E ρ = ρ :=
  exists_stationaryState (fun X => E X) (of_linear E hPos hTP)

/-- Wolf Theorem 6.11 for a quantum channel (linear CPTP map).  This recovers
the existence result already proved by Cesàro means in `Cesaro.lean`, but now via
Brouwer's fixed point theorem (the route taken by Wolf). -/
theorem exists_stationaryState_of_channel [NeZero D]
    (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hE : IsChannel E) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ, ρ ∈ densityMatrices D ∧ E ρ = ρ :=
  exists_stationaryState_of_linear E hE.pos hE.tp

end IsStationaryMap

/-! ### Compatibility bridges with the existing linear-map definitions

The predicates defined above for arbitrary functions coincide with the existing
linear-map predicates when applied to linear maps. -/

theorem IsPositive.eq_of_linear
    (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    IsPositive (fun X => E X) ↔ IsPositiveMap E := by
  simp [IsPositive, IsPositiveMap]

theorem IsTracePreserving.eq_of_linear
    (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    IsTracePreserving (fun X => E X) ↔ IsTracePreservingMap E := by
  simp [IsTracePreserving, IsTracePreservingMap]
