/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.FixedPoint.Cesaro
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Spanning by stationary density matrices

This file proves Wolf Corollary 6.8 (Linearly independent stationary states):
the fixed-point space of a positive trace-preserving linear map is spanned by
stationary density matrices.

## Source

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Corollary 6.8; local
  source `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1204--1218.
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

variable {D : ℕ}

/-- A stationary density matrix for a linear map `E`. -/
structure IsStationaryDensity
    (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) : Prop where
  posSemidef : ρ.PosSemidef
  trace_one : Matrix.trace ρ = (1 : ℂ)
  fixed_point : E ρ = ρ

namespace IsPositiveMap

variable (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)

/-- The fixed-point subspace of `E`. -/
def fixedPointsSubmodule (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    Submodule ℂ (Matrix (Fin D) (Fin D) ℂ) where
  carrier := {X | E X = X}
  add_mem' {a b} ha hb := by
    simp at ha hb
    show E (a + b) = a + b
    rw [LinearMap.map_add, ha, hb]
  zero_mem' := by simp
  smul_mem' c {a} ha := by
    simp at ha
    show E (c • a) = c • a
    rw [LinearMap.map_smul, ha]

lemma mem_fixedPointsSubmodule {X : Matrix (Fin D) (Fin D) ℂ} :
    X ∈ fixedPointsSubmodule E ↔ E X = X := Iff.rfl

/-- The set of PSD fixed points. -/
def posSemidefFixedPointsSet (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    Set (Matrix (Fin D) (Fin D) ℂ) :=
  {X | X ∈ fixedPointsSubmodule E ∧ X.PosSemidef}

lemma mem_posSemidefFixedPointsSet {X : Matrix (Fin D) (Fin D) ℂ} :
    X ∈ posSemidefFixedPointsSet E ↔ E X = X ∧ X.PosSemidef := by
  simp [posSemidefFixedPointsSet, IsPositiveMap.mem_fixedPointsSubmodule]

/-- Every fixed point is a ℂ-linear combination of PSD fixed points
(by Wolf Proposition 6.8). -/
lemma fixedPoint_mem_span_posSemidef
    (hE : IsPositiveMap E) (hTP : IsTracePreservingMap E)
    {X : Matrix (Fin D) (Fin D) ℂ} (hX_fix : E X = X) :
    X ∈ Submodule.span ℂ (posSemidefFixedPointsSet E) := by
  obtain ⟨P₁, P₂, P₃, P₄, hP₁, hP₂, hP₃, hP₄, hFP₁, hFP₂, hFP₃, hFP₄, h_decomp⟩ :=
    IsPositiveMap.exists_posSemidef_fixedPoints_decomposition E hE hTP hX_fix
  have mem (P : Matrix (Fin D) (Fin D) ℂ) (hPf : E P = P) (hPp : P.PosSemidef) :
      P ∈ Submodule.span ℂ (posSemidefFixedPointsSet E) :=
    Submodule.subset_span (by
      rw [IsPositiveMap.mem_posSemidefFixedPointsSet]
      exact ⟨hPf, hPp⟩)
  rw [h_decomp]
  refine Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.sub_mem _
    (mem P₁ hFP₁ hP₁) (mem P₂ hFP₂ hP₂)))
    (Submodule.smul_mem _ _ (Submodule.sub_mem _
      (mem P₃ hFP₃ hP₃) (mem P₄ hFP₄ hP₄)))

/-- The fixed-point subspace is spanned by its PSD elements. -/
lemma fixedPointsSubmodule_top_span_by_posSemidef
    (hE : IsPositiveMap E) (hTP : IsTracePreservingMap E) :
    Submodule.span ℂ (posSemidefFixedPointsSet E) = fixedPointsSubmodule E := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro X ⟨hX_mem, -⟩
    exact hX_mem
  · intro X hX
    rcases (IsPositiveMap.mem_fixedPointsSubmodule (E := E)).mp hX with hX_fix
    exact fixedPoint_mem_span_posSemidef E hE hTP hX_fix

end IsPositiveMap
