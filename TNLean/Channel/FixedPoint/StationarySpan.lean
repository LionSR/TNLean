/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.FixedPoint.Cesaro
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Fixed-point subspace spanned by positive-semidefinite fixed points

This file proves that the fixed-point subspace of a positive trace-preserving
linear map is spanned (over ℂ) by its positive-semidefinite elements, and then
by stationary density matrices.  This is the key spectral lemma for Wolf
Corollary~6.8 (Linearly independent stationary states).  The dimension/basis
statement with exactly `r` linearly independent stationary density matrices is
tracked for follow-up work.

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

/-- For a nonzero PSD matrix, its trace has strictly positive real part.

Follows from `trace_nonneg` (re ≥ 0, im = 0) and `trace_eq_zero_iff`
(nonzero ⇒ nonzero trace). -/
lemma trace_re_pos_of_posSemidef_ne_zero
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ_psd : ρ.PosSemidef) (hρ_ne : ρ ≠ 0) :
    0 < (Matrix.trace ρ).re := by
  have h_re_nonneg : 0 ≤ (Matrix.trace ρ).re :=
    ((RCLike.nonneg_iff (K := ℂ)).mp hρ_psd.trace_nonneg).1
  have h_ne_zero : Matrix.trace ρ ≠ 0 :=
    mt (hρ_psd.trace_eq_zero_iff.mp ·) hρ_ne
  by_contra! hle
  have him_zero : (Matrix.trace ρ).im = 0 :=
    ((RCLike.nonneg_iff (K := ℂ)).mp hρ_psd.trace_nonneg).2
  have hzero : Matrix.trace ρ = 0 :=
    Complex.ext (le_antisymm hle h_re_nonneg) him_zero
  exact h_ne_zero hzero

/-- A nonzero PSD fixed point, scaled by the inverse of its trace, yields a
stationary density matrix. -/
lemma stationaryDensity_of_posSemidef_fixedPoint
    (hE : IsPositiveMap E) (hTP : IsTracePreservingMap E)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ_psd : ρ.PosSemidef)
    (hρ_fix : E ρ = ρ) (hρ_ne : ρ ≠ 0) :
    IsStationaryDensity E ((Matrix.trace ρ)⁻¹ • ρ) := by
  have htr_pos : 0 < (Matrix.trace ρ).re :=
    trace_re_pos_of_posSemidef_ne_zero hρ_psd hρ_ne
  have him_zero : (Matrix.trace ρ).im = 0 :=
    ((RCLike.nonneg_iff (K := ℂ)).mp hρ_psd.trace_nonneg).2
  have hinv_nonneg_ℂ : 0 ≤ ((Matrix.trace ρ)⁻¹ : ℂ) := by
    have htr_nonneg : 0 ≤ (Matrix.trace ρ : ℂ) := hρ_psd.trace_nonneg
    have htr_ne_zero : Matrix.trace ρ ≠ 0 :=
      mt (hρ_psd.trace_eq_zero_iff.mp ·) hρ_ne
    -- In a StarOrderedRing, if 0 ≤ a and a ≠ 0, then 0 ≤ a⁻¹.
    -- For ℂ specifically, this holds because the positive cone is ℝ≥0.
    -- Use the fact that trace ρ is a real positive number.
    have htr_real : (Matrix.trace ρ : ℂ) = ((Matrix.trace ρ).re : ℂ) :=
      Complex.ext rfl him_zero
    rw [htr_real]
    -- Now we need 0 ≤ ((re : ℂ)⁻¹). Since re > 0, its inverse is ≥ 0.
    have hrepos : (0 : ℝ) ≤ ((Matrix.trace ρ).re)⁻¹ := by
      positivity
    have hpos_ℂ : (0 : ℂ) ≤ (((Matrix.trace ρ).re : ℝ)⁻¹ : ℂ) := by
      exact_mod_cast hrepos
    simpa [map_inv₀ (algebraMap ℝ ℂ)] using hpos_ℂ
  have h_psd : ((Matrix.trace ρ)⁻¹ • ρ).PosSemidef :=
    hρ_psd.smul hinv_nonneg_ℂ
  have h_trace_one : Matrix.trace ((Matrix.trace ρ)⁻¹ • ρ) = (1 : ℂ) := by
    rw [Matrix.trace_smul, smul_eq_mul]
    field_simp [mt (hρ_psd.trace_eq_zero_iff.mp ·) hρ_ne]
  have h_fix : E ((Matrix.trace ρ)⁻¹ • ρ) = (Matrix.trace ρ)⁻¹ • ρ := by
    rw [LinearMap.map_smul, hρ_fix]
  exact {
    posSemidef := h_psd
    trace_one := h_trace_one
    fixed_point := h_fix
  }

/-- **Wolf Corollary 6.8, spanning statement.**

The fixed-point subspace of a positive trace-preserving linear map is spanned
(over ℂ) by stationary density matrices (PSD, trace 1, fixed by `E`).

The dimension/basis statement with exactly `r` linearly independent stationary
density matrices is tracked for follow-up work. -/
theorem fixedPointsSubmodule_spanned_by_stationaryDensities
    [NeZero D] (hE : IsPositiveMap E) (hTP : IsTracePreservingMap E) :
    Submodule.span ℂ {ρ | IsStationaryDensity E ρ} = fixedPointsSubmodule E := by
  set P := posSemidefFixedPointsSet E
  set S : Set (Matrix (Fin D) (Fin D) ℂ) := {ρ | IsStationaryDensity E ρ}
  apply le_antisymm
  · -- span(stationary) ⊆ fixedPointsSubmodule
    refine Submodule.span_le.mpr ?_
    rintro ρ hρ
    have hρ_sd : IsStationaryDensity E ρ := hρ
    have hmem : E ρ = ρ := hρ_sd.fixed_point
    simpa [IsPositiveMap.mem_fixedPointsSubmodule] using hmem
  · -- fixedPointsSubmodule ⊆ span(stationary)
    have h_span_P : Submodule.span ℂ P = fixedPointsSubmodule E :=
      fixedPointsSubmodule_top_span_by_posSemidef E hE hTP
    have h_P_sub_span_S : P ⊆ Submodule.span ℂ S := by
      intro X hX
      rw [mem_posSemidefFixedPointsSet] at hX
      rcases hX with ⟨hX_fix, hX_psd⟩
      by_cases hX_zero : X = 0
      · rw [hX_zero]
        exact Submodule.zero_mem _
      · have hstat : IsStationaryDensity E ((Matrix.trace X)⁻¹ • X) :=
          stationaryDensity_of_posSemidef_fixedPoint E hE hTP hX_psd hX_fix hX_zero
        -- X = (tr X) • ((tr X)⁻¹ • X), so X is in the span of stationary densities
        have hX_eq : X = (Matrix.trace X) • ((Matrix.trace X)⁻¹ • X) := by
          calc
            X = (1 : ℂ) • X := by simp
            _ = ((Matrix.trace X) * (Matrix.trace X)⁻¹) • X := by
              field_simp [mt (hX_psd.trace_eq_zero_iff.mp ·) hX_zero]
            _ = (Matrix.trace X) • ((Matrix.trace X)⁻¹ • X) := by simp [mul_smul]
        rw [hX_eq]
        have hmem : ((Matrix.trace X)⁻¹ • X) ∈ Submodule.span ℂ S :=
          Submodule.subset_span (show ((Matrix.trace X)⁻¹ • X) ∈ S from hstat)
        exact Submodule.smul_mem _ (Matrix.trace X) hmem
    have h_span_le : Submodule.span ℂ P ≤ Submodule.span ℂ S :=
      Submodule.span_le.mpr h_P_sub_span_S
    rw [h_span_P] at h_span_le
    exact h_span_le

end IsPositiveMap
