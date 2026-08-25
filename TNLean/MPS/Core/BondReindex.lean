/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.TraceReindex
import TNLean.MPS.Defs

/-!
# Bond-dimension reindexing of matrix product tensors

This file provides the canonical transport of a matrix product tensor along an
equality of bond dimensions.  The transport is expressed as an equivalence and
implemented by reindexing both matrix coordinates along the induced equivalence
of finite bond-index types.

The accompanying simp lemmas identify this transport with the former raw type
cast, describe its values at physical and bond coordinates, and record the
transport of word evaluation together with the invariance of matrix product
vectors, `SameMPV₂`, and `GaugePhaseEquiv`.
-/

open scoped Matrix

namespace MPSTensor

variable {d D D₁ D₂ D₃ : ℕ}

/-- Reindex the bond coordinates of a matrix product tensor along an equality
of bond dimensions. -/
def reindex (h : D₁ = D₂) : MPSTensor d D₁ ≃ MPSTensor d D₂ :=
  Equiv.piCongrRight fun _ : Fin d => Matrix.reindex (finCongr h) (finCongr h)

/-- The bond reindexing along reflexivity is the identity on tensors. -/
@[simp] theorem reindex_rfl (A : MPSTensor d D) :
    reindex (rfl : D = D) A = A := by
  ext i j k
  rfl

/-- The former type-cast transport agrees with bond-coordinate reindexing. -/
@[simp] theorem cast_eq_reindex (h : D₁ = D₂) (A : MPSTensor d D₁) :
    cast (congrArg (MPSTensor d) h) A = reindex h A := by
  subst h
  simp

/-- Reindexing a tensor at one physical index reindexes both matrix
coordinates. -/
theorem reindex_apply (h : D₁ = D₂) (A : MPSTensor d D₁) (i : Fin d) :
    reindex h A i =
      Matrix.reindex (finCongr h) (finCongr h) (A i) := by
  rfl

/-- At one physical index, bond reindexing agrees with dependent transport of
the corresponding matrix value. -/
theorem reindex_apply_eq_cast (h : D₁ = D₂) (A : MPSTensor d D₁) (i : Fin d) :
    reindex h A i =
      cast (congrArg (fun n => Matrix (Fin n) (Fin n) ℂ) h) (A i) := by
  subst h
  rfl

/-- Reindexing at physical and bond coordinates evaluates the original tensor
at the inversely reindexed bond coordinates. -/
@[simp] theorem reindex_apply_apply (h : D₁ = D₂) (A : MPSTensor d D₁)
    (i : Fin d) (j k : Fin D₂) :
    reindex h A i j k = A i (finCongr h.symm j) (finCongr h.symm k) := by
  rfl

/-- Word evaluation commutes with bond-dimension reindexing. -/
theorem reindex_evalWord (h : D₁ = D₂) (A : MPSTensor d D₁)
    (w : List (Fin d)) :
    Kraus.evalWord (reindex h A) w =
      Matrix.reindex (finCongr h) (finCongr h) (Kraus.evalWord A w) := by
  subst h
  simp

/-- Bond-dimension reindexing does not change matrix product vector
coefficients. -/
theorem reindex_mpv (h : D₁ = D₂) (A : MPSTensor d D₁)
    {N : ℕ} (σ : Fin N → Fin d) :
    mpv (reindex h A) σ = mpv A σ := by
  unfold mpv coeff
  rw [reindex_evalWord, Matrix.trace_reindex]

/-- Reindexing the left tensor preserves equality of matrix product vector
families. -/
@[simp] theorem sameMPV₂_reindex_left (h : D₁ = D₂)
    (A : MPSTensor d D₁) (B : MPSTensor d D₃) :
    SameMPV₂ (reindex h A) B ↔ SameMPV₂ A B := by
  constructor <;> intro hAB N σ
  · simpa only [reindex_mpv] using hAB N σ
  · simpa only [reindex_mpv] using hAB N σ

/-- Reindexing the right tensor preserves equality of matrix product vector
families. -/
@[simp] theorem sameMPV₂_reindex_right (h : D₁ = D₂)
    (A : MPSTensor d D₃) (B : MPSTensor d D₁) :
    SameMPV₂ A (reindex h B) ↔ SameMPV₂ A B := by
  constructor <;> intro hAB N σ
  · simpa only [reindex_mpv] using hAB N σ
  · simpa only [reindex_mpv] using hAB N σ

/-- Simultaneous bond-dimension reindexing preserves gauge-phase equivalence. -/
@[simp] theorem gaugePhaseEquiv_reindex (h : D₁ = D₂)
    (A B : MPSTensor d D₁) :
    GaugePhaseEquiv (reindex h A) (reindex h B) ↔ GaugePhaseEquiv A B := by
  subst h
  simp

end MPSTensor
