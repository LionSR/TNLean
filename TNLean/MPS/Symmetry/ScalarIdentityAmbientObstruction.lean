/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.ExactMPSGappedPhase
import QICLean.Channel.Schwarz.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Repeated bond copies of a product tensor

The product tensor with letters `I` and `0` represents the same positive-length
matrix product vector rays at bond dimensions one and two. The bond-two tensor
is unital, but its adjoint transfer map is the identity and hence has a
four-dimensional fixed space. Thus the physical rays do not determine the
fixed-space dimension of an arbitrary ambient realization.

This file proves only these algebraic assertions. For the corresponding product
state, the nearest-neighbor projector onto the complement of `|00⟩` has a unique
periodic ground vector and a uniform positive gap; no Hamiltonian assertion is
formalized here. Source context: arXiv:1010.3732, Section II.F.2, the paragraph
following `eq:inj-sym:gs-smooth`.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open scoped Matrix

namespace MPSTensor

/-- A product tensor with any number of repeated bond copies. -/
def repeatedProductTensor (D : ℕ) : MPSTensor 2 D :=
  fun i => if i = 0 then 1 else 0

/-- The adjoint transfer map fixes every ambient matrix. -/
theorem repeatedProductTensor_adjointMapLM (D : ℕ) :
    Kraus.adjointMapLM (repeatedProductTensor D) = LinearMap.id := by
  ext X i j
  simp [Kraus.adjointMapLM_apply, Kraus.adjointMap_apply, repeatedProductTensor]

/-- Repeated bond copies preserve unitality. -/
theorem repeatedProductTensor_isUnital (D : ℕ) :
    Kraus.IsUnital (repeatedProductTensor D) := by
  simp [Kraus.IsUnital, repeatedProductTensor]

/-- At bond dimension two the adjoint fixed space has complex dimension four. -/
theorem repeatedProductTensor_fixedSpace_finrank :
    Module.finrank ℂ
      (LinearMap.ker (LinearMap.id - Kraus.adjointMapLM (repeatedProductTensor 2))) = 4 := by
  rw [repeatedProductTensor_adjointMapLM, sub_self, LinearMap.ker_zero]
  simp [Module.finrank_matrix]

private theorem repeatedProductTensor_evalWord (D : ℕ) (w : List (Fin 2)) :
    Kraus.evalWord (repeatedProductTensor D) w =
      if ∀ i ∈ w, i = 0 then 1 else 0 := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [Kraus.evalWord_cons, ih]
    by_cases hi : i = 0 <;> simp [repeatedProductTensor, hi]

/-- Repeating the bond copy twice multiplies every periodic vector coefficient by two. -/
theorem repeatedProductTensor_mpv {N : ℕ} (w : Fin N → Fin 2) :
    mpv (repeatedProductTensor 2) w = 2 * mpv (repeatedProductTensor 1) w := by
  simp only [mpv, coeff, repeatedProductTensor_evalWord]
  split <;> simp

/-- The bond-one and bond-two tensors determine the same positive-length physical rays. -/
theorem repeatedProductTensor_samePositiveMpvRay :
    SamePositiveMpvRay (repeatedProductTensor 2) (repeatedProductTensor 1) := by
  intro N _
  have h : (mpv (repeatedProductTensor 2) : (Fin N → Fin 2) → ℂ) =
      (2 : ℂ) • mpv (repeatedProductTensor 1) := by
    funext w
    exact repeatedProductTensor_mpv w
  rw [h]
  exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (by norm_num)) _

end MPSTensor
