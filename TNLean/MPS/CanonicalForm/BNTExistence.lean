/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.BNTCharacterization

/-!
# Existence of a basis of normal tensors

This module constructs a basis of normal tensors from literal CPSV canonical-form data by
choosing one representative from each MPV phase-equivalence class of the displayed blocks.
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ} {A : MPSTensor d D}

/-- Literal CPSV canonical-form data admit a basis of normal tensors obtained by
choosing one representative from each MPV phase-equivalence class.

The conclusion is the existence part of the construction underlying
arXiv:1606.00608, Proposition `prop:char-BNT`, lines 271--280 and 1137--1146. -/
theorem CPSVCanonicalFormData.exists_isCPSVBasisOfNormalTensors
    (data : CPSVCanonicalFormData A) :
    ∃ g : ℕ, ∃ dimB : Fin g → ℕ,
      ∃ basis : (j : Fin g) → MPSTensor d (dimB j),
        (∀ j, 0 < dimB j) ∧
        IsCPSVBasisOfNormalTensors A (fun j ↦ ⟨dimB j, basis j⟩) := by
  classical
  let : ∀ k, NeZero (data.dim k) :=
    fun k ↦ ⟨Nat.ne_of_gt (data.dim_pos k)⟩
  let classes := mpvPhaseClassData data.blocks
  let dimB : Fin classes.g → ℕ := fun j ↦ data.dim (classes.repr j)
  let basis : (j : Fin classes.g) → MPSTensor d (dimB j) :=
    fun j ↦ data.blocks (classes.repr j)
  have hdimB : ∀ j, 0 < dimB j := by
    intro j
    exact data.dim_pos (classes.repr j)
  let : ∀ j, NeZero (dimB j) := fun j ↦ ⟨Nat.ne_of_gt (hdimB j)⟩
  refine ⟨classes.g, dimB, basis, hdimB, ?_⟩
  apply (data.isCPSVBasisOfNormalTensors_iff_covered_and_minimal basis).2
  refine ⟨?_, ?_, ?_⟩
  · intro j
    exact data.blocks_normal (classes.repr j)
  · intro k
    obtain ⟨j, q, hEnum⟩ := classes.exists_enum_eq k
    have hPhase : MPVBlockPhaseEquiv (basis j) (data.blocks k) := by
      change MPVBlockPhaseEquiv (data.blocks (classes.repr j)) (data.blocks k)
      rw [← hEnum]
      exact classes.enum_phase j q
    obtain ⟨hdim, hGauge⟩ :=
      hPhase.dim_eq_and_gaugePhaseEquiv_of_isNormalTensor
        (data.blocks_normal (classes.repr j)) (data.blocks_normal k)
    obtain ⟨X, ζ, _hζ, hrel⟩ := hGauge
    refine ⟨j, hdim, X, ζ, ?_, hrel⟩
    exact norm_eq_one_of_gaugePhase_cast_of_isNormalTensor
      (data.blocks_normal (classes.repr j)) (data.blocks_normal k) hdim hrel
  · intro j k hjk hdim hUnit
    obtain ⟨X, ζ, hζnorm, hrel⟩ := hUnit
    apply classes.blocks_not_equiv j k hjk hdim
    exact ⟨X, ζ,
      Complex.ne_zero_of_norm_eq_one hζnorm, hrel⟩

end MPSTensor
