/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.BNTCharacterization

/-!
# Existence of a basis of normal tensors

This module constructs a basis of normal tensors from literal CPSV canonical-form data.
It first restricts the displayed canonical-form blocks to those with nonzero weight and
then chooses one representative from each MPV phase-equivalence class.
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ} {A : MPSTensor d D}

/-- Literal CPSV canonical-form data admit a basis of normal tensors obtained by
restricting to nonzero-weight blocks and choosing one representative from each
MPV phase-equivalence class.

**Scope restriction (active blocks):** Literal canonical-form syntax permits
zero-weight listed blocks. The formal theorem covers only blocks with nonzero
weight because zero-weight blocks contribute nothing to any positive-length
matrix product vector. See
`docs/paper-gaps/cpsv16_bnt_characterization_active_blocks.tex`.

The conclusion is the existence part of the construction underlying
arXiv:1606.00608, Proposition `prop:char-BNT`, lines 271--280 and 1137--1146,
with this active-block restriction made explicit. -/
theorem CPSVCanonicalFormData.exists_isCPSVBasisOfNormalTensors
    (data : CPSVCanonicalFormData A) :
    ∃ g : ℕ, ∃ dimB : Fin g → ℕ,
      ∃ basis : (j : Fin g) → MPSTensor d (dimB j),
        (∀ j, 0 < dimB j) ∧
        IsCPSVBasisOfNormalTensors A (fun j ↦ ⟨dimB j, basis j⟩) := by
  classical
  letI : ∀ k, NeZero (data.dim k) :=
    fun k ↦ ⟨Nat.ne_of_gt (data.dim_pos k)⟩
  let Active := {k : Fin data.r // data.weights k ≠ 0}
  let activeEquiv : Fin (Fintype.card Active) ≃ Active :=
    (Fintype.equivFin Active).symm
  let dimActive : Fin (Fintype.card Active) → ℕ :=
    fun k ↦ data.dim (activeEquiv k)
  let blocksActive : (k : Fin (Fintype.card Active)) → MPSTensor d (dimActive k) :=
    fun k ↦ data.blocks (activeEquiv k)
  let classes := mpvPhaseClassData blocksActive
  let dimB : Fin classes.g → ℕ := fun j ↦ dimActive (classes.repr j)
  let basis : (j : Fin classes.g) → MPSTensor d (dimB j) :=
    fun j ↦ blocksActive (classes.repr j)
  have hdimB : ∀ j, 0 < dimB j := by
    intro j
    exact data.dim_pos (activeEquiv (classes.repr j))
  letI : ∀ j, NeZero (dimB j) := fun j ↦ ⟨Nat.ne_of_gt (hdimB j)⟩
  refine ⟨classes.g, dimB, basis, hdimB, ?_⟩
  apply (data.isCPSVBasisOfNormalTensors_iff_covered_and_minimal basis).2
  refine ⟨?_, ?_, ?_⟩
  · intro j
    exact data.blocks_normal (activeEquiv (classes.repr j))
  · intro k hk
    let kActive : Active := ⟨k, hk⟩
    let l : Fin (Fintype.card Active) := activeEquiv.symm kActive
    obtain ⟨j, q, hEnum⟩ := classes.exists_enum_eq l
    have hl : (activeEquiv l : Fin data.r) = k := by
      exact congrArg Subtype.val (activeEquiv.apply_symm_apply kActive)
    have hPhase : MPVBlockPhaseEquiv (basis j) (data.blocks k) := by
      change MPVBlockPhaseEquiv
        (blocksActive (classes.repr j)) (data.blocks k)
      rw [← hl, ← hEnum]
      exact classes.enum_phase j q
    obtain ⟨hdim, hGauge⟩ :=
      hPhase.dim_eq_and_gaugePhaseEquiv_of_isNormalTensor
        (data.blocks_normal (activeEquiv (classes.repr j)))
        (data.blocks_normal k)
    obtain ⟨X, ζ, _hζ, hrel⟩ := hGauge
    refine ⟨j, hdim, X, ζ, ?_, hrel⟩
    exact norm_eq_one_of_gaugePhase_cast_of_isNormalTensor
      (data.blocks_normal (activeEquiv (classes.repr j)))
      (data.blocks_normal k) hdim hrel
  · intro j k hjk hdim hUnit
    obtain ⟨X, ζ, hζnorm, hrel⟩ := hUnit
    apply classes.blocks_not_equiv j k hjk hdim
    exact ⟨X, ζ,
      norm_ne_zero_iff.mp (by rw [hζnorm]; exact one_ne_zero), hrel⟩

end MPSTensor
