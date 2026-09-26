/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SimpleBlocking
import TNLean.MPS.MPU.SourceVCompleteNetwork

/-!
# Canonical form II under positive blocking

A positive physical block preserves the full-support canonical-form-II
presentation of an MPU, including its ambient positive diagonal fixed matrix.
Consequently the source gate of a simple blocked tensor is an isometry for
exactly the weight recorded by the original presentation. The source cuts and
their factors are computed on the blocked tensor.

Source: arXiv:1703.09188, canonical form II, lines 269--281; blocking,
lines 297--305; Theorem `ThmFund1`, lines 577--588.
-/

open scoped Matrix

namespace MPOTensor

variable {d D : ℕ} {U : MPOTensor d D}

/-- Full support of canonical-form-II data is preserved by any positive
physical blocking, after the canonical reindexing of the blocked alphabet.

Source: arXiv:1703.09188, lines 269--281 and 297--305. -/
theorem hasFullSupport_blockTensorCFIIData
    (data : MPSTensor.CPSVCanonicalFormIIData U.normalizedFlattening)
    (hfull : data.toCPSVCanonicalFormData.HasFullSupport)
    (p : ℕ) (hp : 0 < p) :
    (blockTensorCFIIData U data p hp).toCPSVCanonicalFormData.HasFullSupport := by
  unfold blockTensorCFIIData
  convert ((data.blockTensor p hp).reindexPhysical
      (blockedDoubledIndexEquiv d p)).hasFullSupport_cast
    (MPSTensor.CPSVCanonicalFormData.hasFullSupport_reindexPhysical _
      (data.toCPSVCanonicalFormData.hasFullSupport_blockTensor hfull p hp)
      (blockedDoubledIndexEquiv d p)) (normalizedFlattening_blockTensor U p) using 1
  congr 1
  exact eq_of_heq ((cast_heq _ _).trans (eqRec_heq _ _).symm)

/-- A positive block of an MPU in canonical form II retains canonical form II
in the same ambient bond coordinates and with the same recorded fixed matrix.

Source: arXiv:1703.09188, lines 269--281 and 297--305; line 356. -/
noncomputable def IsMPUCanonicalFormII.blockTensor
    (hU : IsMPUCanonicalFormII U) (p : ℕ) (hp : 0 < p) :
    IsMPUCanonicalFormII (MPOTensor.blockTensor U p) where
  isMPU := hU.isMPU.blockTensor p hp
  cfii := blockTensorCFIIData U hU.cfii p hp
  fullSupport_eq := hasFullSupport_blockTensorCFIIData hU.cfii hU.hasFullSupport p hp
  ρ := hU.ρ
  ρ_posDef := hU.ρ_posDef
  ρ_isDiag := hU.ρ_isDiag
  ρ_trace := hU.ρ_trace
  ρ_fixed := by
    rw [normalizedFlattening_blockTensor, MPSTensor.transferMap_reindexPhysical_equiv]
    exact MPSTensor.transferMap_blockTensor_fixedPoint U.normalizedFlattening p hU.ρ hU.ρ_fixed

/-- If a positive block is simple, its source gate is an isometry for the
original canonical-form-II weight. All source-cut factors here belong to the
blocked tensor, not the unblocked tensor.

Source: arXiv:1703.09188, Theorem `ThmFund1`, lines 577--588. -/
theorem IsMPUCanonicalFormII.sourceV_blockTensor_isIsometry
    (hU : IsMPUCanonicalFormII U) (p : ℕ) (hp : 0 < p)
    (hS : IsMPUSimple (MPOTensor.blockTensor U p)) :
    (sourceV (MPOTensor.blockTensor U p) hU.ρ hU.ρ_posDef).IsIsometry := by
  exact (hU.blockTensor p hp).sourceV_isIsometry hS

/-- An MPU in canonical form II has a simple positive block of length at
most `D⁴` whose source gate is isometric for the same ambient fixed matrix.
This includes bond dimension one.

Source: arXiv:1703.09188, Proposition III.3(ii), lines 378--427, and
Theorem `ThmFund1`, lines 577--588. -/
theorem IsMPUCanonicalFormII.exists_sourceV_blockTensor_isIsometry
    (hU : IsMPUCanonicalFormII U) :
    ∃ p : ℕ, 0 < p ∧ p ≤ D ^ 4 ∧
      IsMPUSimple (MPOTensor.blockTensor U p) ∧
      (sourceV (MPOTensor.blockTensor U p) hU.ρ hU.ρ_posDef).IsIsometry := by
  let _ : NeZero d := hU.neZero_phys
  let _ : NeZero D := hU.neZero_bond
  obtain ⟨p, hp, hpD, hS⟩ := hU.isMPU.exists_blockTensor_isMPUSimple
  exact ⟨p, hp, hpD, hS, hU.sourceV_blockTensor_isIsometry p hp hS⟩

end MPOTensor
