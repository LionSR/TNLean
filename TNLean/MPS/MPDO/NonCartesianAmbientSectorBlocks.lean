/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTAlgebraTensorClause
import TNLean.MPS.MPDO.NonCartesianActiveSectorCounterexample
import TNLean.MPS.MPDO.PhysicalIsometricEmbedding

/-!
# The non-Cartesian block in a proper ambient physical sector

This module embeds the four-dimensional non-Cartesian candidate into the first
four coordinates of a five-dimensional physical space. It also embeds the
already-constructed left-canonical normal representative without repeating its
Perron--Frobenius argument.

Every construction here is project-derived auxiliary counterexample
infrastructure, not a result asserted by arXiv:1606.00608. The paper's lines
217--246, 1628--1665, and 1740--1782 provide only the normal-block,
simple-biCF, and per-block reduction context.
-/

open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace MPOTensor.NonCartesianAmbientSectorBlocks

open PhysicalSectorFactorization
open NonCartesianActiveSectorCandidate

/-- The literal inclusion of the four source coordinates into the first four
coordinates of the five-dimensional physical space.

This is project-derived auxiliary counterexample infrastructure, not a result
asserted by arXiv:1606.00608; lines 217--246, 1628--1665, and 1740--1782 are
context only. -/
def physicalInclusion : Matrix (Fin 5) (Fin 4) ℂ :=
  fun i p ↦ if i.val = p.val then 1 else 0

/-- The literal coordinate inclusion is an isometry.

This is project-derived auxiliary counterexample infrastructure, not a result
asserted by arXiv:1606.00608; lines 217--246, 1628--1665, and 1740--1782 are
context only. -/
theorem physicalInclusion_isometry :
    physicalInclusionᴴ * physicalInclusion = 1 := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    norm_num [physicalInclusion, Matrix.mul_apply, Fin.sum_univ_five] <;> omega

/-- The projection onto the first four ambient physical coordinates.

This is a project-derived definition for auxiliary counterexample
infrastructure, not a result asserted by arXiv:1606.00608; lines 217--246,
1628--1665, and 1740--1782 are context only. -/
def badPhysicalSupport : Matrix (Fin 5) (Fin 5) ℂ :=
  physicalInclusion * physicalInclusionᴴ

/-- The original candidate has full one-site physical support. The proof uses
its actual `(0,0)` virtual slice, which is one quarter of the identity, rather
than assuming full support.

This is project-derived auxiliary counterexample infrastructure, not a result
asserted by arXiv:1606.00608; lines 217--246, 1628--1665, and 1740--1782 are
context only. -/
theorem candidate_physicalSupportProj_eq_one :
    physicalSupportProj tensor = 1 := by
  have hSlice : physicalSlice tensor (0 : Fin 2) (0 : Fin 2) =
      (1 / 4 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [physicalSlice, tensor, sectorMatrix, leftPairing, rightPairing,
        Matrix.vecMulVec]
  have hFix := physicalSupportProj_mul_physicalSlice tensor
    (0 : Fin 2) (0 : Fin 2)
  rw [hSlice, Matrix.mul_smul, Matrix.mul_one] at hFix
  ext i j
  have hEntry := congrFun (congrFun hFix i) j
  simp only [Matrix.smul_apply] at hEntry
  linear_combination 4 * hEntry

/-- The non-Cartesian candidate embedded into the first four ambient physical
coordinates.

This is a project-derived definition for auxiliary counterexample
infrastructure, not a result asserted by arXiv:1606.00608; lines 217--246,
1628--1665, and 1740--1782 are context only. -/
def embeddedCandidate : MPOTensor 5 2 :=
  changePhysicalBasis physicalInclusion tensor

/-- The embedded candidate has exactly the first-four-coordinate support.

This is project-derived auxiliary counterexample infrastructure, not a result
asserted by arXiv:1606.00608; lines 217--246, 1628--1665, and 1740--1782 are
context only. -/
theorem embeddedCandidate_physicalSupportProj :
    physicalSupportProj embeddedCandidate = badPhysicalSupport := by
  rw [embeddedCandidate, physicalSupportProj_changePhysicalBasis
    physicalInclusion physicalInclusion_isometry, candidate_physicalSupportProj_eq_one]
  simp [badPhysicalSupport]

/-- One-site injectivity is preserved by the literal physical inclusion.

This is project-derived auxiliary counterexample infrastructure, not a result
asserted by arXiv:1606.00608; lines 217--246, 1628--1665, and 1740--1782 are
context only. -/
theorem embeddedCandidate_isInjective : embeddedCandidate.IsInjective := by
  exact (isInjective_toMPSTensor_changePhysicalBasis_iff
    physicalInclusion physicalInclusion_isometry tensor).2 tensor_isInjective

/-- The embedded candidate remains an MPDO tensor.

This is project-derived auxiliary counterexample infrastructure, not a result
asserted by arXiv:1606.00608; lines 217--246, 1628--1665, and 1740--1782 are
context only. -/
theorem embeddedCandidate_isMPDO : embeddedCandidate.IsMPDO := by
  exact (isMPDO_changePhysicalBasis_iff
    physicalInclusion physicalInclusion_isometry tensor).2 tensor_isSAL.1

/-- The embedded candidate still saturates the area law.

This is project-derived auxiliary counterexample infrastructure, not a result
asserted by arXiv:1606.00608; lines 217--246, 1628--1665, and 1740--1782 are
context only. -/
theorem embeddedCandidate_isSAL : embeddedCandidate.IsSAL := by
  exact (isSAL_changePhysicalBasis_iff
    physicalInclusion physicalInclusion_isometry tensor).2 tensor_isSAL

/-- The embedded candidate obeys literal physical-trace idempotence.

This is project-derived auxiliary counterexample infrastructure, not a result
asserted by arXiv:1606.00608; lines 217--246, 1628--1665, and 1740--1782 are
context only. -/
theorem embeddedCandidate_physTraceTransfer_idempotent :
    physTraceTransfer embeddedCandidate * physTraceTransfer embeddedCandidate =
      physTraceTransfer embeddedCandidate := by
  rw [embeddedCandidate,
    physTraceTransfer_changePhysicalBasis physicalInclusion
      physicalInclusion_isometry tensor]
  exact physTraceTransfer_tensor_idempotent

/-- The embedded candidate has a left-canonical normal representative with a
nonzero coefficient of norm strictly below one. The representative is obtained
by applying the literal physical inclusion to the already-constructed
Perron-gauged representative.

This is project-derived auxiliary counterexample infrastructure, not a result
asserted by arXiv:1606.00608; lines 217--246, 1628--1665, and 1740--1782 are
context only. -/
theorem exists_embedded_leftCanonical_normal_bad_block :
    ∃ (mu : ℂ) (B : MPSTensor (5 * 5) 2),
      mu ≠ 0 ∧ ‖mu‖ < 1 ∧ Kraus.IsInjective B ∧
        MPSTensor.IsLeftCanonical B ∧ MPSTensor.IsNormalTensor B ∧
        MPSTensor.GaugeEquiv embeddedCandidate.toMPSTensor (mu • B) := by
  obtain ⟨mu, B, hmu, hmuNorm, hBInj, hBLeft, hBNormal, hTensorGauge⟩ :=
    exists_leftCanonical_normalTensor_scalar_representation
  let Bmpo : MPOTensor 4 2 := verticalBNTMPO B
  let Bambient : MPSTensor (5 * 5) 2 :=
    (changePhysicalBasis physicalInclusion Bmpo).toMPSTensor
  have hAmbientInj : Kraus.IsInjective Bambient := by
    exact (isInjective_toMPSTensor_changePhysicalBasis_iff
      physicalInclusion physicalInclusion_isometry Bmpo).2 (by simpa [Bmpo] using hBInj)
  have hAmbientLeft : MPSTensor.IsLeftCanonical Bambient := by
    exact isLeftCanonical_toMPSTensor_changePhysicalBasis
      physicalInclusion physicalInclusion_isometry Bmpo (by simpa [Bmpo] using hBLeft)
  have hAmbientNormal : MPSTensor.IsNormalTensor Bambient := by
    exact (isNormalTensor_toMPSTensor_changePhysicalBasis_iff
      physicalInclusion physicalInclusion_isometry Bmpo).2 (by simpa [Bmpo] using hBNormal)
  have hAmbientGauge :
      MPSTensor.GaugeEquiv embeddedCandidate.toMPSTensor (mu • Bambient) := by
    have hSource : MPSTensor.GaugeEquiv tensor.toMPSTensor
        (verticalBNTMPO (mu • B)).toMPSTensor := by
      simpa using hTensorGauge
    have h := gaugeEquiv_toMPSTensor_changePhysicalBasis
      physicalInclusion hSource
    have hVertical : verticalBNTMPO (mu • B) = mu • verticalBNTMPO B := rfl
    rw [hVertical, changePhysicalBasis_smul] at h
    exact h
  exact ⟨mu, Bambient, hmu, hmuNorm, hAmbientInj, hAmbientLeft,
    hAmbientNormal, hAmbientGauge⟩

end MPOTensor.NonCartesianAmbientSectorBlocks
