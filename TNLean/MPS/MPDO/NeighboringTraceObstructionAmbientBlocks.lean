/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.BNT.Basic
import TNLean.MPS.FundamentalTheorem.SectorBNT.Examples
import TNLean.MPS.MPDO.BNTAlgebraTensorClause
import TNLean.MPS.MPDO.NonCartesianActiveSectorCounterexample
import TNLean.MPS.MPDO.PhysicalIsometricEmbedding
import TNLean.MPS.MPDO.PureRFPSAL

/-!
# Ambient blocks for the rank-one neighboring-trace obstruction

This module embeds the four-dimensional tensor from
`NonCartesianActiveSectorCounterexample` into the first four coordinates of a
five-dimensional physical space. The inherited "non-Cartesian" name refers
only to an auxiliary failure of a product relabelling. The mathematical
obstruction is that no physical-sector factorization has neighboring traces
of the CPSV16 form
\(\operatorname{tr}(\eta_{k,h}) = a_k b_h\) with
\(\sum_k a_k b_k = 1\).

The module also embeds the already-constructed left-canonical normal
representative without repeating its Perron--Frobenius argument.

Every definition and result here is project-derived auxiliary counterexample
infrastructure, not an assertion of arXiv:1606.00608. The factorization above
is Theorem 4.9(iv), equations `tralktrrk` and `PsiPhi`, lines 864--888; its
Appendix-C form is given at lines 1383--1401, derived in Lemma `SALZCL` at
lines 1484--1499, and used in Proposition `prop2to3` at lines 1740--1782.
Lines 217--246 and 1628--1665 provide only the normal-block, coefficient, and
simple-biCF context.
-/

open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace MPOTensor.NeighboringTraceObstructionAmbientBlocks

open PhysicalSectorFactorization
open NonCartesianActiveSectorCandidate

/-- The literal inclusion of the four source coordinates into the first four
coordinates of the five-dimensional physical space. -/
def physicalInclusion : Matrix (Fin 5) (Fin 4) ℂ :=
  fun i p ↦ if i.val = p.val then 1 else 0

/-- The literal coordinate inclusion is an isometry. -/
theorem physicalInclusion_isometry :
    physicalInclusionᴴ * physicalInclusion = 1 := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    norm_num [physicalInclusion, Matrix.mul_apply, Fin.sum_univ_five] <;> omega

/-- The projection onto the first four ambient physical coordinates. -/
def obstructionPhysicalSupport : Matrix (Fin 5) (Fin 5) ℂ :=
  physicalInclusion * physicalInclusionᴴ

/-- The obstruction tensor has full one-site physical support. The proof uses
its actual `(0,0)` virtual slice, which is one quarter of the identity, rather
than assuming full support. -/
theorem tensor_physicalSupportProj_eq_one :
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

/-- The four-letter obstruction tensor embedded into the first four ambient
physical coordinates. -/
def embeddedObstruction : MPOTensor 5 2 :=
  changePhysicalBasis physicalInclusion tensor

/-- The embedded obstruction has exactly the first-four-coordinate support. -/
theorem embeddedObstruction_physicalSupportProj :
    physicalSupportProj embeddedObstruction = obstructionPhysicalSupport := by
  rw [embeddedObstruction, physicalSupportProj_changePhysicalBasis
    physicalInclusion physicalInclusion_isometry, tensor_physicalSupportProj_eq_one]
  simp [obstructionPhysicalSupport]

/-- One-site injectivity is preserved by the literal physical inclusion. -/
theorem embeddedObstruction_isInjective : embeddedObstruction.IsInjective := by
  exact (isInjective_toMPSTensor_changePhysicalBasis_iff
    physicalInclusion physicalInclusion_isometry tensor).2 tensor_isInjective

/-- The embedded obstruction remains an MPDO tensor. -/
theorem embeddedObstruction_isMPDO : embeddedObstruction.IsMPDO := by
  exact (isMPDO_changePhysicalBasis_iff
    physicalInclusion physicalInclusion_isometry tensor).2 tensor_isSAL.1

/-- The embedded obstruction still saturates the area law. -/
theorem embeddedObstruction_isSAL : embeddedObstruction.IsSAL := by
  exact (isSAL_changePhysicalBasis_iff
    physicalInclusion physicalInclusion_isometry tensor).2 tensor_isSAL

/-- The embedded obstruction obeys literal physical-trace idempotence. -/
theorem embeddedObstruction_physTraceTransfer_idempotent :
    physTraceTransfer embeddedObstruction * physTraceTransfer embeddedObstruction =
      physTraceTransfer embeddedObstruction := by
  rw [embeddedObstruction,
    physTraceTransfer_changePhysicalBasis physicalInclusion
      physicalInclusion_isometry tensor]
  exact physTraceTransfer_tensor_idempotent

private theorem physicalSlice_eq_sum_of_conjugation {d D : ℕ}
    {K L : MPOTensor d D} (X : GL (Fin D) ℂ)
    (hX : ∀ i, L.toMPSTensor i = X * K.toMPSTensor i * X⁻¹) (β α : Fin D) :
    physicalSlice L β α = ∑ ν : Fin D, ∑ μ : Fin D,
      (X β μ * (X⁻¹ : Matrix (Fin D) (Fin D) ℂ) ν α) • physicalSlice K μ ν := by
  ext i j
  have hEntry := congrArg
    (fun A : Matrix (Fin D) (Fin D) ℂ ↦ A β α)
    (hX (finProdFinEquiv (i, j)))
  simpa [toMPSTensor, physicalSlice, Matrix.mul_apply, Matrix.sum_apply,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul,
    mul_assoc, mul_left_comm, mul_comm] using hEntry

private theorem physicalSupportProj_isHermitian {d D : ℕ} (K : MPOTensor d D) :
    (physicalSupportProj K).IsHermitian :=
  (Matrix.posSemidef_self_mul_conjTranspose (physicalSliceColumns K)).supportProj_isHermitian

private theorem physicalSupportProj_eq_of_gaugeEquiv {d D : ℕ}
    {K L : MPOTensor d D} (hGauge : MPSTensor.GaugeEquiv K.toMPSTensor L.toMPSTensor) :
    physicalSupportProj K = physicalSupportProj L := by
  have hGaugeSymm := hGauge.symm
  obtain ⟨X, hX⟩ := hGauge
  have hKL : physicalSupportProj K * physicalSupportProj L = physicalSupportProj L :=
    mul_physicalSupportProj_eq_self_of_forall_mul_physicalSlice_eq L
      (physicalSupportProj K) (fun β α ↦ by
        rw [physicalSlice_eq_sum_of_conjugation X hX]
        simp_rw [Matrix.mul_sum, Matrix.mul_smul, physicalSupportProj_mul_physicalSlice])
  obtain ⟨Y, hY⟩ := hGaugeSymm
  have hLK : physicalSupportProj L * physicalSupportProj K = physicalSupportProj K :=
    mul_physicalSupportProj_eq_self_of_forall_mul_physicalSlice_eq K
      (physicalSupportProj L) (fun β α ↦ by
        rw [physicalSlice_eq_sum_of_conjugation Y hY]
        simp_rw [Matrix.mul_sum, Matrix.mul_smul, physicalSupportProj_mul_physicalSlice])
  have hLK' : physicalSupportProj K * physicalSupportProj L = physicalSupportProj K := by
    simpa only [Matrix.conjTranspose_mul, (physicalSupportProj_isHermitian K).eq,
      (physicalSupportProj_isHermitian L).eq] using congrArg Matrix.conjTranspose hLK
  exact hLK'.symm.trans hKL

private theorem physicalSupportProj_smul_of_ne {d D : ℕ} (K : MPOTensor d D)
    {c : ℂ} (hc : c ≠ 0) :
    physicalSupportProj (c • K) = physicalSupportProj K := by
  have hScaled : ∀ β α,
      physicalSupportProj K * physicalSlice (c • K) β α = physicalSlice (c • K) β α := by
    intro β α
    rw [show physicalSlice (c • K) β α = c • physicalSlice K β α by rfl,
      Matrix.mul_smul, physicalSupportProj_mul_physicalSlice]
  have hUnscaled : ∀ β α,
      physicalSupportProj (c • K) * physicalSlice K β α = physicalSlice K β α := by
    intro β α
    apply MulAction.injective₀ hc
    change c • (physicalSupportProj (c • K) * physicalSlice K β α) =
      c • physicalSlice K β α
    rw [← Matrix.mul_smul]
    exact physicalSupportProj_mul_physicalSlice (c • K) β α
  have hScaledSupport :
      physicalSupportProj K * physicalSupportProj (c • K) = physicalSupportProj (c • K) :=
    mul_physicalSupportProj_eq_self_of_forall_mul_physicalSlice_eq
      (c • K) (physicalSupportProj K) hScaled
  have hUnscaledSupport :
      physicalSupportProj (c • K) * physicalSupportProj K = physicalSupportProj K :=
    mul_physicalSupportProj_eq_self_of_forall_mul_physicalSlice_eq
      K (physicalSupportProj (c • K)) hUnscaled
  have hUnscaledSupport' :
      physicalSupportProj K * physicalSupportProj (c • K) = physicalSupportProj K := by
    simpa only [Matrix.conjTranspose_mul, (physicalSupportProj_isHermitian K).eq,
      (physicalSupportProj_isHermitian (c • K)).eq] using
      congrArg Matrix.conjTranspose hUnscaledSupport
  exact hScaledSupport.symm.trans hUnscaledSupport'

/-- The embedded obstruction has a left-canonical normal representative with a
nonzero coefficient of norm strictly below one. The representative is obtained
by applying the literal physical inclusion to the already-constructed
Perron-gauged representative. -/
theorem exists_embedded_leftCanonical_normal_obstruction_block :
    ∃ (mu : ℂ) (B : MPSTensor (5 * 5) 2),
      mu ≠ 0 ∧ ‖mu‖ < 1 ∧ Kraus.IsInjective B ∧
        MPSTensor.IsLeftCanonical B ∧ MPSTensor.IsNormalTensor B ∧
        MPSTensor.GaugeEquiv embeddedObstruction.toMPSTensor (mu • B) ∧
        physicalSupportProj (verticalBNTMPO B) = obstructionPhysicalSupport := by
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
      MPSTensor.GaugeEquiv embeddedObstruction.toMPSTensor (mu • Bambient) := by
    have hSource : MPSTensor.GaugeEquiv tensor.toMPSTensor
        (verticalBNTMPO (mu • B)).toMPSTensor := by
      simpa using hTensorGauge
    have h := gaugeEquiv_toMPSTensor_changePhysicalBasis
      physicalInclusion hSource
    have hVertical : verticalBNTMPO (mu • B) = mu • verticalBNTMPO B := rfl
    rw [hVertical, changePhysicalBasis_smul] at h
    exact h
  have hAmbientGaugeMPO : MPSTensor.GaugeEquiv embeddedObstruction.toMPSTensor
      (mu • verticalBNTMPO Bambient).toMPSTensor := by
    rw [← show verticalBNTMPO (mu • Bambient) =
      mu • verticalBNTMPO Bambient from rfl, verticalBNTMPO_toMPSTensor]
    exact hAmbientGauge
  have hAmbientSupport :
      physicalSupportProj (verticalBNTMPO Bambient) = obstructionPhysicalSupport := by
    calc
      physicalSupportProj (verticalBNTMPO Bambient) =
          physicalSupportProj (mu • verticalBNTMPO Bambient) :=
        (physicalSupportProj_smul_of_ne (verticalBNTMPO Bambient) hmu).symm
      _ = physicalSupportProj embeddedObstruction :=
        (physicalSupportProj_eq_of_gaugeEquiv hAmbientGaugeMPO).symm
      _ = obstructionPhysicalSupport := embeddedObstruction_physicalSupportProj
  exact ⟨mu, Bambient, hmu, hmuNorm, hAmbientInj, hAmbientLeft,
    hAmbientNormal, hAmbientGauge, hAmbientSupport⟩

/-! ## The terminal physical block -/

/-- The one-dimensional physical coordinate included as ambient coordinate four. -/
def terminalPhysicalInclusion : Matrix (Fin 5) (Fin 1) ℂ :=
  fun i _ ↦ if i = 4 then 1 else 0

/-- The terminal coordinate inclusion is an isometry. -/
theorem terminalPhysicalInclusion_isometry :
    terminalPhysicalInclusionᴴ * terminalPhysicalInclusion = 1 := by
  ext p q
  fin_cases p
  fin_cases q
  norm_num [terminalPhysicalInclusion, Matrix.mul_apply, Fin.sum_univ_five]

/-- The scalar product-state MPO before inclusion into the ambient coordinate. -/
private noncomputable def terminalSource : MPOTensor 1 1 :=
  doubledTensor MPSTensor.scalarUnitTensor

@[simp] private theorem terminalSource_apply (i j : Fin 1) :
    terminalSource i j = 1 := by
  fin_cases i
  fin_cases j
  ext a b
  fin_cases a
  fin_cases b
  simp [terminalSource, doubledTensor, MPSTensor.scalarUnitTensor]

private lemma scalarUnitTensor_evalWord {N : ℕ} (σ : Fin N → Fin 1) :
    Kraus.evalWord MPSTensor.scalarUnitTensor (List.ofFn σ) = 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [List.ofFn_succ, Kraus.evalWord_cons, ih]
      simp [MPSTensor.scalarUnitTensor]

private theorem scalarUnitTensor_transferMap_eq_id :
    Kraus.transferMap MPSTensor.scalarUnitTensor = LinearMap.id := by
  apply LinearMap.ext
  intro X
  ext a b
  fin_cases a
  fin_cases b
  simp [MPSTensor.scalarUnitTensor]

private theorem terminalSource_transferMap_eq_id :
    Kraus.transferMap terminalSource.toMPSTensor = LinearMap.id := by
  apply LinearMap.ext
  intro X
  ext a b
  fin_cases a
  fin_cases b
  simp [toMPSTensor, terminalSource_apply]

/-- The terminal bond-one block, supported exactly on ambient coordinate four. -/
def terminalBlock : MPOTensor 5 1 :=
  changePhysicalBasis terminalPhysicalInclusion terminalSource

/-- The projection onto ambient physical coordinate four. -/
def terminalPhysicalSupport : Matrix (Fin 5) (Fin 5) ℂ :=
  terminalPhysicalInclusion * terminalPhysicalInclusionᴴ

/-- The scalar source is one-site injective. -/
private theorem terminalSource_isInjective : Kraus.IsInjective terminalSource.toMPSTensor := by
  apply top_unique
  intro X _hX
  have hGenerator : terminalSource.toMPSTensor 0 ∈
      Submodule.span ℂ (Set.range terminalSource.toMPSTensor) :=
    Submodule.subset_span (Set.mem_range_self 0)
  have hScalar := (Submodule.span ℂ (Set.range terminalSource.toMPSTensor)).smul_mem
    (X 0 0) hGenerator
  convert hScalar using 1
  ext a b
  fin_cases a
  fin_cases b
  simp [toMPSTensor, terminalSource_apply]

/-- The terminal block is one-site injective. -/
theorem terminalBlock_isInjective : Kraus.IsInjective terminalBlock.toMPSTensor := by
  exact (isInjective_toMPSTensor_changePhysicalBasis_iff
    terminalPhysicalInclusion terminalPhysicalInclusion_isometry terminalSource).2
      terminalSource_isInjective

/-- The terminal block is left-canonical. -/
theorem terminalBlock_isLeftCanonical :
    MPSTensor.IsLeftCanonical terminalBlock.toMPSTensor := by
  apply isLeftCanonical_toMPSTensor_changePhysicalBasis
    terminalPhysicalInclusion terminalPhysicalInclusion_isometry terminalSource
  simp [MPSTensor.IsLeftCanonical, Kraus.IsTP, toMPSTensor, terminalSource_apply]

/-- The terminal block is a normal tensor. -/
theorem terminalBlock_isNormalTensor :
    MPSTensor.IsNormalTensor terminalBlock.toMPSTensor := by
  exact (isNormalTensor_toMPSTensor_changePhysicalBasis_iff
    terminalPhysicalInclusion terminalPhysicalInclusion_isometry terminalSource).2
      (MPSTensor.isNormalTensor_of_bondDim_one_of_transferMap_eq_id
        terminalSource.toMPSTensor terminalSource_transferMap_eq_id)

private theorem terminalSource_isMPDO : terminalSource.IsMPDO := by
  intro N _hN
  exact doubledTensor_posSemidef MPSTensor.scalarUnitTensor N

private theorem terminalSource_physTraceTransfer_eq_one :
    physTraceTransfer terminalSource = 1 := by
  ext a b
  fin_cases a
  fin_cases b
  simp [physTraceTransfer, terminalSource_apply]

private theorem scalarUnitTensor_pureState_trace_ne_zero (N : ℕ) :
    Matrix.trace (MPSTensor.pureState MPSTensor.scalarUnitTensor N) ≠ 0 := by
  have hMpv : ∀ σ : Fin N → Fin 1,
      MPSTensor.mpv MPSTensor.scalarUnitTensor σ = 1 := by
    intro σ
    simp [MPSTensor.mpv, scalarUnitTensor_evalWord, Matrix.trace]
  have hPure : MPSTensor.pureState MPSTensor.scalarUnitTensor N = 1 := by
    ext σ τ
    obtain rfl : τ = σ := Subsingleton.elim τ σ
    simp only [MPSTensor.pureState, Matrix.vecMulVec_apply, Pi.star_apply,
      Matrix.one_apply_eq]
    rw [hMpv]
    simp
  rw [hPure]
  simp

private theorem terminalSource_isSAL : terminalSource.IsSAL := by
  have hPureRFP : MPSTensor.IsTransferIdempotent MPSTensor.scalarUnitTensor := by
    rw [MPSTensor.IsTransferIdempotent, scalarUnitTensor_transferMap_eq_id,
      LinearMap.comp_id]
  have hPureSAL := MPSTensor.isSAL_of_isTransferIdempotent
    MPSTensor.scalarUnitTensor hPureRFP
  refine ⟨terminalSource_isMPDO, ?_, ?_⟩
  · intro N _hN
    rw [terminalSource, mpo_doubledTensor]
    exact scalarUnitTensor_pureState_trace_ne_zero N
  · intro N L hL hLN
    change (doubledTensor MPSTensor.scalarUnitTensor).mutualInfoChain N L _ _ =
      (doubledTensor MPSTensor.scalarUnitTensor).mutualInfoChain N (L + 1) _ _
    rw [mutualInfoChain_doubledTensor MPSTensor.scalarUnitTensor N L _
        (scalarUnitTensor_pureState_trace_ne_zero N),
      mutualInfoChain_doubledTensor MPSTensor.scalarUnitTensor N (L + 1) _
        (scalarUnitTensor_pureState_trace_ne_zero N)]
    congr 1
    exact hPureSAL N L hL hLN

/-- The terminal block is an MPDO tensor. -/
theorem terminalBlock_isMPDO : terminalBlock.IsMPDO := by
  exact (isMPDO_changePhysicalBasis_iff
    terminalPhysicalInclusion terminalPhysicalInclusion_isometry terminalSource).2
      terminalSource_isMPDO

/-- The terminal block saturates the area law. -/
theorem terminalBlock_isSAL : terminalBlock.IsSAL := by
  exact (isSAL_changePhysicalBasis_iff
    terminalPhysicalInclusion terminalPhysicalInclusion_isometry terminalSource).2
      terminalSource_isSAL

/-- The physical-trace transfer of the terminal block is exactly one. -/
theorem terminalBlock_physTraceTransfer_eq_one :
    physTraceTransfer terminalBlock = 1 := by
  rw [terminalBlock, physTraceTransfer_changePhysicalBasis
    terminalPhysicalInclusion terminalPhysicalInclusion_isometry terminalSource]
  exact terminalSource_physTraceTransfer_eq_one

/-- The terminal block has literal physical-trace idempotence. -/
theorem terminalBlock_physTraceTransfer_idempotent :
    physTraceTransfer terminalBlock * physTraceTransfer terminalBlock =
      physTraceTransfer terminalBlock := by
  rw [terminalBlock_physTraceTransfer_eq_one, one_mul]

private theorem terminalSource_physicalSupportProj :
    physicalSupportProj terminalSource = 1 := by
  have hSlice : physicalSlice terminalSource 0 0 = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simp [physicalSlice, terminalSource_apply]
  have hFix := physicalSupportProj_mul_physicalSlice terminalSource 0 0
  rw [hSlice, Matrix.mul_one] at hFix
  exact hFix

/-- The terminal block has exactly the coordinate-four physical support. -/
theorem terminalBlock_physicalSupportProj :
    physicalSupportProj terminalBlock = terminalPhysicalSupport := by
  rw [terminalBlock, physicalSupportProj_changePhysicalBasis
    terminalPhysicalInclusion terminalPhysicalInclusion_isometry,
    terminalSource_physicalSupportProj]
  simp [terminalPhysicalSupport]

/-- The obstruction and terminal physical supports are orthogonal, in this order. -/
theorem obstructionPhysicalSupport_mul_terminalPhysicalSupport :
    obstructionPhysicalSupport * terminalPhysicalSupport = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [obstructionPhysicalSupport, terminalPhysicalSupport, physicalInclusion,
      terminalPhysicalInclusion, Matrix.mul_apply, Fin.sum_univ_one,
      Fin.sum_univ_four, Fin.sum_univ_five] <;> simp

/-- The terminal and obstruction physical supports are orthogonal, in the reverse order. -/
theorem terminalPhysicalSupport_mul_obstructionPhysicalSupport :
    terminalPhysicalSupport * obstructionPhysicalSupport = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [obstructionPhysicalSupport, terminalPhysicalSupport, physicalInclusion,
      terminalPhysicalInclusion, Matrix.mul_apply, Fin.sum_univ_one,
      Fin.sum_univ_four, Fin.sum_univ_five] <;> simp

/-- The obstruction and terminal physical supports resolve the ambient identity. -/
theorem obstructionPhysicalSupport_add_terminalPhysicalSupport :
    obstructionPhysicalSupport + terminalPhysicalSupport = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [obstructionPhysicalSupport, terminalPhysicalSupport, physicalInclusion,
      terminalPhysicalInclusion, Matrix.mul_apply, Fin.sum_univ_one,
      Fin.sum_univ_four, Fin.sum_univ_five] <;> simp

/-! ## The two-block BNT canonical form -/

/-- The two-sector, one-copy-per-sector decomposition has obstruction-block
coefficient `mu` and terminal-block coefficient exactly one. -/
@[reducible] noncomputable def obstructionTerminalDecomposition
    (mu : ℂ) (B : MPSTensor (5 * 5) 2) (hmu : mu ≠ 0) :
    MPSTensor.SectorDecomposition (5 * 5) where
  basisCount := 2
  basisDim := Fin.cons (α := fun _ : Fin 2 ↦ ℕ) 2 (fun _ : Fin 1 ↦ 1)
  basis := Fin.cons
    (α := fun j : Fin 2 ↦ MPSTensor (5 * 5)
      (Fin.cons (α := fun _ : Fin 2 ↦ ℕ) 2 (fun _ : Fin 1 ↦ 1) j))
    B (fun _ : Fin 1 ↦ terminalBlock.toMPSTensor)
  sectors :=
    { copies := fun _ ↦ 1
      copies_pos := fun _ ↦ Nat.one_pos
      weight := fun j _ ↦
        Fin.cons (α := fun _ : Fin 2 ↦ ℂ) mu (fun _ : Fin 1 ↦ 1) j
      weight_ne_zero := by
        intro j q
        fin_cases j
        · exact hmu
        · exact one_ne_zero }

/-- The two basis bond dimensions are exactly two and one. -/
theorem obstructionTerminalDecomposition_basisDim
    (mu : ℂ) (B : MPSTensor (5 * 5) 2) (hmu : mu ≠ 0) :
    (obstructionTerminalDecomposition mu B hmu).basisDim 0 = 2 ∧
      (obstructionTerminalDecomposition mu B hmu).basisDim (Fin.succ 0) = 1 := by
  constructor
  · rfl
  · rfl

/-- The basis blocks are literally the unabsorbed obstruction normal block and the
terminal bond-one block. -/
theorem obstructionTerminalDecomposition_basis
    (mu : ℂ) (B : MPSTensor (5 * 5) 2) (hmu : mu ≠ 0) :
    (obstructionTerminalDecomposition mu B hmu).basis 0 = B ∧
      (obstructionTerminalDecomposition mu B hmu).basis (Fin.succ 0) =
        terminalBlock.toMPSTensor := by
  constructor
  · rfl
  · rfl

/-- The literal two-block decomposition is in BNT canonical form. The
basis-family separation is forced by the impossible bond-dimension equality
`2 = 1`; the terminal coefficient supplies the single global unit witness. -/
theorem obstructionTerminalDecomposition_isBNTCanonicalForm
    (mu : ℂ) (B : MPSTensor (5 * 5) 2) (hmu : mu ≠ 0) (hmuNorm : ‖mu‖ < 1)
    (hBInj : Kraus.IsInjective B) (hBLeft : MPSTensor.IsLeftCanonical B)
    (hBNormal : MPSTensor.IsNormalTensor B) :
    MPSTensor.IsBNTCanonicalForm (obstructionTerminalDecomposition mu B hmu) := by
  have hTerminalNormal := terminalBlock_isNormalTensor
  have hBSelf : Filter.Tendsto
      (fun N : ℕ ↦ MPSTensor.mpvOverlap (d := 5 * 5) B B N)
      Filter.atTop (nhds (1 : ℂ)) :=
    MPSTensor.overlap_tendsto_one_of_peripheralPrimitive_of_irreducible B
      hBNormal.no_invariant_proj hBLeft hBNormal.primitive_transfer
  have hTerminalSelf : Filter.Tendsto
      (fun N : ℕ ↦ MPSTensor.mpvOverlap (d := 5 * 5)
        terminalBlock.toMPSTensor terminalBlock.toMPSTensor N)
      Filter.atTop (nhds (1 : ℂ)) :=
    MPSTensor.overlap_tendsto_one_of_peripheralPrimitive_of_irreducible
      terminalBlock.toMPSTensor hTerminalNormal.no_invariant_proj
      terminalBlock_isLeftCanonical hTerminalNormal.primitive_transfer
  have hCrossBT : Filter.Tendsto
      (fun N : ℕ ↦ MPSTensor.mpvOverlap (d := 5 * 5)
        B terminalBlock.toMPSTensor N) Filter.atTop (nhds 0) :=
    MPSTensor.mpvOverlap_tendsto_zero_of_dim_ne B terminalBlock.toMPSTensor
      hBInj terminalBlock_isInjective hBLeft terminalBlock_isLeftCanonical (by omega)
  have hCrossTB : Filter.Tendsto
      (fun N : ℕ ↦ MPSTensor.mpvOverlap (d := 5 * 5)
        terminalBlock.toMPSTensor B N) Filter.atTop (nhds 0) :=
    MPSTensor.mpvOverlap_tendsto_zero_of_dim_ne terminalBlock.toMPSTensor B
      terminalBlock_isInjective hBInj terminalBlock_isLeftCanonical hBLeft (by omega)
  refine {
    basis_dim_pos := ?_
    basis_irreducible := ?_
    basis_left_canonical := ?_
    basis_normalized_self_overlap := ?_
    bnt_data := ?_
    basis_distinct := ?_
    weight_norm_le_one := ?_
    weight_unit_exists := ?_ }
  · intro j
    change Fin 2 at j
    fin_cases j
    · norm_num
    · exact Nat.one_pos
  · intro j
    change Fin 2 at j
    fin_cases j
    · exact hBNormal.no_invariant_proj
    · exact hTerminalNormal.no_invariant_proj
  · intro j
    change Fin 2 at j
    fin_cases j
    · exact hBLeft
    · exact terminalBlock_isLeftCanonical
  · intro j
    change Fin 2 at j
    fin_cases j
    · exact hBSelf
    · exact hTerminalSelf
  · have hLI := MPSTensor.eventually_linearIndependent_of_finite_overlap_tendsto_orthonormal
        (obstructionTerminalDecomposition mu B hmu).basis
        (fun j ↦ by
          change Fin 2 at j
          fin_cases j
          · exact hBSelf
          · exact hTerminalSelf)
        (fun i j hij ↦ by
          change Fin 2 at i j
          fin_cases i <;> fin_cases j
          · exact absurd rfl hij
          · exact hCrossBT
          · exact hCrossTB
          · exact absurd rfl hij)
    rw [Filter.Eventually] at hLI
    obtain ⟨N0, hN0⟩ := Filter.mem_atTop_sets.mp hLI
    exact ⟨N0, fun N hN ↦ hN0 N (Nat.le_of_lt hN)⟩
  · intro j k hjk hdim
    change Fin 2 at j k
    fin_cases j <;> fin_cases k
    · exact absurd rfl hjk
    · norm_num [obstructionTerminalDecomposition, Fin.cons_succ] at hdim
    · norm_num [obstructionTerminalDecomposition, Fin.cons_succ] at hdim
    · exact absurd rfl hjk
  · intro j q
    change Fin 2 at j
    fin_cases j
    · fin_cases q
      change ‖mu‖ ≤ 1
      exact le_of_lt hmuNorm
    · fin_cases q
      change ‖(1 : ℂ)‖ ≤ 1
      norm_num
  · refine ⟨(Fin.succ 0 : Fin 2), 0, ?_⟩
    change ‖(1 : ℂ)‖ = 1
    norm_num

/-- The prepared neighboring-trace obstruction and terminal block give an
explicit normalized two-sector BNT witness. The obstruction basis tensor
remains unabsorbed and normal; only the gauge target carries the coefficient
`mu`. Its MPO presentation has the first-four-coordinate support, orthogonal
to the terminal support in both multiplication orders. -/
theorem exists_obstruction_terminal_twoBlock_BNT_witness :
    ∃ (mu : ℂ) (B : MPSTensor (5 * 5) 2) (hmu : mu ≠ 0),
      ‖mu‖ < 1 ∧
      Kraus.IsInjective B ∧
      MPSTensor.IsLeftCanonical B ∧
      MPSTensor.IsNormalTensor B ∧
      MPSTensor.GaugeEquiv embeddedObstruction.toMPSTensor (mu • B) ∧
      (obstructionTerminalDecomposition mu B hmu).basisCount = 2 ∧
      (obstructionTerminalDecomposition mu B hmu).copies 0 = 1 ∧
      (obstructionTerminalDecomposition mu B hmu).copies (Fin.succ 0) = 1 ∧
      (obstructionTerminalDecomposition mu B hmu).basisDim 0 = 2 ∧
      (obstructionTerminalDecomposition mu B hmu).basisDim (Fin.succ 0) = 1 ∧
      (obstructionTerminalDecomposition mu B hmu).basis 0 = B ∧
      (obstructionTerminalDecomposition mu B hmu).basis (Fin.succ 0) = terminalBlock.toMPSTensor ∧
      (obstructionTerminalDecomposition mu B hmu).weight 0 0 = mu ∧
      (obstructionTerminalDecomposition mu B hmu).weight (Fin.succ 0) 0 = 1 ∧
      physicalSupportProj (verticalBNTMPO B) = obstructionPhysicalSupport ∧
      physicalSupportProj terminalBlock = terminalPhysicalSupport ∧
      physicalSupportProj (verticalBNTMPO B) * physicalSupportProj terminalBlock = 0 ∧
      physicalSupportProj terminalBlock * physicalSupportProj (verticalBNTMPO B) = 0 ∧
      physicalSupportProj (verticalBNTMPO B) + physicalSupportProj terminalBlock = 1 ∧
      MPSTensor.IsBNTCanonicalForm (obstructionTerminalDecomposition mu B hmu) := by
  obtain ⟨mu, B, hmu, hmuNorm, hBInj, hBLeft, hBNormal, hGauge, hObstructionSupport⟩ :=
    exists_embedded_leftCanonical_normal_obstruction_block
  have hObstructionTerminal :
      physicalSupportProj (verticalBNTMPO B) * physicalSupportProj terminalBlock = 0 := by
    rw [hObstructionSupport, terminalBlock_physicalSupportProj]
    exact obstructionPhysicalSupport_mul_terminalPhysicalSupport
  have hTerminalObstruction :
      physicalSupportProj terminalBlock * physicalSupportProj (verticalBNTMPO B) = 0 := by
    rw [hObstructionSupport, terminalBlock_physicalSupportProj]
    exact terminalPhysicalSupport_mul_obstructionPhysicalSupport
  have hSupportSum :
      physicalSupportProj (verticalBNTMPO B) + physicalSupportProj terminalBlock = 1 := by
    rw [hObstructionSupport, terminalBlock_physicalSupportProj]
    exact obstructionPhysicalSupport_add_terminalPhysicalSupport
  obtain ⟨hDimZero, hDimOne⟩ := obstructionTerminalDecomposition_basisDim mu B hmu
  obtain ⟨hBasisZero, hBasisOne⟩ := obstructionTerminalDecomposition_basis mu B hmu
  refine ⟨mu, B, hmu, hmuNorm, hBInj, hBLeft, hBNormal, hGauge, ?_⟩
  refine ⟨rfl, rfl, rfl, hDimZero, hDimOne,
    hBasisZero, hBasisOne, rfl, rfl, hObstructionSupport,
    terminalBlock_physicalSupportProj, hObstructionTerminal,
    hTerminalObstruction, hSupportSum, ?_⟩
  exact obstructionTerminalDecomposition_isBNTCanonicalForm
    mu B hmu hmuNorm hBInj hBLeft hBNormal

end MPOTensor.NeighboringTraceObstructionAmbientBlocks
