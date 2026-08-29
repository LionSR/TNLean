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
noncomputable def terminalSource : MPOTensor 1 1 :=
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

private lemma terminalSource_evalWord {N : ℕ} (σ τ : Fin N → Fin 1) :
    evalWord terminalSource (List.ofFn σ) (List.ofFn τ) = 1 := by
  rw [terminalSource, evalWord_doubledTensor, scalarUnitTensor_evalWord,
    scalarUnitTensor_evalWord]
  simp

private theorem scalarUnitTensor_transferMap :
    Kraus.transferMap MPSTensor.scalarUnitTensor = LinearMap.id := by
  apply LinearMap.ext
  intro X
  ext a b
  fin_cases a
  fin_cases b
  simp [MPSTensor.scalarUnitTensor]

private theorem terminalSource_transferMap :
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
theorem terminalSource_isInjective : Kraus.IsInjective terminalSource.toMPSTensor := by
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
        terminalSource.toMPSTensor terminalSource_transferMap)

private theorem terminalSource_isMPDO : terminalSource.IsMPDO := by
  intro N _hN
  exact doubledTensor_posSemidef MPSTensor.scalarUnitTensor N

private theorem terminalSource_physTraceTransfer :
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
    rw [MPSTensor.IsTransferIdempotent, scalarUnitTensor_transferMap,
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
theorem terminalBlock_physTraceTransfer :
    physTraceTransfer terminalBlock = 1 := by
  rw [terminalBlock, physTraceTransfer_changePhysicalBasis
    terminalPhysicalInclusion terminalPhysicalInclusion_isometry terminalSource]
  exact terminalSource_physTraceTransfer

/-- The terminal block has literal physical-trace idempotence. -/
theorem terminalBlock_physTraceTransfer_idempotent :
    physTraceTransfer terminalBlock * physTraceTransfer terminalBlock =
      physTraceTransfer terminalBlock := by
  rw [terminalBlock_physTraceTransfer, one_mul]

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

/-- The bad and terminal physical supports are orthogonal, in this order. -/
theorem badPhysicalSupport_mul_terminalPhysicalSupport :
    badPhysicalSupport * terminalPhysicalSupport = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [badPhysicalSupport, terminalPhysicalSupport, physicalInclusion,
      terminalPhysicalInclusion, Matrix.mul_apply, Fin.sum_univ_one,
      Fin.sum_univ_four, Fin.sum_univ_five] <;> simp

/-- The terminal and bad physical supports are orthogonal, in the reverse order. -/
theorem terminalPhysicalSupport_mul_badPhysicalSupport :
    terminalPhysicalSupport * badPhysicalSupport = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [badPhysicalSupport, terminalPhysicalSupport, physicalInclusion,
      terminalPhysicalInclusion, Matrix.mul_apply, Fin.sum_univ_one,
      Fin.sum_univ_four, Fin.sum_univ_five] <;> simp

/-- The bad and terminal physical supports resolve the ambient identity. -/
theorem badPhysicalSupport_add_terminalPhysicalSupport :
    badPhysicalSupport + terminalPhysicalSupport = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [badPhysicalSupport, terminalPhysicalSupport, physicalInclusion,
      terminalPhysicalInclusion, Matrix.mul_apply, Fin.sum_univ_one,
      Fin.sum_univ_four, Fin.sum_univ_five] <;> simp

/-! ## The literal two-block SectorBNT decomposition -/

/-- The two-sector, one-copy-per-sector decomposition with bad-block weight
`mu` and terminal-block weight exactly one. -/
@[reducible] noncomputable def badTerminalDecomposition
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

/-- The decomposition has exactly two basis sectors. -/
theorem badTerminalDecomposition_basisCount
    (mu : ℂ) (B : MPSTensor (5 * 5) 2) (hmu : mu ≠ 0) :
    (badTerminalDecomposition mu B hmu).basisCount = 2 := rfl

/-- Each basis sector occurs exactly once. -/
theorem badTerminalDecomposition_copies
    (mu : ℂ) (B : MPSTensor (5 * 5) 2) (hmu : mu ≠ 0)
    (j : Fin (badTerminalDecomposition mu B hmu).basisCount) :
    (badTerminalDecomposition mu B hmu).copies j = 1 := rfl

/-- The two basis bond dimensions are exactly two and one. -/
theorem badTerminalDecomposition_basisDim
    (mu : ℂ) (B : MPSTensor (5 * 5) 2) (hmu : mu ≠ 0) :
    (badTerminalDecomposition mu B hmu).basisDim 0 = 2 ∧
      (badTerminalDecomposition mu B hmu).basisDim (Fin.succ 0) = 1 := by
  constructor
  · rfl
  · rfl

/-- The basis blocks are literally the unabsorbed bad normal block and the
terminal bond-one block. -/
theorem badTerminalDecomposition_basis
    (mu : ℂ) (B : MPSTensor (5 * 5) 2) (hmu : mu ≠ 0) :
    (badTerminalDecomposition mu B hmu).basis 0 = B ∧
      (badTerminalDecomposition mu B hmu).basis (Fin.succ 0) = terminalBlock.toMPSTensor := by
  constructor
  · rfl
  · rfl

/-- The two raw weights are literally `(mu, 1)`. -/
theorem badTerminalDecomposition_weight
    (mu : ℂ) (B : MPSTensor (5 * 5) 2) (hmu : mu ≠ 0) :
    (badTerminalDecomposition mu B hmu).weight 0 0 = mu ∧
      (badTerminalDecomposition mu B hmu).weight (Fin.succ 0) 0 = 1 := by
  constructor
  · rfl
  · rfl

/-- The literal two-block decomposition is in BNT canonical form. The
basis-family separation is forced by the impossible bond-dimension equality
`2 = 1`; the terminal weight supplies the single global unit witness. -/
theorem badTerminalDecomposition_isBNTCanonicalForm
    (mu : ℂ) (B : MPSTensor (5 * 5) 2) (hmu : mu ≠ 0) (hmuNorm : ‖mu‖ < 1)
    (hBInj : Kraus.IsInjective B) (hBLeft : MPSTensor.IsLeftCanonical B)
    (hBNormal : MPSTensor.IsNormalTensor B) :
    MPSTensor.IsBNTCanonicalForm (badTerminalDecomposition mu B hmu) := by
  let hTerminalNormal := terminalBlock_isNormalTensor
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
        (badTerminalDecomposition mu B hmu).basis
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
    · norm_num [badTerminalDecomposition, Fin.cons_succ] at hdim
    · norm_num [badTerminalDecomposition, Fin.cons_succ] at hdim
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

/-- The prepared non-Cartesian candidate and terminal block give an explicit
normalized two-sector BNT witness. The bad basis tensor remains unabsorbed and
normal; only the gauge target carries the coefficient `mu`. -/
theorem exists_bad_terminal_twoBlock_BNT_witness :
    ∃ (mu : ℂ) (B : MPSTensor (5 * 5) 2) (hmu : mu ≠ 0),
      ‖mu‖ < 1 ∧
      Kraus.IsInjective B ∧
      MPSTensor.IsLeftCanonical B ∧
      MPSTensor.IsNormalTensor B ∧
      MPSTensor.GaugeEquiv embeddedCandidate.toMPSTensor (mu • B) ∧
      (badTerminalDecomposition mu B hmu).basisCount = 2 ∧
      (badTerminalDecomposition mu B hmu).copies 0 = 1 ∧
      (badTerminalDecomposition mu B hmu).copies (Fin.succ 0) = 1 ∧
      (badTerminalDecomposition mu B hmu).basisDim 0 = 2 ∧
      (badTerminalDecomposition mu B hmu).basisDim (Fin.succ 0) = 1 ∧
      (badTerminalDecomposition mu B hmu).basis 0 = B ∧
      (badTerminalDecomposition mu B hmu).basis (Fin.succ 0) = terminalBlock.toMPSTensor ∧
      (badTerminalDecomposition mu B hmu).weight 0 0 = mu ∧
      (badTerminalDecomposition mu B hmu).weight (Fin.succ 0) 0 = 1 ∧
      physicalSupportProj embeddedCandidate = badPhysicalSupport ∧
      physicalSupportProj terminalBlock = terminalPhysicalSupport ∧
      badPhysicalSupport * terminalPhysicalSupport = 0 ∧
      terminalPhysicalSupport * badPhysicalSupport = 0 ∧
      badPhysicalSupport + terminalPhysicalSupport = 1 ∧
      MPSTensor.IsBNTCanonicalForm (badTerminalDecomposition mu B hmu) := by
  obtain ⟨mu, B, hmu, hmuNorm, hBInj, hBLeft, hBNormal, hGauge⟩ :=
    exists_embedded_leftCanonical_normal_bad_block
  refine ⟨mu, B, hmu, hmuNorm, hBInj, hBLeft, hBNormal, hGauge, ?_⟩
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    embeddedCandidate_physicalSupportProj, terminalBlock_physicalSupportProj,
    badPhysicalSupport_mul_terminalPhysicalSupport,
    terminalPhysicalSupport_mul_badPhysicalSupport,
    badPhysicalSupport_add_terminalPhysicalSupport, ?_⟩
  exact badTerminalDecomposition_isBNTCanonicalForm
    mu B hmu hmuNorm hBInj hBLeft hBNormal

end MPOTensor.NonCartesianAmbientSectorBlocks
