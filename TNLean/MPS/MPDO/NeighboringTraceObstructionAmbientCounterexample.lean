/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BiCFDerivation.BNTDirectSum
import TNLean.MPS.MPDO.BNTProjectorSelection
import TNLean.MPS.MPDO.LocalOrthogonalSumAreaLaw
import TNLean.MPS.MPDO.NeighboringTraceObstructionAmbientBlocks
import TNLean.MPS.MPDO.SALTraceTransfer

/-!
# An ambient neighboring-trace obstruction in simple biCF form

This module assembles the rank-one neighboring-trace obstruction and the
terminal product block from `NeighboringTraceObstructionAmbientBlocks` into a
single five-letter matrix product density operator.  Its horizontal
presentation is the literal two-sector basis-of-normal-tensors decomposition:
the obstruction coefficient is absorbed only in the assembled tensor, while
the displayed basis tensor remains normal, and the terminal coefficient is
one.

The assembly follows the standing simple-biCF setting and the block-diagonal
argument of CPSV16, Appendix C.2, lines 1628--1782.  The finite simultaneous
word span and the entropy transport used below are project-derived bridges;
they are not attributed to that passage beyond their stated source roles.
-/

open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace MPOTensor.NeighboringTraceObstructionAmbientCounterexample

open NeighboringTraceObstructionAmbientBlocks

/-- The two-sector decomposition used for the ambient construction. -/
@[reducible] def sectors (mu : ℂ) (B : MPSTensor (5 * 5) 2) (hmu : mu ≠ 0) :
    MPSTensor.SectorDecomposition (5 * 5) :=
  obstructionTerminalDecomposition mu B hmu

/-- The five-letter ambient MPO obtained from the weighted two-sector BNT.

Source role: this is the literal canonical-form assembly in CPSV16,
Appendix C.2, lines 1628--1665. -/
def ambient (mu : ℂ) (B : MPSTensor (5 * 5) 2) (hmu : mu ≠ 0) :
    MPOTensor 5 3 :=
  verticalBNTMPO (sectors mu B hmu).toTensor

/-- The ambient doubled-index tensor is exactly the displayed BNT assembly. -/
@[simp] theorem ambient_toMPSTensor_eq_sectors_toTensor
    (mu : ℂ) (B : MPSTensor (5 * 5) 2) (hmu : mu ≠ 0) :
    (ambient mu B hmu).toMPSTensor = (sectors mu B hmu).toTensor :=
  verticalBNTMPO_toMPSTensor _

/-- The two one-copy coefficients are copy independent. -/
theorem sectors_weight_copy_independent
    (mu : ℂ) (B : MPSTensor (5 * 5) 2) (hmu : mu ≠ 0) :
    ∀ (j : Fin (sectors mu B hmu).basisCount)
      (q q' : Fin ((sectors mu B hmu).copies j)),
      (sectors mu B hmu).weight j q = (sectors mu B hmu).weight j q' := by
  intro j q q'
  fin_cases j <;> exact Subsingleton.elim q q' ▸ rfl

/-- A BNT canonical form supplies the finite simultaneous word span, hence
the biCF condition used at the start of CPSV16 Appendix C.2.

The implication from the quantitative simultaneous span to `HasBiCF` is a
project-derived bridge. -/
theorem sectors_hasBiCF
    (mu : ℂ) (B : MPSTensor (5 * 5) 2) (hmu : mu ≠ 0)
    (hBNT : MPSTensor.IsBNTCanonicalForm (sectors mu B hmu)) :
    MPSTensor.HasBiCF (sectors mu B hmu).basis := by
  obtain ⟨N, _hN, _hNBound, hSpan⟩ :=
    hBNT.exists_basis_wordTupleSpanTop_le_three_totalDim_pow_five
  exact MPSTensor.hasBiCF_of_wordTupleSpanTop (sectors mu B hmu).basis hSpan

/-- Bond dimensions of the two physical sectors. -/
@[reducible] def sectorDim : Fin 2 → ℕ :=
  Fin.cons 2 (fun _ : Fin 1 ↦ 1)

/-- The actual entropy sectors: the embedded obstruction and the terminal
product block. -/
def physicalSector : (s : Fin 2) → MPOTensor 5 (sectorDim s) :=
  Fin.cons embeddedObstruction (fun _ : Fin 1 ↦ terminalBlock)

/-- The corresponding orthogonal one-site support projections. -/
def sectorProjection : Fin 2 → Matrix (Fin 5) (Fin 5) ℂ :=
  Fin.cons obstructionPhysicalSupport (fun _ : Fin 1 ↦ terminalPhysicalSupport)

/-- Each chosen projection is the joint column support of its physical
sector. -/
theorem physicalSector_physicalSupportProj (s : Fin 2) :
    physicalSupportProj (physicalSector s) = sectorProjection s := by
  fin_cases s
  · exact embeddedObstruction_physicalSupportProj
  · exact terminalBlock_physicalSupportProj

/-- The chosen one-site supports are orthogonal projections. -/
theorem sectorProjection_isOrthogonal (s : Fin 2) :
    IsOrthogonalProjection (sectorProjection s) := by
  rw [← physicalSector_physicalSupportProj s]
  exact (Matrix.posSemidef_self_mul_conjTranspose
    (physicalSliceColumns (physicalSector s))).isOrthogonalProjection_supportProj

/-- Distinct physical sectors have orthogonal one-site supports. -/
theorem sectorProjection_mul_eq_zero {s t : Fin 2} (hst : s ≠ t) :
    sectorProjection s * sectorProjection t = 0 := by
  fin_cases s <;> fin_cases t
  · exact absurd rfl hst
  · exact obstructionPhysicalSupport_mul_terminalPhysicalSupport
  · exact terminalPhysicalSupport_mul_obstructionPhysicalSupport
  · exact absurd rfl hst

/-- A tensor's physical support projection fixes it on the ket index.  This
is the tensor-level support identity used in the local orthogonal-sum entropy
argument. -/
private theorem ketLeftMul_physicalSupportProj {d D : ℕ} (K : MPOTensor d D) :
    K.ketLeftMul (physicalSupportProj K) = K := by
  ext i j β α
  have h := congrFun (congrFun (physicalSupportProj_mul_physicalSlice K β α) i) j
  simpa [ketLeftMul, physicalSlice, Matrix.mul_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul] using h

/-- Every nonempty prefix marginal of a physical sector remains in its
chosen one-site support. -/
theorem physicalSector_reducedBlockState_supported
    (s : Fin 2) (N L : ℕ) (_hN : 2 ≤ N) (hL : L + 1 ≤ N) :
    firstSiteMatrix (sectorProjection s) L *
        reducedBlockState (physicalSector s) N (L + 1) hL =
      reducedBlockState (physicalSector s) N (L + 1) hL := by
  apply firstSiteMatrix_mul_reducedBlockState_of_ketLeftMul_eq
  rw [← physicalSector_physicalSupportProj s]
  exact ketLeftMul_physicalSupportProj (physicalSector s)

/-- Gauge-equivalent doubled-index tensors have identical closed MPOs. -/
private theorem mpo_eq_of_gaugeEquiv {d D : ℕ} {K L : MPOTensor d D}
    (hGauge : MPSTensor.GaugeEquiv K.toMPSTensor L.toMPSTensor) (N : ℕ) :
    mpo K N = mpo L N := by
  ext σ τ
  rw [← MPSTensor.mpv_toMPSTensor_pairConfig,
    ← MPSTensor.mpv_toMPSTensor_pairConfig]
  exact hGauge.sameMPV N (fun n ↦ finProdFinEquiv (σ n, τ n))

/-- The first common-weight-absorbed BNT sector is the absorbed obstruction
tensor. -/
private theorem firstAbsorbedSector_toMPSTensor
    (mu : ℂ) (B : MPSTensor (5 * 5) 2) (hmu : mu ≠ 0) :
    (commonWeightAbsorbedBasisMPOTensor (sectors mu B hmu)
      (sectors_weight_copy_independent mu B hmu) 0).toMPSTensor = mu • B := by
  rw [commonWeightAbsorbedBasisMPOTensor_toMPSTensor]
  rfl

/-- The second common-weight-absorbed BNT sector is the terminal block. -/
private theorem secondAbsorbedSector_toMPSTensor
    (mu : ℂ) (B : MPSTensor (5 * 5) 2) (hmu : mu ≠ 0) :
    (commonWeightAbsorbedBasisMPOTensor (sectors mu B hmu)
      (sectors_weight_copy_independent mu B hmu) (Fin.succ 0)).toMPSTensor =
        terminalBlock.toMPSTensor := by
  rw [commonWeightAbsorbedBasisMPOTensor_toMPSTensor]
  change (fun i ↦ (1 : ℂ) • terminalBlock.toMPSTensor i) =
    terminalBlock.toMPSTensor
  simp

/-- The identity presentation gives equality of the positive-length MPV
families of the ambient tensor and its BNT assembly. -/
theorem ambient_sameMPV₂Pos_sectors_toTensor
    (mu : ℂ) (B : MPSTensor (5 * 5) 2) (hmu : mu ≠ 0) :
    MPSTensor.SameMPV₂Pos (ambient mu B hmu).toMPSTensor
      (sectors mu B hmu).toTensor := by
  intro N _hN ρ
  rw [ambient_toMPSTensor_eq_sectors_toTensor]
  rfl

/-- At every positive length, the ambient periodic operator is the sum of
the actual embedded obstruction and terminal periodic operators.

This is the two-sector specialization of the coefficient-absorption identity
in CPSV16, Appendix C.2, lines 1660--1665 and 1753--1770. -/
theorem mpo_ambient_eq_sum_physicalSector
    (mu : ℂ) (B : MPSTensor (5 * 5) 2) (hmu : mu ≠ 0)
    (hGauge : MPSTensor.GaugeEquiv embeddedObstruction.toMPSTensor (mu • B))
    (N : ℕ) (hN : 0 < N) :
    mpo (ambient mu B hmu) N = ∑ s : Fin 2, mpo (physicalSector s) N := by
  rw [mpo_eq_sum_copies_smul_commonWeightAbsorbedBasisMPOTensor
    (ambient mu B hmu) (sectors mu B hmu)
    (ambient_sameMPV₂Pos_sectors_toTensor mu B hmu)
    (sectors_weight_copy_independent mu B hmu) hN]
  have hFirst :
      mpo (commonWeightAbsorbedBasisMPOTensor (sectors mu B hmu)
        (sectors_weight_copy_independent mu B hmu) 0) N =
        mpo embeddedObstruction N := by
    ext σ τ
    rw [← MPSTensor.mpv_toMPSTensor_pairConfig,
      ← MPSTensor.mpv_toMPSTensor_pairConfig,
      firstAbsorbedSector_toMPSTensor]
    exact (hGauge.sameMPV N (fun n ↦ finProdFinEquiv (σ n, τ n))).symm
  have hSecond :
      mpo (commonWeightAbsorbedBasisMPOTensor (sectors mu B hmu)
        (sectors_weight_copy_independent mu B hmu) (Fin.succ 0)) N =
        mpo terminalBlock N := by
    apply mpo_eq_of_gaugeEquiv (N := N)
    rw [secondAbsorbedSector_toMPSTensor]
    exact MPSTensor.GaugeEquiv.refl _
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  have hCopiesZero : (sectors mu B hmu).copies 0 = 1 := rfl
  have hSecond' :
      mpo (commonWeightAbsorbedBasisMPOTensor (sectors mu B hmu)
        (sectors_weight_copy_independent mu B hmu) (1 : Fin 2)) N =
        mpo terminalBlock N := by
    simpa using hSecond
  rw [hCopiesZero]
  norm_num only [Nat.cast_one]
  rw [one_smul, one_smul, hFirst, hSecond']
  rfl

/-- Positivity of the two actual sectors makes the ambient tensor an MPDO. -/
theorem ambient_isMPDO
    (mu : ℂ) (B : MPSTensor (5 * 5) 2) (hmu : mu ≠ 0)
    (hGauge : MPSTensor.GaugeEquiv embeddedObstruction.toMPSTensor (mu • B)) :
    IsMPDO (ambient mu B hmu) := by
  intro N hN
  rw [mpo_ambient_eq_sum_physicalSector mu B hmu hGauge N hN]
  rw [Fin.sum_univ_two]
  exact (embeddedObstruction_isMPDO N hN).add (terminalBlock_isMPDO N hN)

/-- The local orthogonal-sum entropy decomposition transports SAL from the
embedded obstruction and terminal sectors to the ambient tensor. -/
theorem ambient_isSAL
    (mu : ℂ) (B : MPSTensor (5 * 5) 2) (hmu : mu ≠ 0)
    (hGauge : MPSTensor.GaugeEquiv embeddedObstruction.toMPSTensor (mu • B)) :
    IsSAL (ambient mu B hmu) := by
  apply isSAL_of_localOrthogonalSum
    (ambient mu B hmu) physicalSector (fun _ : Fin 2 ↦ 1) sectorProjection
  · intro s
    exact Nat.one_pos
  · exact sectorProjection_isOrthogonal
  · intro s t hst
    exact sectorProjection_mul_eq_zero hst
  · intro N hN
    simpa using mpo_ambient_eq_sum_physicalSector mu B hmu hGauge N hN
  · exact physicalSector_reducedBlockState_supported
  · intro s
    fin_cases s
    · exact embeddedObstruction_isSAL
    · exact terminalBlock_isSAL

/-- Scalar multiplication of a doubled-index tensor scales its physical-trace
transfer by the same scalar. -/
private theorem doubledPhysTraceTransfer_smul {d D : ℕ}
    (c : ℂ) (A : MPSTensor (d * d) D) :
    doubledPhysTraceTransfer d (c • A) = c • doubledPhysTraceTransfer d A := by
  simp [doubledPhysTraceTransfer, Finset.smul_sum]

/-- Scalar multiplication preserves nilpotency. -/
private theorem isNilpotent_smul {n : ℕ} (c : ℂ)
    {T : Matrix (Fin n) (Fin n) ℂ} (hT : IsNilpotent T) :
    IsNilpotent (c • T) := by
  obtain ⟨m, hm⟩ := hT
  exact ⟨m, by rw [smul_pow, hm]; simp⟩

/-- The doubled physical-trace transfers of gauge-equivalent tensors are
similar matrices. -/
private theorem exists_doubledPhysTraceTransfer_eq_conj_of_gaugeEquiv
    {d D : ℕ} {A B : MPSTensor (d * d) D}
    (hGauge : MPSTensor.GaugeEquiv A B) :
    ∃ X : GL (Fin D) ℂ,
      doubledPhysTraceTransfer d B =
        (X : Matrix (Fin D) (Fin D) ℂ) * doubledPhysTraceTransfer d A *
          ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
  obtain ⟨X, hX⟩ := hGauge
  refine ⟨X, ?_⟩
  rw [doubledPhysTraceTransfer, doubledPhysTraceTransfer,
    Matrix.mul_sum, Matrix.sum_mul]
  exact Finset.sum_congr rfl fun i _ ↦ hX (finProdFinEquiv (i, i))

/-- The absorbed obstruction block inherits literal transfer idempotence from
the actual embedded obstruction by virtual gauge similarity. -/
theorem firstAbsorbed_doubledPhysTraceTransfer_idempotent
    (mu : ℂ) (B : MPSTensor (5 * 5) 2)
    (hGauge : MPSTensor.GaugeEquiv embeddedObstruction.toMPSTensor (mu • B)) :
    IsIdempotentElem (doubledPhysTraceTransfer 5 (mu • B)) := by
  obtain ⟨X, hTransfer⟩ :=
    exists_doubledPhysTraceTransfer_eq_conj_of_gaugeEquiv hGauge
  rw [hTransfer]
  calc
    ((X : Matrix (Fin 2) (Fin 2) ℂ) *
          doubledPhysTraceTransfer 5 embeddedObstruction.toMPSTensor *
          ((X⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) *
        ((X : Matrix (Fin 2) (Fin 2) ℂ) *
          doubledPhysTraceTransfer 5 embeddedObstruction.toMPSTensor *
          ((X⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) =
      (X : Matrix (Fin 2) (Fin 2) ℂ) *
        (doubledPhysTraceTransfer 5 embeddedObstruction.toMPSTensor *
          doubledPhysTraceTransfer 5 embeddedObstruction.toMPSTensor) *
        ((X⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by
      simp [Matrix.mul_assoc]
    _ = (X : Matrix (Fin 2) (Fin 2) ℂ) *
        doubledPhysTraceTransfer 5 embeddedObstruction.toMPSTensor *
        ((X⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [doubledPhysTraceTransfer_toMPSTensor,
        embeddedObstruction_physTraceTransfer_idempotent]

/-- The unabsorbed obstruction representative has nonnilpotent
physical-trace transfer.  The proof uses only SAL nonvanishing for the actual
embedded sector, its literal idempotence, nonzero scalar absorption, and
virtual gauge transport. -/
theorem obstructionBasis_doubledPhysTraceTransfer_not_isNilpotent
    (mu : ℂ) (B : MPSTensor (5 * 5) 2)
    (hGauge : MPSTensor.GaugeEquiv embeddedObstruction.toMPSTensor (mu • B)) :
    ¬ IsNilpotent (doubledPhysTraceTransfer 5 B) := by
  intro hNil
  have hScaled : IsNilpotent (doubledPhysTraceTransfer 5 (mu • B)) := by
    rw [doubledPhysTraceTransfer_smul]
    exact isNilpotent_smul mu hNil
  have hEmbedded :
      IsNilpotent (doubledPhysTraceTransfer 5 embeddedObstruction.toMPSTensor) :=
    (isNilpotent_doubledPhysTraceTransfer_iff_of_gaugePhaseEquiv
      hGauge.toGaugePhaseEquiv).mpr hScaled
  rw [doubledPhysTraceTransfer_toMPSTensor] at hEmbedded
  have hIdempotent : IsIdempotentElem (physTraceTransfer embeddedObstruction) :=
    embeddedObstruction_physTraceTransfer_idempotent
  exact embeddedObstruction_isSAL.physTraceTransfer_ne_zero
    (hIdempotent.eq_zero_of_isNilpotent hEmbedded)

/-- Neither unabsorbed representative of the displayed BNT has nilpotent
physical-trace transfer. -/
theorem sectors_basis_doubledPhysTraceTransfer_not_isNilpotent
    (mu : ℂ) (B : MPSTensor (5 * 5) 2) (hmu : mu ≠ 0)
    (hGauge : MPSTensor.GaugeEquiv embeddedObstruction.toMPSTensor (mu • B))
    (j : Fin (sectors mu B hmu).basisCount) :
    ¬ IsNilpotent (doubledPhysTraceTransfer 5 ((sectors mu B hmu).basis j)) := by
  change Fin 2 at j
  by_cases hj : j = 0
  · subst j
    rw [(obstructionTerminalDecomposition_basis mu B hmu).1]
    exact obstructionBasis_doubledPhysTraceTransfer_not_isNilpotent
      mu B hGauge
  · have hj' : j = Fin.succ 0 := by
      fin_cases j <;> simp_all
    subst j
    let S := sectors mu B hmu
    have hDim : S.basisDim (Fin.succ 0) = 1 :=
      (obstructionTerminalDecomposition_basisDim mu B hmu).2
    intro hNil
    have hCast : IsNilpotent
        (doubledPhysTraceTransfer 5
          (cast (congr_arg (MPSTensor (5 * 5)) hDim) (S.basis (Fin.succ 0)))) :=
      (isNilpotent_doubledPhysTraceTransfer_cast_iff hDim
        (S.basis (Fin.succ 0))).mpr hNil
    have hBasis : S.basis (Fin.succ 0) = terminalBlock.toMPSTensor :=
      (obstructionTerminalDecomposition_basis mu B hmu).2
    have hCastEq :
        cast (congr_arg (MPSTensor (5 * 5)) hDim) (S.basis (Fin.succ 0)) =
          terminalBlock.toMPSTensor := by
      apply eq_of_heq
      exact (cast_heq _ _).trans (heq_of_eq hBasis)
    rw [hCastEq, doubledPhysTraceTransfer_toMPSTensor,
      terminalBlock_physTraceTransfer_eq_one] at hCast
    exact not_isNilpotent_one hCast

private theorem isIdempotentElem_smul_doubledPhysTraceTransfer_cast_iff
    {d D₁ D₂ : ℕ} (hdim : D₁ = D₂) (c : ℂ)
    (A : MPSTensor (d * d) D₁) :
    IsIdempotentElem
        (c • doubledPhysTraceTransfer d
          (cast (congr_arg (MPSTensor (d * d)) hdim) A)) ↔
      IsIdempotentElem (c • doubledPhysTraceTransfer d A) := by
  subst D₂
  rfl

/-- Every flattened weighted block of the ambient BNT has idempotent
physical-trace transfer. -/
private theorem sectors_flatWeightedTransfer_idempotent
    (mu : ℂ) (B : MPSTensor (5 * 5) 2) (hmu : mu ≠ 0)
    (hGauge : MPSTensor.GaugeEquiv embeddedObstruction.toMPSTensor (mu • B))
    (s : Fin (sectors mu B hmu).totalCopies) :
    IsIdempotentElem
      ((sectors mu B hmu).flatWeight s •
        doubledPhysTraceTransfer 5 ((sectors mu B hmu).flatBasis s)) := by
  let S := sectors mu B hmu
  change IsIdempotentElem
    (S.flatWeight s • doubledPhysTraceTransfer 5 (S.flatBasis s))
  obtain ⟨⟨j, q⟩, rfl⟩ := S.flatIndexEquiv.surjective s
  rw [MPSTensor.SectorDecomposition.flatWeight_flatIndexEquiv]
  have hDim := S.flatDim_flatIndexEquiv ⟨j, q⟩
  apply (isIdempotentElem_smul_doubledPhysTraceTransfer_cast_iff hDim
    (S.weight j q) (S.flatBasis (S.flatIndexEquiv ⟨j, q⟩))).mp
  have hBasisCast :
      cast (congr_arg (MPSTensor (5 * 5)) hDim)
          (S.flatBasis (S.flatIndexEquiv ⟨j, q⟩)) = S.basis j := by
    apply eq_of_heq
    exact (cast_heq _ _).trans (S.flatBasis_flatIndexEquiv_heq ⟨j, q⟩)
  rw [hBasisCast]
  change Fin 2 at j
  fin_cases j
  · fin_cases q
    change IsIdempotentElem (mu • doubledPhysTraceTransfer 5 B)
    rw [← doubledPhysTraceTransfer_smul]
    exact firstAbsorbed_doubledPhysTraceTransfer_idempotent mu B hGauge
  · fin_cases q
    change IsIdempotentElem
      ((1 : ℂ) • doubledPhysTraceTransfer 5 terminalBlock.toMPSTensor)
    rw [one_smul, doubledPhysTraceTransfer_toMPSTensor,
      terminalBlock_physTraceTransfer_eq_one]
    exact one_mul 1

/-- The ambient tensor satisfies the physical-trace zero-correlation-length
identity without rescaling.

Source: CPSV16, Definition 4.2, lines 735--739, in the standing Appendix C.2
setting at lines 1628--1782. -/
theorem ambient_literal_physTrace_ZCL
    (mu : ℂ) (B : MPSTensor (5 * 5) 2) (hmu : mu ≠ 0)
    (hGauge : MPSTensor.GaugeEquiv embeddedObstruction.toMPSTensor (mu • B)) :
    physTraceTransfer (ambient mu B hmu) *
        physTraceTransfer (ambient mu B hmu) =
      physTraceTransfer (ambient mu B hmu) := by
  let S := sectors mu B hmu
  have hS :
      doubledPhysTraceTransfer 5 S.toTensor *
          doubledPhysTraceTransfer 5 S.toTensor =
        doubledPhysTraceTransfer 5 S.toTensor := by
    have hBlocks :
        (fun s : Fin S.totalCopies ↦
            (S.flatWeight s • doubledPhysTraceTransfer 5 (S.flatBasis s)) *
              (S.flatWeight s • doubledPhysTraceTransfer 5 (S.flatBasis s))) =
          fun s ↦ S.flatWeight s • doubledPhysTraceTransfer 5 (S.flatBasis s) := by
      funext s
      exact sectors_flatWeightedTransfer_idempotent mu B hmu hGauge s
    rw [doubledPhysTraceTransfer_toTensor]
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
    rw [← Matrix.blockDiagonal'_mul, hBlocks]
  rw [← doubledPhysTraceTransfer_toMPSTensor (ambient mu B hmu),
    ambient_toMPSTensor_eq_sectors_toTensor]
  exact hS

/-- The ambient tensor has the displayed simple canonical form.  The terminal
block supplies the single global unit coefficient, and both unabsorbed BNT
representatives have nonnilpotent physical-trace transfer.

**Scope restriction (normalized fixed representative):** this is the
project's fixed-representative predicate, including the global unit-weight
convention at CPSV16, line 246.  See
<https://sirui-lu.com/QICLean/paper-gaps/cpsv16_unit_weight_rfp_scale_tension.pdf>.
Source: CPSV16, canonical form at lines 224--246, simplicity at lines
815--822, and the standing Appendix C.2 hypothesis at line 1628. -/
theorem ambient_isSimpleCanonicalForm
    (mu : ℂ) (B : MPSTensor (5 * 5) 2) (hmu : mu ≠ 0)
    (hGauge : MPSTensor.GaugeEquiv embeddedObstruction.toMPSTensor (mu • B))
    (hBNT : MPSTensor.IsBNTCanonicalForm (sectors mu B hmu)) :
    IsSimpleCanonicalForm (ambient mu B hmu) := by
  refine ⟨ambient_isMPDO mu B hmu hGauge, sectors mu B hmu, hBNT,
    sectors_basis_doubledPhysTraceTransfer_not_isNilpotent mu B hmu hGauge, ?_⟩
  let S := sectors mu B hmu
  have hTotal : S.totalDim = 3 := by rfl
  let X : (s : Fin S.totalCopies) → GL (Fin (S.flatDim s)) ℂ := fun _ ↦ 1
  refine ⟨hTotal, X, ?_⟩
  have hGlobal : MPSTensor.globalGaugeOfBlocks X = 1 := by
    change Units.map _ (Units.map _ ((MulEquiv.piUnits).symm X)) = 1
    rw [show X = 1 by rfl]
    simp
  intro p
  rw [ambient_toMPSTensor_eq_sectors_toTensor]
  simp only [hGlobal, Units.val_one, inv_one, one_mul, mul_one]
  exact (cast_eq _ _).symm

/-- Every positive-length ambient periodic operator has strictly positive
normalization.  This is the normalization clause used in the Appendix C.2
standing MPDO and SAL hypotheses.

Source: CPSV16, lines 623--630, 811--815, and 1760--1780. -/
theorem trace_mpo_ambient_pos
    (mu : ℂ) (B : MPSTensor (5 * 5) 2) (hmu : mu ≠ 0)
    (hGauge : MPSTensor.GaugeEquiv embeddedObstruction.toMPSTensor (mu • B))
    {N : ℕ} (hN : 0 < N) :
    0 < Matrix.trace (mpo (ambient mu B hmu) N) := by
  exact trace_mpo_pos_of_isMPDO_isSourceZCL (ambient mu B hmu)
    (ambient_isMPDO mu B hmu hGauge)
    ((ambient_isSAL mu B hmu hGauge).isSourceZCL_of_physTraceTransfer_sq
      (ambient_literal_physTrace_ZCL mu B hmu hGauge)) hN

/-- There is a five-letter ambient tensor satisfying the complete standing
simple-biCF, MPDO, SAL, and literal physical-trace ZCL package used in CPSV16,
Appendix C.2.  Its displayed BNT has one obstruction block with strict
coefficient bound `0 < ‖mu‖ < 1` and one terminal block with coefficient
exactly one, which is the single global unit-weight witness.

The simultaneous word span behind biCF and the local orthogonal-sum entropy
argument are project-derived bridges.  The displayed canonical assembly,
global normalization, and literal ZCL condition are the source hypotheses at
CPSV16, lines 224--246, 623--630, 735--739, 811--822, and 1628--1782. -/
theorem exists_ambient_standing_simpleBiCF_package :
    ∃ (mu : ℂ) (B : MPSTensor (5 * 5) 2) (hmu : mu ≠ 0),
      0 < ‖mu‖ ∧ ‖mu‖ < 1 ∧
      Kraus.IsInjective B ∧
      MPSTensor.IsLeftCanonical B ∧
      MPSTensor.IsNormalTensor B ∧
      MPSTensor.GaugeEquiv embeddedObstruction.toMPSTensor (mu • B) ∧
      let S := sectors mu B hmu
      let M := ambient mu B hmu
      IsMPDO M ∧
      (∀ N, 0 < N → 0 < Matrix.trace (mpo M N)) ∧
      IsSAL M ∧
      IsSimpleCanonicalForm M ∧
      MPSTensor.IsBNTCanonicalForm S ∧
      MPSTensor.HasBiCF S.basis ∧
      M.toMPSTensor = S.toTensor ∧
      (∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
        S.weight j q = S.weight j q') ∧
      S.basisCount = 2 ∧
      S.copies 0 = 1 ∧
      S.copies (Fin.succ 0) = 1 ∧
      S.basisDim 0 = 2 ∧
      S.basisDim (Fin.succ 0) = 1 ∧
      S.basis 0 = B ∧
      S.basis (Fin.succ 0) = terminalBlock.toMPSTensor ∧
      S.weight 0 0 = mu ∧
      S.weight (Fin.succ 0) 0 = 1 ∧
      physicalSupportProj embeddedObstruction = obstructionPhysicalSupport ∧
      physicalSupportProj terminalBlock = terminalPhysicalSupport ∧
      obstructionPhysicalSupport * terminalPhysicalSupport = 0 ∧
      terminalPhysicalSupport * obstructionPhysicalSupport = 0 ∧
      obstructionPhysicalSupport + terminalPhysicalSupport = 1 ∧
      physTraceTransfer M * physTraceTransfer M = physTraceTransfer M := by
  obtain ⟨mu, B, hmu, hmuNorm, hBInj, hBLeft, hBNormal, hGauge,
    hBasisCount, hCopiesZero, hCopiesOne, hDimZero, hDimOne,
    hBasisZero, hBasisOne, hWeightZero, hWeightOne, _hBSupport,
    _hTerminalSupport, _hSupportZeroTerminal, _hTerminalZeroSupport,
    _hSupportSum, hBNT⟩ := exists_obstruction_terminal_twoBlock_BNT_witness
  have hmuNormPos : 0 < ‖mu‖ := norm_pos_iff.mpr hmu
  refine ⟨mu, B, hmu, hmuNormPos, hmuNorm, hBInj, hBLeft, hBNormal,
    hGauge, ?_⟩
  dsimp only
  exact ⟨ambient_isMPDO mu B hmu hGauge,
    fun N hN ↦ trace_mpo_ambient_pos mu B hmu hGauge hN,
    ambient_isSAL mu B hmu hGauge,
    ambient_isSimpleCanonicalForm mu B hmu hGauge hBNT,
    hBNT, sectors_hasBiCF mu B hmu hBNT,
    ambient_toMPSTensor_eq_sectors_toTensor mu B hmu,
    sectors_weight_copy_independent mu B hmu,
    hBasisCount, hCopiesZero, hCopiesOne, hDimZero, hDimOne,
    hBasisZero, hBasisOne, hWeightZero, hWeightOne,
    embeddedObstruction_physicalSupportProj,
    terminalBlock_physicalSupportProj,
    obstructionPhysicalSupport_mul_terminalPhysicalSupport,
    terminalPhysicalSupport_mul_obstructionPhysicalSupport,
    obstructionPhysicalSupport_add_terminalPhysicalSupport,
    ambient_literal_physTrace_ZCL mu B hmu hGauge⟩

end MPOTensor.NeighboringTraceObstructionAmbientCounterexample
