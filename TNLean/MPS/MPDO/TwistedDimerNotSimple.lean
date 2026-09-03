/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.BNTRefinement
import TNLean.MPS.CanonicalForm.CPSVBlocking
import TNLean.MPS.CanonicalForm.CPSVPhysicalReindex
import TNLean.MPS.MPDO.SectorTrace
import TNLean.MPS.MPDO.Simple
import TNLean.MPS.MPDO.TwistedDimerHorizontalCF

/-!
# The twisted quantum dimer is not simple

**Scope: Definition 4.7 fails for the twisted dimer at every blocking
length.** The $\mathbb Z_2$-twisted quantum dimer `T` of
`TNLean.MPS.MPDO.TwistedDimer` is a project example, not a tensor stated in
the source. Its doubled-index tensor is in literal canonical form with the two
rescaled horizontal blocks (`TNLean.MPS.MPDO.TwistedDimerHorizontalCF`).
Blocking $L$ sites keeps this canonical form, and its BNT refinement supplies
a BNT sector presentation of the blocked doubled-index tensor. The rescaled
block $k = 1$ has vanishing physical-trace transfer, and blocking raises the
physical-trace transfer to the $L$-th power, so the representative of the
phase class of the blocked block $k = 1$ has nilpotent ket-against-bra
contraction. Presentation independence of nonnilpotency
(`MPOTensor.bnt_basis_not_isNilpotent_iff`) then rules out every presentation
with only nonnilpotent representatives, at every positive blocking length.

## Main results

* `MPOTensor.physTraceTransfer_blockTensor` — blocking raises the
  physical-trace transfer to the power of the blocking length;
* `blockedCanonicalFormData` — the literal canonical form of the blocked
  doubled-index tensor, on the blocked doubled alphabet;
* `T_not_isSimple` — the twisted dimer is not simple in the sense of
  Definition 4.7.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Definition 4.7, lines 815--822, and lines 995--1010 (project example, not a
  tensor stated in the source)
-/

open scoped BigOperators Matrix

noncomputable section

namespace MPOTensor

variable {d D : ℕ}

/-- **Blocking raises the physical-trace transfer to a power.** The
physical-trace transfer of the $L$-site blocking is the sum over all
length-$L$ configurations of the diagonal word evaluations, which is the
$L$-th power of the one-site physical-trace transfer
(`sum_evalWord_diag_eq_verticalLoop_pow`).

Source: arXiv:1606.00608, blocking construction at lines 227--230. -/
theorem physTraceTransfer_blockTensor (M : MPOTensor d D) (L : ℕ) :
    physTraceTransfer (blockTensor M L) = physTraceTransfer M ^ L := by
  rw [← verticalLoop_eq_physTraceTransfer M, ← sum_evalWord_diag_eq_verticalLoop_pow]
  unfold physTraceTransfer
  simp only [blockTensor_apply, Kraus.wordOfBlock]
  exact (MPSTensor.decodeBlockEquiv d L).sum_comp
    fun σ => evalWord M (List.ofFn σ) (List.ofFn σ)

namespace TwistedDimer

/-- The literal canonical form of the $L$-site blocking of the twisted dimer,
on the doubled alphabet of the blocked tensor: the one-site canonical form
`canonicalFormData` blocked by `L` and relabeled along the canonical pairing of
the blocked ket and bra words.

Source: arXiv:1606.00608, Section 2.3, lines 214--245, blocked as in lines
317--345 (project example). -/
def blockedCanonicalFormData (L : ℕ) (hL : 0 < L) :
    MPSTensor.CPSVCanonicalFormData
      (Kraus.reindexPhysical (blockedDoubledIndexEquiv 8 L)
        (MPSTensor.blockTensor T.toMPSTensor L)) :=
  (canonicalFormData.blockTensor L hL).reindexPhysical (blockedDoubledIndexEquiv 8 L)

/-- The retained blocks of the blocked canonical form are the doubled-index
tensors of the blocked rescaled horizontal blocks. -/
lemma blockedCanonicalFormData_blocks (L : ℕ) (hL : 0 < L) (k : Fin 2) :
    (blockedCanonicalFormData L hL).blocks k = (blockTensor (normalizedBlock k) L).toMPSTensor := by
  rw [toMPSTensor_blockTensor]
  rfl

/-- The blocked rescaled block $k = 1$ has vanishing ket-against-bra
contraction: the one-site physical-trace transfer vanishes
(`physTraceTransfer_normalizedBlock_one`), and blocking raises it to a
positive power. -/
lemma doubledPhysTraceTransfer_blockedCanonicalFormData_blocks_one (L : ℕ) (hL : 0 < L) :
    doubledPhysTraceTransfer (MPSTensor.blockPhysDim 8 L)
      ((blockedCanonicalFormData L hL).blocks (1 : Fin 2)) = 0 := by
  have h : doubledPhysTraceTransfer (MPSTensor.blockPhysDim 8 L)
      (blockTensor (normalizedBlock 1) L).toMPSTensor = 0 := by
    rw [doubledPhysTraceTransfer_toMPSTensor, physTraceTransfer_blockTensor,
      physTraceTransfer_normalizedBlock_one, zero_pow hL.ne']
  exact (congrArg (doubledPhysTraceTransfer (MPSTensor.blockPhysDim 8 L))
    (blockedCanonicalFormData_blocks L hL 1)).trans h

/-- **The twisted quantum dimer is not simple** in the sense of
arXiv:1606.00608, Definition 4.7, lines 815--822.

Fix a positive blocking length $L$ and a BNT sector presentation $P$ of the
blocked doubled-index tensor. The BNT refinement of the blocked literal
canonical form `blockedCanonicalFormData` is another presentation $Q$, whose
representatives are chosen among the two blocked rescaled horizontal blocks.
The blocked block $k = 1$ is a gauge-phase multiple of its class
representative, and its ket-against-bra contraction vanishes, so that
representative has nilpotent contraction. By presentation independence
(`bnt_basis_not_isNilpotent_iff`), $P$ also has a representative with
nilpotent contraction.

This is a project example, not a tensor stated in the source. -/
theorem T_not_isSimple : ¬ IsSimple T := by
  rintro ⟨_, L, hL, P, hPres, hNonNil⟩
  rw [toMPSTensor_blockTensor] at hPres
  let data := blockedCanonicalFormData L hL
  let ref := data.bntRefinement
  have hQ : MPSTensor.IsBNTSectorPresentation _ ref.representativeSectorDecomposition :=
    ref.isBNTSectorPresentation (show (0 : ℕ) < 2 by norm_num)
  have hAll := (bnt_basis_not_isNilpotent_iff hPres hQ).mp hNonNil
  let k₁ : Fin data.r := (1 : Fin 2)
  apply hAll (data.classCopy k₁).1
  have hGauge : MPSTensor.GaugePhaseEquiv
      (cast (congr_arg (MPSTensor (MPSTensor.blockPhysDim 8 L * MPSTensor.blockPhysDim 8 L))
          (ref.copyDimEq k₁))
        (data.blocks (data.representativeIndex (data.classCopy k₁).1)))
      (data.blocks k₁) := by
    refine ⟨ref.listedGauge k₁, ref.copyPhase k₁,
      Complex.ne_zero_of_norm_eq_one (ref.copyPhaseNorm k₁), fun i => ?_⟩
    rw [ref.blocksEqListedGaugeConj k₁ i, ref.regroupedBlocksEq k₁]
    simp only [smul_mul_assoc, mul_smul_comm]
  have hNil : IsNilpotent (doubledPhysTraceTransfer (MPSTensor.blockPhysDim 8 L)
      (data.blocks k₁)) := by
    rw [doubledPhysTraceTransfer_blockedCanonicalFormData_blocks_one]
    exact IsNilpotent.zero
  exact (isNilpotent_doubledPhysTraceTransfer_cast_iff (ref.copyDimEq k₁) _).mp
    ((isNilpotent_doubledPhysTraceTransfer_iff_of_gaugePhaseEquiv hGauge).mpr hNil)

end TwistedDimer

end MPOTensor
