/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.ActiveBNTRefinement
import TNLean.MPS.CanonicalForm.CPSVPhysicalReindex
import TNLean.MPS.MPDO.RescalingStableLengthDependentRFPCanonicalForm
import TNLean.MPS.MPDO.SourceSimpleTensor

/-!
# Normalization-free Definition 4.7 simplicity of the dimer tensor

The rescaling-stable dimer tensor is simple in the normalization-free,
source-facing sense of arXiv:1606.00608, Definition 4.7. The witness uses
blocking length one and the active BNT refinement of the tensor's literal CPSV
canonical form. Its retained block has nonnilpotent ket-against-bra contraction.

## Main results

* `toMPSTensor_blockTensor_R_one`: one-site blocking is the canonical physical
  relabeling of the doubled tensor.
* `R_isSourceSimple`: the dimer satisfies normalization-free Definition 4.7
  simplicity.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Definition 4.7, lines 815--822
-/

open scoped Matrix BigOperators

noncomputable section

namespace MPOTensor.RescalingStableLengthDependentRFP

/-- The canonical relabeling from the doubled physical alphabet after one-site
blocking to the original doubled physical alphabet. -/
def oneSiteDoubledEquiv :
    Fin (MPSTensor.blockPhysDim 4 1 * MPSTensor.blockPhysDim 4 1) ≃ Fin (4 * 4) :=
  finProdFinEquiv.symm |>.trans
    (Equiv.prodCongr (MPSTensor.singleBlockEquiv 4) (MPSTensor.singleBlockEquiv 4)) |>.trans
      finProdFinEquiv

@[simp]
lemma oneSiteDoubledEquiv_diagonal (i : Fin (MPSTensor.blockPhysDim 4 1)) :
    oneSiteDoubledEquiv (finProdFinEquiv (i, i)) =
      finProdFinEquiv
        (MPSTensor.singleBlockEquiv 4 i, MPSTensor.singleBlockEquiv 4 i) := by
  simp [oneSiteDoubledEquiv]

/-- One-site physical blocking of the dimer gives the canonical physical
relabeling of its doubled-index tensor. -/
theorem toMPSTensor_blockTensor_R_one :
    (MPOTensor.blockTensor R 1).toMPSTensor =
      MPSTensor.reindexPhysical oneSiteDoubledEquiv R.toMPSTensor := by
  funext ij
  simp [MPSTensor.reindexPhysical, MPOTensor.toMPSTensor,
    MPOTensor.blockTensor_apply, MPSTensor.wordOfBlock_one,
    MPOTensor.evalWord, oneSiteDoubledEquiv]
  rw [MPSTensor.finProdFinEquiv_divNat, MPSTensor.finProdFinEquiv_modNat]

/-- The ket-against-bra contraction of `retainedBlock` is unchanged by the
one-site doubled physical relabeling. -/
lemma doubledPhysTraceTransfer_reindexPhysical_oneSiteDoubledEquiv :
    MPOTensor.doubledPhysTraceTransfer 4
        (MPSTensor.reindexPhysical oneSiteDoubledEquiv retainedBlock) =
      MPOTensor.doubledPhysTraceTransfer 4 retainedBlock := by
  rw [MPOTensor.doubledPhysTraceTransfer, MPOTensor.doubledPhysTraceTransfer]
  change (∑ i : Fin (MPSTensor.blockPhysDim 4 1),
      retainedBlock (finProdFinEquiv
        (MPSTensor.singleBlockEquiv 4 i, MPSTensor.singleBlockEquiv 4 i))) =
    ∑ i : Fin 4, retainedBlock (finProdFinEquiv (i, i))
  exact (MPSTensor.singleBlockEquiv 4).sum_comp
    (fun i : Fin 4 => retainedBlock (finProdFinEquiv (i, i)))

/-- The rescaling-stable dimer tensor is simple in the normalization-free,
source-facing sense of Definition 4.7.

The positive blocking length is $L=1$. The BNT is the representative family
supplied by the active refinement of `canonicalFormData`; its only retained
normal block is `retainedBlock`, whose doubled physical-trace transfer is
nonnilpotent.

This theorem neither asserts simplicity for every positive blocking nor changes
the normalized fixed-representative predicate `MPOTensor.IsSimple`.

Source: arXiv:1606.00608, Definition 4.7, lines 815--822. -/
theorem R_isSourceSimple : MPOTensor.IsSourceSimple R := by
  have hRne : ∀ N : ℕ, 0 < N → MPOTensor.mpo R N ≠ 0 := by
    intro N hN hzero
    have hentry := congrFun (congrFun hzero (fun _ => 0)) (fun _ => 0)
    rw [mpo_R_entry_formula hN] at hentry
    simp [chainIndicator, ChainOK, φ, wN, wMat, bondBit1, bondBit2] at hentry
  refine ⟨R_isMPDO, hRne, 1, by norm_num, ?_⟩
  let data := canonicalFormData.reindexPhysical oneSiteDoubledEquiv
  let ref := data.activeBNTRefinement
  refine ⟨data.activePhaseClasses.g,
    fun j => ⟨data.dim (data.activeRepresentativeIndex j),
      data.blocks (data.activeRepresentativeIndex j)⟩, ?_, ?_⟩
  · rw [toMPSTensor_blockTensor_R_one]
    exact ref.representativesBNT
  · intro j
    change ¬ IsNilpotent (MPOTensor.doubledPhysTraceTransfer 4
      (MPSTensor.reindexPhysical oneSiteDoubledEquiv retainedBlock))
    rw [doubledPhysTraceTransfer_reindexPhysical_oneSiteDoubledEquiv]
    exact doubledPhysTraceTransfer_retainedBlock_not_isNilpotent

end MPOTensor.RescalingStableLengthDependentRFP
