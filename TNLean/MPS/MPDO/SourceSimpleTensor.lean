/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.ActiveBNTRefinement
import TNLean.MPS.CanonicalForm.CPSVPhysicalReindex
import TNLean.MPS.MPDO.RescalingStableLengthDependentRFPCanonicalForm

/-!
# Normalization-free Definition 4.7 simplicity

This module records the source-facing simplicity condition of arXiv:1606.00608,
Definition 4.7. After a positive physical blocking, the doubled-index tensor must
admit a CPSV basis of normal tensors, and the ket-against-bra contraction of every
basis element must be nonnilpotent. The interface includes the condition that the
tensor generates MPDOs, but deliberately excludes the separate line-246
unit-weight normalization.

## Main results

* `MPOTensor.IsSourceSimple`: normalization-free Definition 4.7 simplicity.
* `MPOTensor.RescalingStableLengthDependentRFP.toMPSTensor_blockTensor_R_one`:
  one-site blocking is the canonical physical relabeling of the doubled tensor.
* `MPOTensor.RescalingStableLengthDependentRFP.R_isSourceSimple`: the dimer is
  simple in the normalization-free Definition 4.7 sense, witnessed at blocking
  length one by the active BNT refinement of its literal canonical form.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Definition 4.7, lines 815--822
-/

open scoped Matrix BigOperators

noncomputable section

namespace MPOTensor

variable {d D : ℕ}

/-- **Normalization-free Definition 4.7 simplicity.** A tensor generating MPDOs
is source-simple when, after some positive physical blocking, its doubled-index
tensor has a CPSV basis of normal tensors and no basis element has nilpotent
ket-against-bra contraction.

The witness uses `MPSTensor.IsCPSVBasisOfNormalTensors`, rather than an arbitrary
family of canonical blocks. It does not impose the line-246 unit-weight
normalization and makes no claim that every positive blocking has such a witness.

Source: arXiv:1606.00608, Definition 4.7, lines 815--822. -/
def IsSourceSimple (M : MPOTensor d D) : Prop :=
  IsMPDO M ∧
    ∃ L : ℕ, 0 < L ∧
      ∃ g : ℕ,
        ∃ blocks : (j : Fin g) →
            Σ D' : ℕ, MPSTensor
              (MPSTensor.blockPhysDim d L * MPSTensor.blockPhysDim d L) D',
          MPSTensor.IsCPSVBasisOfNormalTensors (blockTensor M L).toMPSTensor blocks ∧
            ∀ j, ¬ IsNilpotent
              (doubledPhysTraceTransfer (MPSTensor.blockPhysDim d L) (blocks j).2)

end MPOTensor

namespace MPOTensor.RescalingStableLengthDependentRFP

/-- The canonical relabeling from the doubled physical alphabet after one-site
blocking to the original doubled physical alphabet. -/
noncomputable def oneSiteDoubledEquiv :
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
  refine ⟨R_isMPDO, 1, by norm_num, ?_⟩
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
