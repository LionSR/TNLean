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
# Active canonical-block simplicity of the dimer tensor

The rescaling-stable dimer tensor is simple under the active canonical-block
reading of arXiv:1606.00608, Definition 4.7. The witness uses blocking length
one and the active BNT refinement of the tensor's literal CPSV canonical form.
Its retained block has nonnilpotent ket-against-bra contraction.

## Main results

* `toMPSTensor_blockTensor_R_one`: one-site blocking is the canonical physical
  relabeling of the doubled tensor.
* `R_isSourceSimple`: the dimer satisfies the active canonical-block reading of
  Definition 4.7.
* `R_isNonvanishingSourceSimple`: the dimer also satisfies the strengthened
  positive-length nonvanishing predicate.

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

@[deprecated "Simplify directly with `oneSiteDoubledEquiv`." (since := "2026-08-15"), simp]
lemma oneSiteDoubledEquiv_diagonal (i : Fin (MPSTensor.blockPhysDim 4 1)) :
    oneSiteDoubledEquiv (finProdFinEquiv (i, i)) =
      finProdFinEquiv
        (MPSTensor.singleBlockEquiv 4 i, MPSTensor.singleBlockEquiv 4 i) := by
  simp [oneSiteDoubledEquiv]

/-- One-site physical blocking of the dimer gives the canonical physical
relabeling of its doubled-index tensor. -/
theorem toMPSTensor_blockTensor_R_one :
    (MPOTensor.blockTensor R 1).toMPSTensor =
      Kraus.reindexPhysical oneSiteDoubledEquiv R.toMPSTensor := by
  funext ij
  change
    R (MPSTensor.singleBlockEquiv 4 ij.divNat)
        (MPSTensor.singleBlockEquiv 4 ij.modNat) * 1 =
      R (finProdFinEquiv
          (MPSTensor.singleBlockEquiv 4 ij.divNat,
            MPSTensor.singleBlockEquiv 4 ij.modNat)).divNat
        (finProdFinEquiv
          (MPSTensor.singleBlockEquiv 4 ij.divNat,
            MPSTensor.singleBlockEquiv 4 ij.modNat)).modNat
  rw [mul_one, MPSTensor.finProdFinEquiv_divNat, MPSTensor.finProdFinEquiv_modNat]

private theorem R_mpo_ne_zero (N : ℕ) (hN : 0 < N) : mpo R N ≠ 0 := by
  intro hzero
  have hentry := congrFun (congrFun hzero (fun _ => 0)) (fun _ => 0)
  rw [mpo_R_entry_formula hN] at hentry
  simp [chainIndicator, ChainOK, φ, wN, wMat, bondBit1, bondBit2] at hentry

/-- The rescaling-stable dimer tensor is simple under the active canonical-block reading of
Definition 4.7.

The positive blocking length is $L=1$. The BNT is the representative family
supplied by the active refinement of `canonicalFormData`; its only retained
normal block is `retainedBlock`, whose doubled physical-trace transfer is
nonnilpotent.

This theorem neither asserts simplicity for every positive blocking nor changes
the normalized fixed-representative predicate `MPOTensor.IsSimple`.

**Local fix (dormant BNT candidates):** The active presentation follows the nonzero
canonical-block construction and excludes candidates with coefficient identically zero.  See
`docs/paper-gaps/cpsv16_bnt_uniqueness_zero_coefficient.tex`.

Source: arXiv:1606.00608, Definition 4.7, lines 815--822. -/
theorem R_isSourceSimple : MPOTensor.IsSourceSimple R := by
  let data := canonicalFormData.reindexPhysical oneSiteDoubledEquiv
  let ref := data.activeBNTRefinement
  have hActive : Nonempty data.Active := by
    change Nonempty { k : Fin 1 // (weight : ℂ) ≠ 0 }
    refine ⟨⟨0, ?_⟩⟩
    exact_mod_cast weight_ne
  refine ⟨R_isMPDO, 1, by norm_num, ref.representativeSectorDecomposition, ?_, ?_⟩
  · rw [toMPSTensor_blockTensor_R_one]
    exact ref.isActiveCPSVBasisOfNormalTensors hActive
  · intro j
    change ¬ IsNilpotent (MPOTensor.doubledPhysTraceTransfer 4
      (Kraus.reindexPhysical oneSiteDoubledEquiv retainedBlock))
    have hTransfer : MPOTensor.doubledPhysTraceTransfer 4
        (Kraus.reindexPhysical oneSiteDoubledEquiv retainedBlock) =
        MPOTensor.doubledPhysTraceTransfer 4 retainedBlock := by
      rw [MPOTensor.doubledPhysTraceTransfer, MPOTensor.doubledPhysTraceTransfer]
      change (∑ i : Fin (MPSTensor.blockPhysDim 4 1),
          retainedBlock (finProdFinEquiv
            (MPSTensor.singleBlockEquiv 4 i, MPSTensor.singleBlockEquiv 4 i))) =
        ∑ i : Fin 4, retainedBlock (finProdFinEquiv (i, i))
      exact (MPSTensor.singleBlockEquiv 4).sum_comp
        (fun i : Fin 4 => retainedBlock (finProdFinEquiv (i, i)))
    rw [hTransfer]
    exact doubledPhysTraceTransfer_retainedBlock_not_isNilpotent

/-- The dimer satisfies the documented active canonical-block reading of source simplicity,
and its closed MPO is nonzero at every positive chain length. The latter follows by evaluating
the entry identity at the all-zero configuration.

The nonvanishing conjunct is additional to CPSV16 Definition 4.7. -/
theorem R_isNonvanishingSourceSimple : MPOTensor.IsNonvanishingSourceSimple R :=
  ⟨R_isSourceSimple, R_mpo_ne_zero⟩

end MPOTensor.RescalingStableLengthDependentRFP
