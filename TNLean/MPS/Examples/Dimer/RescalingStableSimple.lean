/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.BNTPresentation.Refinement
import TNLean.MPS.CanonicalForm.PhysicalReindex
import TNLean.MPS.Examples.Dimer.RescalingStableLengthDependentRFPCanonicalForm
import TNLean.MPS.CanonicalForm.SimpleMPO.Simple

/-!
# Simplicity of the dimer tensor

The rescaling-stable dimer tensor is simple in the sense of arXiv:1606.00608,
Definition 4.7. The witness uses blocking length one and the BNT refinement of
the tensor's literal CPSV canonical form. Its retained block has nonnilpotent
ket-against-bra contraction.

## Main results

* `blockTensor_R_one`: one-site blocking is the canonical physical relabeling of the
  dimer tensor.
* `R_isSimple`: the dimer satisfies Definition 4.7.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Definition 4.7, lines 815--822
-/

open scoped Matrix BigOperators

noncomputable section

namespace MPOTensor.RescalingStableLengthDependentRFP

/-- The canonical relabeling from the ket-bra alphabet after one-site blocking to the
original ket-bra alphabet. -/
def oneSitePairEquiv :
    Fin (Kraus.blockPhysDim 4 1) × Fin (Kraus.blockPhysDim 4 1) ≃ Fin 4 × Fin 4 :=
  Equiv.prodCongr (Kraus.singleBlockEquiv 4) (Kraus.singleBlockEquiv 4)

/-- One-site physical blocking of the dimer is the canonical physical relabeling of the
dimer tensor. -/
theorem blockTensor_R_one :
    MPOTensor.blockTensor R 1 = Kraus.reindexPhysical oneSitePairEquiv R := by
  funext ⟨a, b⟩
  change R (Kraus.singleBlockEquiv 4 a, Kraus.singleBlockEquiv 4 b) * 1 =
    R (Kraus.singleBlockEquiv 4 a, Kraus.singleBlockEquiv 4 b)
  rw [Matrix.mul_one]

/-- The rescaling-stable dimer tensor is simple in the sense of Definition 4.7.

The positive blocking length is $L=1$. The BNT is the representative family
supplied by the BNT refinement of `canonicalFormData`; its only retained
normal block is `retainedBlock`, whose physical-trace transfer is
nonnilpotent.

This theorem does not assert simplicity for every positive blocking.

Source: arXiv:1606.00608, Definition 4.7, lines 815--822. -/
theorem R_isSimple : MPOTensor.IsSimple R := by
  -- T.2c: the BNT refinement is stated on a `Fin` alphabet.
  let e : Fin (Kraus.blockPhysDim 4 1 * Kraus.blockPhysDim 4 1) ≃ Fin 4 × Fin 4 :=
    finProdFinEquiv.symm.trans oneSitePairEquiv
  let data := canonicalFormData.reindexPhysical e
  let ref := data.bntRefinement
  have hBlock : MPOTensor.blockTensor R 1 =
      Kraus.reindexPhysical finProdFinEquiv (Kraus.reindexPhysical e R) := by
    rw [blockTensor_R_one]
    funext x
    simp [Kraus.reindexPhysical, e]
  refine ⟨R_isMPDO, 1, by norm_num, ref.representativeSectorDecomposition.reindexPhysical
    finProdFinEquiv, ?_, ?_⟩
  · rw [hBlock]
    exact (ref.isBNTSectorPresentation Nat.one_pos).reindexPhysical finProdFinEquiv
  · intro j
    change ¬ IsNilpotent (MPOTensor.physTraceTransfer
      (Kraus.reindexPhysical finProdFinEquiv (Kraus.reindexPhysical e retainedBlock)))
    have hTransfer : MPOTensor.physTraceTransfer
        (Kraus.reindexPhysical finProdFinEquiv (Kraus.reindexPhysical e retainedBlock)) =
        MPOTensor.physTraceTransfer retainedBlock := by
      simp only [MPOTensor.physTraceTransfer, Kraus.reindexPhysical, e, oneSitePairEquiv,
        Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.prodCongr_apply, Prod.map]
      exact (Kraus.singleBlockEquiv 4).sum_comp (fun i : Fin 4 => retainedBlock (i, i))
    rw [hTransfer]
    exact physTraceTransfer_retainedBlock_not_isNilpotent

end MPOTensor.RescalingStableLengthDependentRFP
