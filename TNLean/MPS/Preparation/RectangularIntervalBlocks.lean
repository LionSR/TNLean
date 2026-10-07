/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Chain.RectangularIntervals
import TNLean.MPS.Preparation.RectangularBlocks
import QICLean.Algebra.MatrixDependentEntries

/-!
# Actual block channels as rectangular intervals

The rectangular matrices in each partition block are the original site matrices at its
successive cuts. Their transfer map is the corresponding ordered rectangular interval.
Only equality-based relabeling of the final bond is needed at the ring closure.

## References

* arXiv:2307.01696v2, paragraph "Inhomogeneous short-range correlated MPS".
-/

open Matrix MPSPreparation MPSTensor Fin.NatCast
open scoped BigOperators

namespace VaryingBondChain

variable {d D N M : ℕ} [NeZero N]

/-- Each actual site in a block is the original site at the same natural-number cut. -/
theorem rectangularBlockSites_eq_siteTensorAt (A : VaryingBondChain d D N)
    {ℓ : Fin M → ℕ} (hN : ∑ j, ℓ j = N) (k : Fin M) (i : Fin (ℓ k)) :
    rectangularBlockSites A hN k i = siteTensorAt A (blockOffset ℓ k.val + i.val) := by
  have hsite : blockSite hN k i = ((blockOffset ℓ k.val + i.val : ℕ) : Fin N) := by
    apply Fin.ext
    exact (Nat.mod_eq_of_lt (blockOffset_add_lt hN k i)).symm
  funext s
  ext x y
  apply Matrix.entry_eq_of_heq (fun j => A.tensor j s) hsite
  · exact (Fin.heq_ext_iff (congrArg A.bondDim hsite)).2 rfl
  · exact (Fin.heq_ext_iff (congrArg (fun j => A.bondDim (finRotate N j)) hsite)).2 rfl

/-- The actual recursive block transfer is the corresponding natural-cut interval. -/
theorem rectangularTransfer_block_eq_channelInterval (A : VaryingBondChain d D N)
    {ℓ : Fin M → ℕ} (hN : ∑ j, ℓ j = N) (k : Fin M) :
    Kraus.rectangularTransfer (blockBondDim A ℓ k) (rectangularBlockSites A hN k) =
      Matrix.channelInterval (siteTransferAt A) (blockOffset ℓ k.val)
        (blockOffset ℓ k.val + ℓ k) (Nat.le_add_right _ _) := by
  rw [Kraus.rectangularTransfer_eq_channelInterval (blockBondDim A ℓ k)
    (rectangularBlockSites A hN k) (fun i => siteTransferAt A (blockOffset ℓ k.val + i))
      (fun i => by rw [rectangularBlockSites_eq_siteTensorAt]; rfl)]
  exact Matrix.channelInterval_shift (siteTransferAt A) (blockOffset ℓ k.val)
    (Nat.zero_le (ℓ k))

/-- Relabeling the final actual bond of the blocked tensor by its natural-number cut
identifies its Kraus map with the actual ordered interval. -/
theorem rectangularKrausMap_blockTensor_cast_eq_channelInterval (A : VaryingBondChain d D N)
    {ℓ : Fin M → ℕ} (hN : ∑ j, ℓ j = N) (k : Fin M) :
    Matrix.rectangularKrausMap (fun s =>
      (rectangularBlockTensor A hN k s).submatrix id
        (Fin.cast (blockBondDim_length A hN k))) =
      Matrix.channelInterval (siteTransferAt A) (blockOffset ℓ k.val)
        (blockOffset ℓ k.val + ℓ k) (Nat.le_add_right _ _) := by
  refine Eq.trans ?_ (rectangularTransfer_block_eq_channelInterval A hN k)
  have ht (s : Fin (blockPhysDim d (ℓ k))) :
      (rectangularBlockTensor A hN k s).submatrix id
          (Fin.cast (blockBondDim_length A hN k)) =
        Kraus.rectangularEval (blockBondDim A ℓ k) (rectangularBlockSites A hN k)
          (decodeBlockEquiv d (ℓ k) s) := by
    ext x y
    rfl
  simp_rw [ht]
  calc
    Matrix.rectangularKrausMap (fun s =>
        Kraus.rectangularEval (blockBondDim A ℓ k) (rectangularBlockSites A hN k)
          (decodeBlockEquiv d (ℓ k) s)) =
      Matrix.rectangularKrausMap
        (Kraus.rectangularEval (blockBondDim A ℓ k) (rectangularBlockSites A hN k)) :=
      Matrix.rectangularKrausMap_equiv (decodeBlockEquiv d (ℓ k)).symm
        (Kraus.rectangularEval (blockBondDim A ℓ k) (rectangularBlockSites A hN k))
    _ =
        Kraus.rectangularTransfer (blockBondDim A ℓ k) (rectangularBlockSites A hN k) := by
      ext X : 1
      exact (Kraus.rectangularTransfer_apply _ _ X).symm

end VaryingBondChain
