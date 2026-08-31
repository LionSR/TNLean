/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CPSVSharpBlocking
import TNLean.MPS.MPDO.SourceBNTBlocking
import TNLean.MPS.ParentHamiltonian.BlockDiagonalOneSiteSpan
import TNLean.MPS.ParentHamiltonian.CoisometricReconstruction

/-!
# Nearest-neighbor parent Hamiltonians after sharp CPSV blocking

A tensor in literal CPSV canonical form admits a blocking of at most
\(3D^5\) sites for which the nearest-neighbor parent-Hamiltonian ground space on
the blocked lattice is spanned by the blocked basis of normal tensors.

**Scope restriction (blocked lattice):** This module proves the second
statement of arXiv:1606.00608, line 527, on the blocked lattice. It does not
prove the preceding original-lattice range bound for every sufficiently long
ring. The distinction is documented in
`docs/paper-gaps/cpsv16_parent_hamiltonian_range_short_ring.tex`.

## Main result

* `MPSTensor.IsCPSVCanonicalForm.exists_bnt_blocked_hasNearestNeighborParentHamiltonian`

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, Proposition
  `propblockinj`, lines 342--345, and Definition 3.9, lines 511--527.
* Perez-Garcia--Verstraete--Wolf--Cirac, arXiv:quant-ph/0608197, Theorem 12,
  proof lines 1424--1456.
-/

namespace MPSTensor

variable {d D : ℕ}

/-- **CPSV16 blocked nearest-neighbor parent Hamiltonian.**

For a tensor in literal CPSV canonical form, some blocking length
\(1 \le p \le 3D^5\) makes the actual blocked tensor's range-two periodic parent
Hamiltonian have ground space spanned by the blocked distinct BNT vectors for
every blocked-chain length \(N>2\). The blocked tensors themselves form a BNT
of the blocked ambient tensor, as required by Definition 3.9.

This is the blocked-lattice statement in arXiv:1606.00608, line 527, using
Proposition `propblockinj` (lines 342--345) and Definition 3.9
(lines 511--525). -/
theorem IsCPSVCanonicalForm.exists_bnt_blocked_hasNearestNeighborParentHamiltonian
    {A : MPSTensor d D} [NeZero D] (hA : IsCPSVCanonicalForm A) :
    ∃ g : ℕ, ∃ dim : Fin g → ℕ,
      ∃ B : (j : Fin g) → MPSTensor d (dim j),
      IsCPSVBasisOfNormalTensors A (fun j => ⟨dim j, B j⟩) ∧
      ∃ p, 0 < p ∧ p ≤ 3 * D ^ 5 ∧
        IsCPSVBasisOfNormalTensors (MPSTensor.blockTensor A p)
          (fun j => ⟨dim j, MPSTensor.blockTensor (B j) p⟩) ∧
        HasParentHamiltonianGroundSpaceSpanning
          (MPSTensor.blockTensor A p) 2
          (fun j => MPSTensor.blockTensor (B j) p) := by
  let data := Classical.choice hA
  let ref := data.bntRefinement
  let dim : Fin data.phaseClasses.g → ℕ := fun j =>
    data.dim (data.representativeIndex j)
  let B : (j : Fin data.phaseClasses.g) → MPSTensor d (dim j) := fun j =>
    data.blocks (data.representativeIndex j)
  have hBNT : IsCPSVBasisOfNormalTensors A (fun j => ⟨dim j, B j⟩) := by
    simpa [dim, B] using ref.representativesBNT
  obtain ⟨p, hp, hpBound, hSpan⟩ :=
    hBNT.exists_positive_wordTupleSpanTop_le_three_cap_pow_five
      (NeZero.pos D) (by simpa [dim] using data.sum_representative_dim_le)
  have hOne : WordTupleSpanTop (fun j => MPSTensor.blockTensor (B j) p) 1 :=
    wordTupleSpanTop_blockTensor_one B hSpan
  have hLocal :
      groundSpace (MPSTensor.blockTensor A p) 2 =
        ⨆ j : Fin data.phaseClasses.g,
          groundSpace (MPSTensor.blockTensor (B j) p) 2 := by
    simpa [B] using
      data.groundSpace_blockTensor_eq_iSup_representatives ref hp (by omega : 0 < 2)
  refine ⟨data.phaseClasses.g, dim, B, hBNT, p, hp, hpBound,
    hBNT.blockTensor hp, ?_⟩
  by_cases hd : d = 0
  · subst d
    intro N hN
    ext ψ
    have hPhys : blockPhysDim 0 p = 0 := by
      rw [blockPhysDim_eq_pow, zero_pow hp.ne']
    have hψ : ψ = 0 := by
      funext σ
      exact Fin.elim0 (Fin.cast hPhys (σ ⟨0, by omega⟩))
    subst ψ
    simp
  · let : NeZero d := ⟨hd⟩
    let blocks : (j : Fin data.phaseClasses.g) →
        MPSTensor (blockPhysDim d p) (dim j) :=
      fun j ↦ MPSTensor.blockTensor (B j) p
    let : ∀ j : Fin data.phaseClasses.g, NeZero (dim j) := fun j ↦
      ⟨(hBNT.blocks_normal j).bondDim_ne_zero⟩
    have hDirect :
        HasParentHamiltonianGroundSpaceSpanning
          (toTensorFromBlocks (d := blockPhysDim d p) (fun _ ↦ 1) blocks) 2 blocks := by
      exact
        hasParentHamiltonianGroundSpaceSpanning_toTensorFromBlocks_of_wordTupleSpanTop_one
          (fun _ ↦ 1) blocks (by simp) hOne
    have hDirectLocal :
        groundSpace
            (toTensorFromBlocks (d := blockPhysDim d p) (fun _ ↦ 1) blocks) 2 =
          ⨆ j : Fin data.phaseClasses.g, groundSpace (blocks j) 2 :=
      groundSpace_toTensorFromBlocks_eq_iSup (fun _ ↦ 1) blocks (by simp) 2
    have hActualDirect :
        groundSpace (MPSTensor.blockTensor A p) 2 =
          groundSpace
            (toTensorFromBlocks (d := blockPhysDim d p) (fun _ ↦ 1) blocks) 2 := by
      exact hLocal.trans hDirectLocal.symm
    exact hDirect.of_groundSpace_eq hActualDirect

end MPSTensor
