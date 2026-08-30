/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CPSVSharpBlocking
import TNLean.MPS.MPDO.BiCFDerivation.DirectSumUniqueness
import TNLean.MPS.ParentHamiltonian.GroundSpaceSpanning
import TNLean.MPS.RFP.NNCPHMultiSector

/-!
# Nearest-neighbor parent Hamiltonians after sharp CPSV blocking

A tensor in literal CPSV canonical form admits a blocking of at most
$3D^5$ sites for which the nearest-neighbor parent-Hamiltonian ground space on
the blocked lattice is spanned by the blocked basis of normal tensors.

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
$1 \le p \le 3D^5$ makes the actual blocked tensor's range-two periodic parent
Hamiltonian have ground space spanned by the blocked distinct BNT vectors for
every blocked-chain length $N>2$.

This is the blocked-lattice statement in arXiv:1606.00608, line 527, using
Proposition `propblockinj` (lines 342--345) and Definition 3.9
(lines 511--525). -/
theorem IsCPSVCanonicalForm.exists_bnt_blocked_hasNearestNeighborParentHamiltonian
    {A : MPSTensor d D} [NeZero D] (hA : IsCPSVCanonicalForm A) :
    ∃ g : ℕ, ∃ dim : Fin g → ℕ,
      ∃ B : (j : Fin g) → MPSTensor d (dim j),
      IsCPSVBasisOfNormalTensors A (fun j => ⟨dim j, B j⟩) ∧
      ∃ p, 0 < p ∧ p ≤ 3 * D ^ 5 ∧
        HasParentHamiltonianGroundSpaceSpanning
          (MPSTensor.blockTensor A p) 2
          (fun j => MPSTensor.blockTensor (B j) p) := by
  obtain ⟨g, dim, B, hBNT, p, hp, hpBound, hOne, hLocal⟩ :=
    hA.exists_bnt_sharp_blocking_and_groundSpace
  refine ⟨g, dim, B, hBNT, p, hp, hpBound, ?_⟩
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
    let blocks : (j : Fin g) → MPSTensor (blockPhysDim d p) (dim j) :=
      fun j ↦ MPSTensor.blockTensor (B j) p
    let : ∀ j : Fin g, NeZero (dim j) := fun j ↦
      ⟨(hBNT.blocks_normal j).bondDim_ne_zero⟩
    have hDirect :
        HasParentHamiltonianGroundSpaceSpanning
          (toTensorFromBlocks (d := blockPhysDim d p) (fun _ ↦ 1) blocks) 2 blocks := by
      apply hasParentHamiltonianGroundSpaceSpanning_toTensorFromBlocks_of_chain_eq_iSup_chain
        (fun _ ↦ 1) blocks (by simp)
      · intro N hN
        exact chainGroundSpace_toTensorFromBlocks_eq_iSup_of_wordTupleSpanTop_one
          (fun _ ↦ 1) blocks (by simp) hOne hN
      · intro N hN j
        exact chainGroundSpace_eq_mpvSubmodule
          (hOne.isInjective_one j) (by omega) (by omega) (by omega)
    have hDirectLocal :
        groundSpace
            (toTensorFromBlocks (d := blockPhysDim d p) (fun _ ↦ 1) blocks) 2 =
          ⨆ j : Fin g, groundSpace (blocks j) 2 :=
      groundSpace_toTensorFromBlocks_eq_iSup (fun _ ↦ 1) blocks (by simp) 2
    have hActualDirect :
        groundSpace (MPSTensor.blockTensor A p) 2 =
          groundSpace
            (toTensorFromBlocks (d := blockPhysDim d p) (fun _ ↦ 1) blocks) 2 := by
      exact hLocal.trans hDirectLocal.symm
    intro N hN
    have hNpos : 0 < N := by omega
    have hTwoN : 2 ≤ N := by omega
    calc
      LinearMap.ker (parentHamiltonian (MPSTensor.blockTensor A p) 2 N) =
          chainGroundSpace (MPSTensor.blockTensor A p) 2 N :=
        ker_parentHamiltonian_eq_chainGroundSpace _ hNpos hTwoN
      _ = chainGroundSpace
          (toTensorFromBlocks (d := blockPhysDim d p) (fun _ ↦ 1) blocks) 2 N :=
        chainGroundSpace_eq_of_groundSpace_eq hActualDirect
      _ = LinearMap.ker
          (parentHamiltonian
            (toTensorFromBlocks (d := blockPhysDim d p) (fun _ ↦ 1) blocks) 2 N) :=
        (ker_parentHamiltonian_eq_chainGroundSpace _ hNpos hTwoN).symm
      _ = bntMPSVectorSpan blocks N := hDirect N hN

end MPSTensor
