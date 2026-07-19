/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.KernelChainGroundSpace
import TNLean.MPS.ParentHamiltonian.UniqueGroundState
import TNLean.MPS.RFP.AppendixBChainCommutation

/-!
# Ground spaces of nearest-neighbor parent Hamiltonians at a renormalization fixed point

For a single normal renormalization fixed-point tensor, the kernel of the
nearest-neighbor parent Hamiltonian on every periodic chain of length greater
than two is the line spanned by the corresponding matrix product vector.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, Theorem 3.10,
  lines 534--541.
-/

namespace MPSTensor

variable {d D : ℕ}

/-- For a single CPSV normal renormalization fixed-point tensor, the kernel of
the nearest-neighbor parent Hamiltonian is spanned, on every periodic chain of
length greater than two, by its matrix product vector.

Source: arXiv:1606.00608, Definition 3.9, lines 517--524, and Theorem 3.10,
lines 534--541.

**Scope restriction (single normal tensor):** The source theorem allows a
canonical-form tensor with several normal sectors and repeated copies. This
result treats the singleton family consisting of one normal tensor. See
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`. -/
theorem rfp_hasParentHamiltonianGroundSpaceSpanning_single
    (A : MPSTensor d D) [NeZero D]
    (hRFP : IsTransferIdempotent A) (hNT : IsNormalTensor A) :
    HasParentHamiltonianGroundSpaceSpanning A 2 (fun _ : Fin 1 ↦ A) := by
  intro N hN
  have hInj : IsInjective A := rfp_nt_structural A hNT.isNormal hRFP
  rw [ker_parentHamiltonian_eq_chainGroundSpace A (by omega) (by omega),
    chainGroundSpace_eq_mpvSubmodule hInj (by omega) (by omega) (by omega),
    ← iSup_mpvSubmodule_eq_bntMPSVectorSpan (fun _ : Fin 1 ↦ A) N]
  simp

/-- A single CPSV normal renormalization fixed-point tensor satisfies the
all-chain nearest-neighbor commuting parent-Hamiltonian ground-space condition.

Source: arXiv:1606.00608, Theorem 3.10, lines 534--541.

**Scope restriction (single normal tensor):** The source theorem allows a
canonical-form tensor with several normal sectors and repeated copies. This
result treats the singleton family consisting of one normal tensor. See
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`. -/
theorem rfp_implies_hasNNCPHGroundSpaces_single
    (A : MPSTensor d D) [NeZero D]
    (hRFP : IsTransferIdempotent A) (hNT : IsNormalTensor A) :
    HasNNCPHGroundSpaces A (fun _ : Fin 1 ↦ A) := by
  rw [hasNNCPHGroundSpaces_iff_forall_isNNCPHGroundState_and_groundSpaceSpanning]
  exact
    ⟨rfp_implies_nncph_ground_state A hRFP hNT,
      rfp_hasParentHamiltonianGroundSpaceSpanning_single A hRFP hNT⟩

end MPSTensor
