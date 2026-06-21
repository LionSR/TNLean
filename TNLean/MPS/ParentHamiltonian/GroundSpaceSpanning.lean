/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockDiagonalChainGroundSpace
import TNLean.MPS.ParentHamiltonian.Commuting

/-!
# Ground-space spanning for block-diagonal parent Hamiltonians

This file reduces the source ground-space spanning clause from
arXiv:1606.00608, Definition 3.9, for block-diagonal tensors to the reverse
inclusion. The easy inclusion of the BNT span into the parent-Hamiltonian kernel
is already proved; therefore the source spanning condition is equivalent to the
reverse inclusion.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

/-- For a block-diagonal tensor with nonzero weights, the source parent-Hamiltonian
ground-space spanning clause is equivalent to the reverse inclusion.

Let \(B=\bigoplus_{j=0}^{r-1}\mu_jA_j\), with every \(\mu_j\ne0\). The inclusion
\[
  \operatorname{span}\{V^{(N)}(A_j):j=0,\ldots,r-1\}
  \subseteq \ker H_L^{(N)}(B)
\]
is the easy direction, already proved by
`bntMPSVectorSpan_le_ker_parentHamiltonian_toTensorFromBlocks`. Hence the
Definition 3.9 spanning equation is reduced to proving, for every \(N>L\),
\[
  \ker H_L^{(N)}(B)
  \subseteq
  \operatorname{span}\{V^{(N)}(A_j):j=0,\ldots,r-1\}.
\]
See arXiv:1606.00608, Definition 3.9, source lines 522--524. -/
theorem hasParentHamiltonianGroundSpaceSpanning_toTensorFromBlocks_iff_ker_le_bntMPSVectorSpan
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j : Fin r, μ j ≠ 0) {L : ℕ} :
    HasParentHamiltonianGroundSpaceSpanning
        (toTensorFromBlocks (d := d) (μ := μ) A) L A ↔
      ∀ N : ℕ, L < N →
        LinearMap.ker (parentHamiltonian
          (toTensorFromBlocks (d := d) (μ := μ) A) L N) ≤
          bntMPSVectorSpan A N := by
  constructor
  · intro hSpan N hN
    rw [hSpan N hN]
  · intro hReverse N hN
    refine le_antisymm (hReverse N hN) ?_
    have hNpos : 0 < N := lt_of_le_of_lt (Nat.zero_le L) hN
    exact bntMPSVectorSpan_le_ker_parentHamiltonian_toTensorFromBlocks
      μ A hμ hNpos (le_of_lt hN)

/-- For block-diagonal nearest-neighbor parent Hamiltonians, the all-chain
source condition is equivalent to all-chain translated parent-term commutation
together with the reverse ground-space inclusion.

This is the nearest-neighbor specialization of
`hasParentHamiltonianGroundSpaceSpanning_toTensorFromBlocks_iff_ker_le_bntMPSVectorSpan`.
It isolates the remaining spanning direction in arXiv:1606.00608,
Theorem 3.10(iii), after the easy inclusion for the BNT vectors. -/
theorem hasNNCPHGroundSpaces_toTensorFromBlocks_iff_forall_isNNCPH_and_ker_le_bntMPSVectorSpan
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j : Fin r, μ j ≠ 0) :
    HasNNCPHGroundSpaces (toTensorFromBlocks (d := d) (μ := μ) A) A ↔
      (∀ N : ℕ, 2 < N →
        IsNNCPH (toTensorFromBlocks (d := d) (μ := μ) A) N) ∧
      ∀ N : ℕ, 2 < N →
        LinearMap.ker (parentHamiltonian
          (toTensorFromBlocks (d := d) (μ := μ) A) 2 N) ≤
          bntMPSVectorSpan A N := by
  rw [hasNNCPHGroundSpaces_iff_forall_isNNCPH_and_groundSpaceSpanning,
    hasParentHamiltonianGroundSpaceSpanning_toTensorFromBlocks_iff_ker_le_bntMPSVectorSpan
      μ A hμ]

end MPSTensor
