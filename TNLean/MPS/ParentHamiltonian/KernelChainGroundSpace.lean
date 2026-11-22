/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.ChainGroundSpace
import TNLean.MPS.ParentHamiltonian.Martingale.Transport

/-!
# Kernels of finite parent Hamiltonians and chain constraints

This file records the elementary frustration-free direction for the periodic
parent Hamiltonian: since the finite parent Hamiltonian is a sum of local
orthogonal projections, a vector in its kernel satisfies every local cyclic
constraint. Hence the kernel of \(H_N(A,L)\) lies in the periodic
chain-ground-space submodule. The converse is the defining frustration-free
direction of the parent-Hamiltonian construction, so in the nondegenerate range
these two submodules are equal.
-/

open scoped BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- The kernel of the finite periodic parent Hamiltonian is contained in the
periodic chain ground space.

Equivalently, a zero-energy vector for \(H_N(A,L)\) satisfies every cyclic
\(L\)-site local MPS constraint. -/
theorem ker_parentHamiltonian_le_chainGroundSpace
    (A : MPSTensor d D) {L N : ℕ} (hN : 0 < N) (hLN : L ≤ N) :
    LinearMap.ker (parentHamiltonian A L N) ≤ chainGroundSpace A L N := by
  have : NeZero N := ⟨by omega⟩
  intro ψ hψ
  rw [chainGroundSpace, dite_eq_left ⟨hN, hLN⟩]
  simp only [Submodule.mem_iInf, Submodule.mem_comap]
  intro i τ
  have hH : (parentRingInteraction A L N).hamiltonian.mulVec ψ = 0 := by
    rwa [LinearMap.mem_ker, parentHamiltonian_eq_toLin'_hamiltonian A L, Matrix.toLin'_apply] at hψ
  have hlocal :
      Matrix.toEuclideanLin ((parentRingInteraction A L N).term i) (WithLp.toLp 2 ψ) = 0 := by
    rw [Matrix.toLpLin_apply, WithLp.ofLp_toLp,
      (ManyBody.Interaction.hamiltonian_mulVec_eq_zero_iff
        (posSemidef_parentRingInteraction_term A hLN)).mp hH i, WithLp.toLp_zero]
  have hrestrictNS := (mem_groundSpaceES_iff A L _).1
    (cyclicRestrictES_mem_groundSpaceES_of_parentRingInteraction_term_eq_zero A hLN i hlocal τ)
  simpa [cyclicRestrictES] using hrestrictNS

/-- The periodic chain ground space is contained in the kernel of the finite
periodic parent Hamiltonian.

Equivalently, imposing every cyclic \(L\)-site local MPS constraint makes every
translated parent interaction vanish, and hence gives zero total energy. -/
theorem chainGroundSpace_le_ker_parentHamiltonian
    (A : MPSTensor d D) {L N : ℕ} (hN : 0 < N) (hLN : L ≤ N) :
    chainGroundSpace A L N ≤ LinearMap.ker (parentHamiltonian A L N) := by
  intro ψ hψ
  rw [LinearMap.mem_ker]
  have hff : IsFrustrationFree A L N ψ :=
    isFrustrationFree_of_mem_chainGroundSpace A hN hLN hψ
  rw [parentHamiltonian_eq_sum_localTerm, LinearMap.sum_apply]
  exact Finset.sum_eq_zero fun i _ => hff i

/-- In the nondegenerate range, the finite periodic parent-Hamiltonian kernel is
exactly the cyclic chain ground space. -/
theorem ker_parentHamiltonian_eq_chainGroundSpace
    (A : MPSTensor d D) {L N : ℕ} (hN : 0 < N) (hLN : L ≤ N) :
    LinearMap.ker (parentHamiltonian A L N) = chainGroundSpace A L N :=
  le_antisymm (ker_parentHamiltonian_le_chainGroundSpace A hN hLN)
    (chainGroundSpace_le_ker_parentHamiltonian A hN hLN)

/-- The cyclic chain ground space transported to the Euclidean-space model. -/
noncomputable def chainGroundSpaceES (A : MPSTensor d D) (L N : ℕ) :
    Submodule ℂ (EuclideanSpace ℂ (Cfg d N)) :=
  (chainGroundSpace A L N).map
    (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm.toLinearMap

/-- In the nondegenerate range, the Euclidean-space finite parent-Hamiltonian
ground space is the transported cyclic chain ground space. -/
theorem parentHamiltonianGroundSpaceES_eq_chainGroundSpaceES
    (A : MPSTensor d D) {L N : ℕ} (hN : 0 < N) (hLN : L ≤ N) :
    parentHamiltonianGroundSpaceES A L N = chainGroundSpaceES A L N := by
  simp [parentHamiltonianGroundSpaceES, chainGroundSpaceES,
    ker_parentHamiltonian_eq_chainGroundSpace A hN hLN]

end MPSTensor
