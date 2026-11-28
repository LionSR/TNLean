/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.GroundSpace.ChainGroundSpace
import TNLean.MPS.Tensor.GroundSpace.UniqueGroundState
import TNLean.MPS.ParentHamiltonian.ParentInteraction.Transport

/-!
# Kernels of finite parent Hamiltonians and chain constraints

This file records the elementary frustration-free direction for the periodic
parent Hamiltonian: since the finite parent Hamiltonian is a sum of local
orthogonal projections, a vector in its kernel satisfies every local cyclic
constraint. Hence the kernel of \(H_N(A,L)\) lies in the periodic
chain-ground-space submodule. The converse is the defining frustration-free
direction of the parent-Hamiltonian construction, so in the nondegenerate range
these two submodules are equal. With the description of the chain ground space of a
block-injective tensor as the line through the periodic MPS vector, this gives the unique
ground state of the parent Hamiltonian on the ring.
-/

open scoped BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- The kernel of the finite periodic parent Hamiltonian is contained in the
periodic chain ground space.

Equivalently, a zero-energy vector for \(H_N(A,L)\) satisfies every cyclic
\(L\)-site local MPS constraint. -/
theorem ker_hamiltonian_parentRingInteraction_le_chainGroundSpace
    (A : MPSTensor d D) {L N : ℕ} (hN : 0 < N) (hLN : L ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    LinearMap.ker (Matrix.toLin' (parentRingInteraction A L N).hamiltonian) ≤
      chainGroundSpace A L N := by
  have : NeZero N := ⟨by omega⟩
  intro ψ hψ
  rw [chainGroundSpace, dite_eq_left ⟨hN, hLN⟩]
  simp only [Submodule.mem_iInf, Submodule.mem_comap]
  intro i τ
  have hH : (parentRingInteraction A L N).hamiltonian.mulVec ψ = 0 := by
    rwa [LinearMap.mem_ker, Matrix.toLin'_apply] at hψ
  have hlocal :
      Matrix.toEuclideanLin ((parentRingInteraction A L N).term i) (WithLp.toLp 2 ψ) = 0 := by
    rw [Matrix.toLpLin_apply, WithLp.ofLp_toLp,
      (ManyBody.Interaction.hamiltonian_mulVec_eq_zero_iff
        (posSemidef_parentRingInteraction_term A _)).mp hH i, WithLp.toLp_zero]
  have hrestrictNS := (mem_groundSpaceES_iff A L _).1
    (cyclicRestrictES_mem_groundSpaceES_of_parentRingInteraction_term_eq_zero A hLN i hlocal τ)
  simpa [cyclicRestrictES] using hrestrictNS

/-- The periodic chain ground space is contained in the kernel of the finite
periodic parent Hamiltonian.

Equivalently, imposing every cyclic \(L\)-site local MPS constraint makes every
translated parent interaction vanish, and hence gives zero total energy. -/
theorem chainGroundSpace_le_ker_hamiltonian_parentRingInteraction
    (A : MPSTensor d D) {L N : ℕ} (hN : 0 < N) (hLN : L ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    chainGroundSpace A L N ≤
      LinearMap.ker (Matrix.toLin' (parentRingInteraction A L N).hamiltonian) := by
  have : NeZero N := ⟨by omega⟩
  intro ψ hψ
  rw [LinearMap.mem_ker, Matrix.toLin'_apply]
  exact (ManyBody.Interaction.mem_zeroSpace_iff_hamiltonian_mulVec_eq_zero
    fun i ↦ posSemidef_parentRingInteraction_term A L i).mp
    (toLp_mem_zeroSpace_parentRingInteraction_of_mem_chainGroundSpace A hN hLN hψ)

/-- In the nondegenerate range, the finite periodic parent-Hamiltonian kernel is
exactly the cyclic chain ground space. -/
theorem ker_hamiltonian_parentRingInteraction_eq_chainGroundSpace
    (A : MPSTensor d D) {L N : ℕ} (hN : 0 < N) (hLN : L ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    LinearMap.ker (Matrix.toLin' (parentRingInteraction A L N).hamiltonian) =
      chainGroundSpace A L N :=
  le_antisymm (ker_hamiltonian_parentRingInteraction_le_chainGroundSpace A hN hLN)
    (chainGroundSpace_le_ker_hamiltonian_parentRingInteraction A hN hLN)

/-- **The ground space of the parent Hamiltonian on the ring.** In the nondegenerate range
\(0 < N\), \(L \le N\), the ground space at energy \(0\) of the Hamiltonian of the parent
interaction on the ring is the cyclic chain ground space, read in the Euclidean space. -/
theorem groundSpace_hamiltonian_parentRingInteraction_eq_map_chainGroundSpace
    (A : MPSTensor d D) {L N : ℕ} (hN : 0 < N) (hLN : L ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    ManyBody.groundSpace (parentRingInteraction A L N).hamiltonian 0 =
      (chainGroundSpace A L N).map
        (WithLp.linearEquiv 2 ℂ (NSiteSpace (Fin d) N)).symm.toLinearMap := by
  have : NeZero N := ⟨by omega⟩
  rw [groundSpace_hamiltonian_parentRingInteraction_eq_map_ker,
    ker_hamiltonian_parentRingInteraction_eq_chainGroundSpace A hN hLN]

/-- **The zero space of the parent interaction on the ring.** In the nondegenerate range
\(0 < N\), \(L \le N\), the vectors annihilated by every translated parent interaction are
those of the cyclic chain ground space, read in the Euclidean space: the frustration-free
ground space is the intersection of the local ground-space constraints. [PGVWC07]
(quant-ph/0608197), Section 3.3. -/
theorem zeroSpace_parentRingInteraction_eq_map_chainGroundSpace
    (A : MPSTensor d D) {L N : ℕ} (hN : 0 < N) (hLN : L ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    (parentRingInteraction A L N).zeroSpace =
      (chainGroundSpace A L N).map
        (WithLp.linearEquiv 2 ℂ (NSiteSpace (Fin d) N)).symm.toLinearMap := by
  have : NeZero N := ⟨by omega⟩
  rw [ManyBody.Interaction.zeroSpace_eq_groundSpace
    fun i ↦ posSemidef_parentRingInteraction_term A L i]
  exact groundSpace_hamiltonian_parentRingInteraction_eq_map_chainGroundSpace A hN hLN

/-! ### Unique ground state -/

/-- **Unique periodic ground state** for a block-injective tensor throughout the interaction
range \(L₀<L\le N\): the periodic MPS vector is nonzero and the ground space at energy \(0\)
of the parent Hamiltonian on the ring is the line through it. This strengthens the finite-size
assumption \(N\ge 2L₀\) printed in [PGVWC07] (quant-ph/0608197), Theorem `uniqueGS`,
`MPSarchive.tex`, lines 1272--1274, to \(N\ge L₀+1\), together with \(N\ge2\). -/
theorem parentHamiltonian_unique_gs {A : MPSTensor d D} [NeZero D]
    {L₀ : ℕ} (hInj : Kraus.IsNBlkInjective A L₀) (hL₀ : 0 < L₀)
    {L N : ℕ} (hL : L₀ < L) (hLN : L ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    ManyBody.groundSpace (parentRingInteraction A L N).hamiltonian 0 = ℂ ∙ mpvState A N ∧
      mpvState A N ≠ 0 := by
  have hNormal : Kraus.IsNormal A := ⟨L₀, hL₀, hInj⟩
  have hNlarge : L₀ + 1 ≤ N := by omega
  refine ⟨?_, mpvState_ne_zero_of_isNBlkInjective hInj hL₀ hNlarge⟩
  rw [groundSpace_hamiltonian_parentRingInteraction_eq_map_chainGroundSpace A (by omega) hLN,
    chainGroundSpace_eq_mpvSubmodule_normal hNormal hInj hL₀ (by omega) hL hLN hNlarge,
    mpvSubmodule, Submodule.map_span, Set.image_singleton]
  rfl

/-- Unique periodic ground state for an injective tensor at every interaction range
\(1<L\le N\): the periodic MPS vector is nonzero and the ground space at energy \(0\) of the
parent Hamiltonian on the ring is the line through it. This is the case \(L₀=1\) of
`parentHamiltonian_unique_gs`. -/
theorem groundSpace_unique_periodic {A : MPSTensor d D} [NeZero D] (hA : Kraus.IsInjective A)
    {L N : ℕ} (hL : 1 < L) (hLN : L ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    ManyBody.groundSpace (parentRingInteraction A L N).hamiltonian 0 = ℂ ∙ mpvState A N ∧
      mpvState A N ≠ 0 :=
  parentHamiltonian_unique_gs (Kraus.isNBlkInjective_one_of_isInjective hA) one_pos hL hLN

/-- Unique ground state for tensors injective after blocking at range \(2L₀\): the periodic
MPS vector is nonzero and spans the ground space at energy \(0\) of the parent Hamiltonian
on the ring. This includes the endpoint \(L₀=1,N=2\). This is the one-dimensional
specialization of arXiv:2011.12127, Section IV.C, lines 2041--2048. -/
theorem parentHamiltonian_unique_gs_injective {A : MPSTensor d D} [NeZero D]
    {L₀ : ℕ} (hA : Kraus.IsNBlkInjective A L₀) (hL₀ : 0 < L₀)
    {N : ℕ} (hN : 2 * L₀ ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    ManyBody.groundSpace (parentRingInteraction A (2 * L₀) N).hamiltonian 0 =
        ℂ ∙ mpvState A N ∧
      mpvState A N ≠ 0 :=
  parentHamiltonian_unique_gs hA hL₀ (by omega) hN

/-- Unique ground state for normal tensors at range \(L₀+1\) on every ring
with \(L₀+1\le N\): the periodic MPS vector is nonzero and spans the ground space at energy
\(0\) of the parent Hamiltonian on the ring. This is arXiv:2011.12127, Section IV.C, lines
2086--2094.

The normality hypothesis is redundant because positive-length block injectivity already
implies normality; it is retained in this specialization. -/
theorem parentHamiltonian_unique_gs_normal {A : MPSTensor d D} [NeZero D]
    {L₀ : ℕ} (_hA : Kraus.IsNormal A) (hInj : Kraus.IsNBlkInjective A L₀) (hL₀ : 0 < L₀)
    {N : ℕ} (hN : L₀ + 1 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    ManyBody.groundSpace (parentRingInteraction A (L₀ + 1) N).hamiltonian 0 =
        ℂ ∙ mpvState A N ∧
      mpvState A N ≠ 0 :=
  parentHamiltonian_unique_gs hInj hL₀ (by omega) hN

end MPSTensor
