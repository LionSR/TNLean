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
chain-ground-space submodule.
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
  intro ψ hψ
  rw [chainGroundSpace, dif_pos ⟨hN, hLN⟩]
  simp only [Submodule.mem_iInf, Submodule.mem_comap]
  intro i τ
  let eN := WithLp.linearEquiv 2 ℂ (NSiteSpace d N)
  have hES : parentHamiltonianES A L N (eN.symm ψ) = 0 := by
    rw [LinearMap.mem_ker] at hψ
    simpa [parentHamiltonianES, eN] using congrArg eN.symm hψ
  have hlocal :
      localTermES A L i (eN.symm ψ) = 0 := by
    rw [parentHamiltonianES_eq_sum_localTermES A L N] at hES
    exact ProjectionGeometry.apply_eq_zero_of_sum_apply_eq_zero
      (fun i : Fin N => localTermES A L i)
      (fun i : Fin N => localTermES_isSymmetricProjection A L i) hES i
  have hrestrictES :
      cyclicRestrictES (d := d) hN L i τ (eN.symm ψ) ∈ groundSpaceES A L :=
    cyclicRestrictES_mem_groundSpaceES_of_localTermES_eq_zero A hLN i hlocal τ
  let eL := WithLp.linearEquiv 2 ℂ (NSiteSpace d L)
  have hrestrictNS :
      eL (cyclicRestrictES (d := d) hN L i τ (eN.symm ψ)) ∈ groundSpace A L :=
    (mem_groundSpaceES_iff A L
      (cyclicRestrictES (d := d) hN L i τ (eN.symm ψ))).1 hrestrictES
  simpa [cyclicRestrictES, eN, eL] using hrestrictNS

end MPSTensor
