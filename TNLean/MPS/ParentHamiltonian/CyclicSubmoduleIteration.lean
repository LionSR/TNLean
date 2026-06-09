/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.UniqueGroundState

/-!
# Cyclic constraints and propagated subspaces

This file records the abstract cyclic-local step used in the block-diagonal
parent-Hamiltonian argument of PGVWC07, Theorem 12.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- Periodic local constraints land in a propagated sequence of subspaces.

If \(G_L(A)\subseteq S_L\) and the subspaces \(S_m\) satisfy
\[
  \mathbb C^d\otimes S_m \cap S_m\otimes \mathbb C^d = S_{m+1}
\]
for all \(m\ge L\), then \(\mathcal G_{N,L}(A)\subseteq S_N\).  This is the
cyclic-local part of the PGVWC07 Theorem 12 argument before the block summands
of \(S_N\) are separated. -/
theorem chainGroundSpace_le_of_local_le_restriction_intersection_submodules
    (A : MPSTensor d D) (S : (M : ℕ) → Submodule ℂ (NSiteSpace d M))
    {L N : ℕ} (hN : 0 < N) (hL : 0 < L) (hLN : L ≤ N) [NeZero d]
    (hlocal : groundSpace A L ≤ S L)
    (hstep : ∀ M : ℕ, L ≤ M →
      ((⨅ b : Fin d, (S M).comap (restrictLastₗ b)) ⊓
        (⨅ a : Fin d, (S M).comap (restrictFirstₗ a))) = S (M + 1)) :
    chainGroundSpace A L N ≤ S N := by
  intro ψ hψ
  rw [chainGroundSpace, dif_pos ⟨hN, hLN⟩] at hψ
  simp only [Submodule.mem_iInf, Submodule.mem_comap] at hψ
  apply contiguous_mem_of_restriction_intersection_submodules S hL hLN hstep
  intro s hs τ
  rw [← cyclicRestrictₗ_eq_contiguousRestrictₗ hN hLN
    (show (⟨s, by omega⟩ : Fin N).val + L ≤ N from hs)]
  exact hlocal (hψ ⟨s, by omega⟩ τ)

end MPSTensor
