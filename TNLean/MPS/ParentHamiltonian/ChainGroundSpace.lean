/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Basic
import TNLean.MPS.ParentHamiltonian.CyclicWindow

/-!
# Periodic chain ground spaces for parent Hamiltonians

For a tensor \(A\) on a periodic chain of \(N\) sites, the length-\(L\) chain
ground space is the intersection of all cyclic \(L\)-site local constraints.
This file contains the generic definitions and elementary consequences that do
not use injectivity or uniqueness.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-! ### The MPS submodule -/

/-- The submodule spanned by the MPS vector.
On the periodic chain, the MPS vector is
\(\sigma \mapsto \operatorname{tr}(A^{\sigma_0} \cdots A^{\sigma_{N-1}})\),
which corresponds to the ground-space map applied to the identity:
\(V^{(N)}(A)=Γ_N(1)\). -/
noncomputable def mpvSubmodule (A : MPSTensor d D) (N : ℕ) :
    Submodule ℂ (NSiteSpace d N) :=
  Submodule.span ℂ {mpv A}

/-- The MPS vector is the ground-space map applied to the identity matrix. -/
theorem mpv_eq_groundSpaceMap_one (A : MPSTensor d D) (N : ℕ) :
    (mpv A : NSiteSpace d N) = groundSpaceMap A N 1 := by
  ext σ
  simp [mpv, coeff, groundSpaceMap_apply]

/-- The MPS vector lies in the ground space \(G_N(A)\) for any \(N\). -/
theorem mpv_mem_groundSpace (A : MPSTensor d D) (N : ℕ) :
    (mpv A : NSiteSpace d N) ∈ groundSpace A N := by
  rw [groundSpace, LinearMap.mem_range]
  exact ⟨1, by ext σ; simp [groundSpaceMap_apply, mpv, coeff]⟩

/-! ### Periodic chain ground space

On a periodic chain of \(N\) sites, the ground space of the parent Hamiltonian
is the set of states whose restriction to every cyclic window of \(L\) consecutive
sites lies in \(G_L(A)\).

For the nondegenerate regime used below, this is the intersection of all cyclic
window constraints. The subsequent theorems state their nondegeneracy assumptions
explicitly. -/

/-- The periodic chain ground space: the set of states \(ψ\) on \(N\) sites such
that every cyclic window of \(L\) consecutive sites restricts into \(G_L(A)\).

When \(N = 0\) or \(L > N\), we return \(\top\) as a degenerate convention. -/
noncomputable def chainGroundSpace (A : MPSTensor d D) (L N : ℕ) :
    Submodule ℂ (NSiteSpace d N) :=
  if hN : 0 < N ∧ L ≤ N then
    ⨅ (i : Fin N) (τ : Fin N → Fin d),
      (groundSpace A L).comap (cyclicRestrictₗ hN.1 L i τ)
  else ⊤

/-- The MPS vector is in the chain ground space.

The proof uses trace cyclicity: for each cyclic window at position \(i\), the
restriction of the MPS vector to that window equals `groundSpaceMap A L X_τ` where
\(X_\tau\) is the product of \(A\)-matrices at outside positions. The cyclic list
verification follows from the window-level membership calculation. -/
theorem mpv_mem_chainGroundSpace (A : MPSTensor d D) (L N : ℕ)
    (hN : 0 < N) (hLN : L ≤ N) :
    (mpv A : NSiteSpace d N) ∈ chainGroundSpace A L N := by
  rw [chainGroundSpace, dif_pos ⟨hN, hLN⟩]
  simp only [Submodule.mem_iInf, Submodule.mem_comap]
  intro i τ
  have hrestrict :
      cyclicRestrictₗ hN L i τ (mpv A) =
        (fun σ => mpv A (replaceWindow L hLN i τ σ)) := by
    ext σ
    rw [cyclicRestrictₗ_apply]
    have hcfg : cyclicCfg hN L i σ τ = replaceWindow L hLN i τ σ := rfl
    rw [hcfg]
  rw [hrestrict]
  exact mpv_window_mem_groundSpace A L N hLN i τ

/-- A vector in the periodic chain ground space is annihilated by every local
parent-Hamiltonian term.

This is the local constraint direction in the parent-Hamiltonian construction:
membership in every cyclic \(L\)-site ground-space window implies the
frustration-free equations for the translated parent interactions. -/
theorem isFrustrationFree_of_mem_chainGroundSpace (A : MPSTensor d D)
    {L N : ℕ} (hN : 0 < N) (hLN : L ≤ N)
    {ψ : NSiteSpace d N} (hψ : ψ ∈ chainGroundSpace A L N) :
    IsFrustrationFree A L N ψ := by
  rw [chainGroundSpace, dif_pos ⟨hN, hLN⟩] at hψ
  simp only [Submodule.mem_iInf, Submodule.mem_comap] at hψ
  intro i
  ext σ
  simp only [localTerm, hLN, ↓reduceDIte, LinearMap.pi_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Pi.zero_apply]
  have hrestrict :
      (fun τ => ψ (replaceWindow L hLN i σ τ)) =
        cyclicRestrictₗ hN L i σ ψ := by
    ext τ
    rw [cyclicRestrictₗ_apply]
    have hcfg : replaceWindow L hLN i σ τ = cyclicCfg hN L i τ σ := rfl
    rw [hcfg]
  have hmem : (fun τ => ψ (replaceWindow L hLN i σ τ)) ∈ groundSpace A L := by
    rw [hrestrict]
    exact hψ i σ
  have hkill := parentInteraction_apply_mem_groundSpace A L _ hmem
  change (parentInteraction A L (fun τ => ψ (replaceWindow L hLN i σ τ)))
    (extractWindow L i σ) = 0
  rw [hkill]
  rfl

/-- Every constrained cyclic window of a chain-ground-space vector has a boundary
matrix representation in the local MPS ground space. -/
theorem chainGroundSpace_window_witnesses (A : MPSTensor d D)
    {L N : ℕ} (hN : 0 < N) (hLN : L ≤ N)
    {ψ : NSiteSpace d N} (hψ : ψ ∈ chainGroundSpace A L N) :
    ∃ YAt : (i : Fin N) → (Fin N → Fin d) → Matrix (Fin D) (Fin D) ℂ,
      ∀ (i : Fin N) (τ : Fin N → Fin d),
        cyclicRestrictₗ hN L i τ ψ = groundSpaceMap A L (YAt i τ) := by
  rw [chainGroundSpace, dif_pos ⟨hN, hLN⟩] at hψ
  simp only [Submodule.mem_iInf, Submodule.mem_comap] at hψ
  have hLocal : ∀ (i : Fin N) (τ : Fin N → Fin d),
      ∃ Y : Matrix (Fin D) (Fin D) ℂ,
        cyclicRestrictₗ hN L i τ ψ = groundSpaceMap A L Y := by
    intro i τ
    have hmem := hψ i τ
    rw [groundSpace, LinearMap.mem_range] at hmem
    obtain ⟨Y, hY⟩ := hmem
    exact ⟨Y, hY.symm⟩
  choose YAt hYAt using hLocal
  exact ⟨YAt, hYAt⟩

/-- Peeling the last site of every cyclic window shows that a larger interaction
range imposes at least the constraints of the preceding range. -/
theorem chainGroundSpace_le_chainGroundSpace_succ (A : MPSTensor d D)
    {L N : ℕ} (hN : 0 < N) (hLN : L + 1 ≤ N) :
    chainGroundSpace A (L + 1) N ≤ chainGroundSpace A L N := by
  intro ψ hψ
  rw [chainGroundSpace, dif_pos ⟨hN, hLN⟩] at hψ
  simp only [Submodule.mem_iInf, Submodule.mem_comap] at hψ
  rw [chainGroundSpace, dif_pos ⟨hN, show L ≤ N from by omega⟩]
  simp only [Submodule.mem_iInf, Submodule.mem_comap]
  intro i τ
  let peeled : Fin N := ⟨(i.val + L) % N, Nat.mod_lt _ hN⟩
  let τ' : Fin N → Fin d :=
    fun k => if (k.val + N - i.val) % N = L then τ peeled else τ k
  have hτ' : cyclicRestrictₗ hN L i τ' ψ = cyclicRestrictₗ hN L i τ ψ := by
    ext σ
    simp only [cyclicRestrictₗ_apply]
    congr 1
    ext k
    simp only [cyclicCfg]
    by_cases hsmall : (k.val + N - i.val) % N < L
    · rw [dif_pos hsmall, dif_pos hsmall]
    · rw [dif_neg hsmall, dif_neg hsmall]
      by_cases hlast : (k.val + N - i.val) % N = L
      · have hk : k = peeled :=
          eq_cyclic_site_of_offset_eq hN hlast
        simp [τ', hk]
      · simp [τ', hlast]
  have hbig := hψ i τ
  have hleft := groundSpace_inLeftGround A L hbig (τ peeled)
  rw [cyclicRestrictₗ_restrictLast hN i τ ψ (τ peeled)] at hleft
  exact hτ' ▸ hleft

/-- The periodic chain ground space is antitone in the interaction range: longer
cyclic windows imply all shorter cyclic-window constraints. -/
theorem chainGroundSpace_le_chainGroundSpace_of_le (A : MPSTensor d D)
    {L' L N : ℕ} (hN : 0 < N) (hL'L : L' ≤ L) (hLN : L ≤ N) :
    chainGroundSpace A L N ≤ chainGroundSpace A L' N := by
  have claim : ∀ m : ℕ, L' + m ≤ N →
      chainGroundSpace A (L' + m) N ≤ chainGroundSpace A L' N := by
    intro m
    induction m with
    | zero =>
        intro _ ψ hψ
        simpa using hψ
    | succ m ih =>
        intro hmN
        exact le_trans
          (by
            simpa [Nat.add_assoc] using
              chainGroundSpace_le_chainGroundSpace_succ (A := A) hN
                (L := L' + m) (by omega : L' + m + 1 ≤ N))
          (ih (by omega))
  have hEq : L' + (L - L') = L := Nat.add_sub_of_le hL'L
  simpa [hEq] using claim (L - L') (by omega : L' + (L - L') ≤ N)

end MPSTensor
