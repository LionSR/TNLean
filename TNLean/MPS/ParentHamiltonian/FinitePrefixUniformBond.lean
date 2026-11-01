/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.PrimeLengthBondDimensionDichotomy
import TNLean.MPS.Preparation.PeriodicFiniteRepresentation
import TNLean.MPS.Preparation.PeriodicBondPadding

/-!
# The finite-prefix step for uniform periodic MPS bond bounds

An eventual fixed tensor gives one common bond bound for every exactly
cyclic-invariant ground vector, including all short positive volumes.
The short representations are constructed from actual OBC existence and
cyclic averaging, rather than assumed. Padding then gives one common
matrix size, while the tensors themselves may depend on the volume.

The exact condition for a nonzero ground vector to have a periodic trace
representation is that its cyclic momentum is zero. Uniqueness gives an
invariant ground line, which does not by itself state this condition.

**Scope restriction (zero-momentum finite prefix):** the uniform ground
family is proved precisely when every permitted short positive volume has
a nonzero zero-momentum ground vector. This condition is characterized,
not derived from the source's unique frustration-free ground-space
hypothesis. See
`docs/paper-gaps/spwc10_ground_state_dichotomy_quantifiers.tex`.

Source: SPWC10, arXiv:0909.5347, Theorem 5 and proof, lines 850--880.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

variable {d L : ℕ}

/-- An actual eventual fixed ground tensor supplies a uniform common
bond dimension for all exactly cyclic-invariant nonzero ground vectors
at all permitted positive volumes. Short representations are constructed,
with no supplied finite-volume MPS premise.
Source: the finite-prefix completion of SPWC10, Theorem 5, lines 850--880. -/
theorem exists_uniform_bond_on_cyclic_ground_sector
    (h : MPVSpace d L →ₗ[ℂ] MPVSpace d L)
    (hUnique : ∀ M, L ≤ M →
      Module.finrank ℂ (LinearMap.ker (periodicInteractionHamiltonianES h M)) = 1)
    {D : ℕ} (B : MPSTensor d D) (M₀ : ℕ)
    (hB : ∀ M, M₀ ≤ M → mpvState B M ≠ 0 ∧
      LinearMap.ker (periodicInteractionHamiltonianES h M) = ℂ ∙ mpvState B M) :
    ∃ K : ℕ, 0 < K ∧
      ∀ M, 0 < M → L ≤ M → ∀ ψ : MPVSpace d M,
        ψ ≠ 0 → periodicInteractionHamiltonianES h M ψ = 0 →
        (∀ (s : Fin M) (σ : Fin M → Fin d), ψ (fun k ↦ σ (k + s)) = ψ σ) →
        ∃ C : MPSTensor d K, mpvState C M ≠ 0 ∧
          LinearMap.ker (periodicInteractionHamiltonianES h M) = ℂ ∙ mpvState C M := by
  classical
  let K := D + M₀ * d ^ M₀ + 1
  refine ⟨K, by dsimp [K]; omega, ?_⟩
  intro M hM hLM ψ hψ hzero hTI
  by_cases hlong : M₀ ≤ M
  · let C := padBond B K
    have hDK : D ≤ K := by dsimp [K]; omega
    have hC : mpvState C M = mpvState B M := mpvState_padBond B hDK hM
    exact ⟨C, by rw [hC]; exact (hB M hlong).1, by rw [hC]; exact (hB M hlong).2⟩
  · have hd : 0 < d := by
      by_contra hd
      have hd0 : d = 0 := by omega
      subst d
      apply hψ
      apply PiLp.ext
      intro σ
      exact Fin.elim0 (σ ⟨0, hM⟩)
    obtain ⟨C, hC⟩ := exists_mpvState_eq_of_cyclic_invariant hM ψ hψ hTI
    have hCK : M * d ^ (M / 2) ≤ K := by
      have hpow : d ^ (M / 2) ≤ d ^ M₀ := Nat.pow_le_pow_right hd (by omega)
      have hmul := Nat.mul_le_mul (show M ≤ M₀ by omega) hpow
      dsimp [K]
      omega
    let C' := padBond C K
    have hC' : mpvState C' M = ψ := (mpvState_padBond C hCK hM).trans hC
    refine ⟨C', by rwa [hC'], ?_⟩
    rw [hC']
    exact eq_span_singleton_of_mem_of_finrank_eq_one (hUnique M hLM) hzero hψ

/-- The literal all-positive-volume common-bond family is equivalent to
zero cyclic momentum at the finitely many permitted volumes preceding
the eventual fixed tensor. This makes the remaining source quantifier
explicit without assuming short periodic representations.
Source: SPWC10, Theorem 5, lines 850--880, finite-prefix boundary. -/
theorem uniform_bond_family_iff_short_cyclic_ground
    (h : MPVSpace d L →ₗ[ℂ] MPVSpace d L)
    (hUnique : ∀ M, L ≤ M →
      Module.finrank ℂ (LinearMap.ker (periodicInteractionHamiltonianES h M)) = 1)
    {D : ℕ} (B : MPSTensor d D) (M₀ : ℕ)
    (hB : ∀ M, M₀ ≤ M → mpvState B M ≠ 0 ∧
      LinearMap.ker (periodicInteractionHamiltonianES h M) = ℂ ∙ mpvState B M) :
    (∃ K : ℕ, 0 < K ∧ ∀ M, 0 < M → L ≤ M →
      ∃ C : MPSTensor d K, mpvState C M ≠ 0 ∧
        LinearMap.ker (periodicInteractionHamiltonianES h M) = ℂ ∙ mpvState C M) ↔
    (∀ M, 0 < M → L ≤ M → M < M₀ →
      ∃ ψ : MPVSpace d M, ψ ≠ 0 ∧ periodicInteractionHamiltonianES h M ψ = 0 ∧
        ∀ (s : Fin M) (σ : Fin M → Fin d), ψ (fun k ↦ σ (k + s)) = ψ σ) := by
  classical
  constructor
  · rintro ⟨K, _, hK⟩ M hM hLM _
    obtain ⟨C, hC, hker⟩ := hK M hM hLM
    refine ⟨mpvState C M, hC, ?_, mpvState_cyclic_invariant C⟩
    change mpvState C M ∈ LinearMap.ker (periodicInteractionHamiltonianES h M)
    rw [hker]
    exact Submodule.mem_span_singleton_self _
  · intro hshort
    obtain ⟨K, hK, hsector⟩ := exists_uniform_bond_on_cyclic_ground_sector h hUnique B M₀ hB
    refine ⟨K, hK, ?_⟩
    intro M hM hLM
    by_cases hlong : M₀ ≤ M
    · have hzero : periodicInteractionHamiltonianES h M (mpvState B M) = 0 := by
        change mpvState B M ∈ LinearMap.ker (periodicInteractionHamiltonianES h M)
        rw [(hB M hlong).2]
        exact Submodule.mem_span_singleton_self _
      exact hsector M hM hLM (mpvState B M) (hB M hlong).1 hzero
        (mpvState_cyclic_invariant B)
    · obtain ⟨ψ, hψ, hzero, hTI⟩ := hshort M hM hLM (Nat.lt_of_not_ge hlong)
      exact hsector M hM hLM ψ hψ hzero hTI

end MPSTensor
