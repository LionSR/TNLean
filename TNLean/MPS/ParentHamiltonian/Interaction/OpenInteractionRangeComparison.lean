/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Gap.Comparison.PeriodicRangeComparison
import QICLean.Spectral.Gap.PositiveComparisonGap
import QICLean.ManyBody.Hamiltonian.KernelGap
import QICLean.ManyBody.Hamiltonian.LocalTermTranslates
import TNLean.MPS.ParentHamiltonian.ParentInteraction.OpenHamiltonian
import TNLean.MPS.ParentHamiltonian.Gap.Comparison.OpenRangeComparison

/-!
# Transfer of canonical gaps to a positive interaction

Suppose the canonical parent Hamiltonians have exact MPS boundary kernels
and uniform gaps at every sufficiently large interaction range. Any positive
interaction whose open kernels eventually agree with those same spaces then
has one positive gap at every volume: every nonzero eigenvalue is at least it.

On one sufficiently long interval, finite dimensionality supplies a positive
multiple of the canonical excitation projection below the given Hamiltonian.
The interval comparison extends to larger chains with the usual window
multiplicity. The finitely many shorter chains require only their individual
finite-dimensional gaps. No relation between the given local kernel and the
MPS space at its interaction range is assumed.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2,
lines 933--947, condition C1, and Section 6, lines 2593--2675.

The transfer is stated for the open-chain translates of a local matrix
(`ManyBody.Interaction.chainTranslates`) and the parent interaction on the open chain.
-/

open Filter
open scoped Topology ComplexOrder
namespace MPSTensor
variable {d D : ℕ}

section Interaction

open ManyBody.Interaction (chainTranslates posSemidef_hamiltonian_chainTranslates)

/-- Uniform canonical gaps at all sufficiently large ranges transfer to the open-chain translates
of any positive semidefinite local matrix whose open kernels eventually equal the same MPS
boundary spaces. The gaps are stated above the kernels: every eigenvalue is `0` or at least the
gap. The conclusion holds at every volume above the actual kernel; neither a local
parent-kernel identity nor an injectivity hypothesis is required. Source: Nachtergaele,
arXiv:cond-mat/9410110, Theorem 1.2, lines 933--947, condition C1, lines 1030--1041, and
Section 6, lines 2593--2675. This is a generic finite-window criterion; canonical gaps are
explicit inputs. -/
theorem exists_toEuclideanLin_hamiltonian_chainTranslates_gap_of_canonical_gaps_of_eventual_kernel
    (A : MPSTensor d D) {R₀ : ℕ} (_hR₀ : 0 < R₀)
    (hCanonical : ∀ W, R₀ ≤ W →
      (∀ N, W ≤ N → LinearMap.ker (Matrix.toEuclideanLin
        (parentChainInteraction A W N).hamiltonian) = groundSpaceES A N) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ N, ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (parentChainInteraction A W N).hamiltonian) μ →
          μ = 0 ∨ (δ : ℂ) ≤ μ)
    {R : ℕ} (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hh : h.PosSemidef)
    (hKernel : ∀ᶠ N : ℕ in atTop,
      LinearMap.ker (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) =
        groundSpaceES A N) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ N, ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) μ → μ = 0 ∨ (γ : ℂ) ≤ μ := by
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hKernel
  let W := max R (max N₀ R₀)
  have hBounds : R ≤ W ∧ N₀ ≤ W ∧ R₀ ≤ W := by omega
  obtain ⟨hCanonicalKernel, δ, hδ, hCanonicalGap⟩ := hCanonical W hBounds.2.2
  obtain ⟨κ, hκ, hLocal⟩ :=
    LinearMap.IsPositive.exists_pos_smul_orthogonal_ker_projection_le
      (Matrix.isPositive_toEuclideanLin_iff.mpr (posSemidef_hamiltonian_chainTranslates hh W))
  rw [hN₀ W hBounds.2.1, ← toEuclideanLin_toMatrix'_parentInteraction, ← map_smul,
    Matrix.toEuclideanLin_le_toEuclideanLin_iff] at hLocal
  refine Nat.exists_pos_forall_of_eventually
    (P := fun N γ => ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) μ → μ = 0 ∨ (γ : ℂ) ≤ μ)
    (fun N γ η hle hgap => ManyBody.forall_hasEigenvalue_mono hle hgap)
    (fun N => ManyBody.exists_pos_forall_hasEigenvalue
      (posSemidef_hamiltonian_chainTranslates hh N))
    (M := W) (δ := κ * δ / (W - R + 1 : ℕ))
    (div_pos (mul_pos hκ hδ) (Nat.cast_pos.mpr (by omega))) ?_
  intro N hN
  exact toEuclideanLin_hamiltonian_chainTranslates_gap_of_long_gap_at_length
    A h hh hBounds.1 hκ hLocal
    (hN₀ N (hBounds.2.1.trans hN)) (hCanonicalKernel N hN) (hCanonicalGap N)

end Interaction

end MPSTensor
