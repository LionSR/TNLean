/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.BlockDiagonalNormalization
import TNLean.MPS.ParentHamiltonian.Gap.PrimitiveBlockGapThreshold

/-!
# A spectral gap for a parent Hamiltonian of normal blocks

A weighted direct sum of pairwise inequivalent normal blocks has a uniform
periodic gap at every interaction range in the PGVWC07 bound, over all chain
lengths.
Independent normalization of the blocks preserves the parent
Hamiltonian exactly, so the primitive block estimate applies unchanged.

This is a construction within the block-injective case of the gap theorem
in Cirac--Pérez-García--Schuch--Verstraete, arXiv:2011.12127, Section IV.C,
lines 2183--2187, following Nachtergaele, arXiv:cond-mat/9410110, Section 6.

The prescribed C1 interaction bound is retained by the final theorem below.
The range comparison and preservation of the C1 length are documented in
`docs/paper-gaps/cpgsv21_block_parent_interaction_range.tex`.
-/

open MPTensor

open Filter
open scoped Topology ComplexOrder

namespace MPSTensor

variable {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ} {dim : Fin r → ℕ} [Nonempty α] [∀ j, NeZero (dim j)]

/-- A direct sum of inequivalent normal blocks has a canonical parent
interaction of positive range whose periodic Hamiltonians have a uniform
positive gap at all sufficiently large volumes. The interaction range is
chosen sufficiently large in this block-injective case of Cirac--Pérez-García--Schuch--Verstraete,
arXiv:2011.12127, Section IV.C, lines 2183--2187. -/
theorem exists_hamiltonian_parentRingInteraction_toTensorFromBlocks_gap_of_isNormal
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPTensor α (Fin (dim j)))
    (hμ : ∀ j, μ j ≠ 0) (hNormal : ∀ j, Kraus.IsNormal (A j))
    (hDistinct : ∀ i j, i ≠ j → ∀ h : dim j = dim i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i)) :
    ∃ R : ℕ, 0 < R ∧ ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ N : ℕ in atTop, ∀ [NeZero N],
      ∀ z : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin
          (parentRingInteraction (toTensorFromBlocks (μ := μ) A) R N).hamiltonian) z →
          z = 0 ∨ (γ : ℂ) ≤ z := by
  obtain ⟨B, ρ, hP, hρ, hDistinctB, hEq⟩ :=
    exists_hasComplementaryFixedPointGap_family_hamiltonian_eq_of_isNormal
      μ A hμ hNormal hDistinct
  simpa only [hEq] using
    exists_hamiltonian_parentRingInteraction_toTensorFromBlocks_gap_of_fixedPointGap
      μ B hμ ρ hP hρ hDistinctB

/-- Beyond one finite interaction threshold, every parent Hamiltonian of the
normal block sum has a uniform eventual periodic gap. The threshold does not
depend on the chosen interaction range. -/
theorem exists_hamiltonian_parentRingInteraction_toTensorFromBlocks_gap_threshold_of_isNormal
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPTensor α (Fin (dim j)))
    (hμ : ∀ j, μ j ≠ 0) (hNormal : ∀ j, Kraus.IsNormal (A j))
    (hDistinct : ∀ i j, i ≠ j → ∀ h : dim j = dim i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i)) :
    ∃ R₀ : ℕ, 0 < R₀ ∧ ∀ R : ℕ, R₀ ≤ R →
      ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ N : ℕ in atTop, ∀ [NeZero N], ∀ z : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin
          (parentRingInteraction (toTensorFromBlocks (μ := μ) A) R N).hamiltonian) z →
          z = 0 ∨ (γ : ℂ) ≤ z := by
  obtain ⟨B, ρ, hP, hρ, hDistinctB, hEq⟩ :=
    exists_hasComplementaryFixedPointGap_family_hamiltonian_eq_of_isNormal
      μ A hμ hNormal hDistinct
  simpa only [hEq] using
    exists_hamiltonian_parentRingInteraction_toTensorFromBlocks_gap_threshold_of_fixedPointGap
      μ B hμ ρ hP hρ hDistinctB

/-- The parent-Hamiltonian gap at the prescribed C1 interaction range is
uniform over every chain length. This is the block-injective gap assertion of
CPGSV21, arXiv:2011.12127, Section IV.C, lines 2183--2187, at the admissible
range in PGVWC07, Theorem 12, lines 1424--1458. -/
theorem exists_hamiltonian_parentRingInteraction_toTensorFromBlocks_uniform_gap_of_isNBlkInjective
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPTensor α (Fin (dim j)))
    (hμ : ∀ j, μ j ≠ 0)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : dim j = dim i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i))
    {L₀ R : ℕ} (hL₀ : 0 < L₀)
    (hBlk : ∀ j, Kraus.IsNBlkInjective (A j) L₀) (hr : 2 ≤ r)
    (hR : 3 * (r - 1) * (L₀ + 1) + 1 ≤ R) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (N : ℕ) [NeZero N], ∀ z : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin
        (parentRingInteraction (toTensorFromBlocks (μ := μ) A) R N).hamiltonian) z →
        z = 0 ∨ (γ : ℂ) ≤ z := by
  obtain ⟨B, ρ, hP, hρ, hBlkB, hDistinctB, hEq⟩ :=
    exists_hasComplementaryFixedPointGap_family_hamiltonian_eq_of_common_isNBlkInjective
      μ A hμ hL₀ hBlk hDistinct
  simpa only [hEq] using
    exists_hamiltonian_parentRingInteraction_toTensorFromBlocks_uniform_gap_of_threeBlock_bound
      μ B hμ ρ hP hρ hDistinctB hL₀ hBlkB hr hR

end MPSTensor
