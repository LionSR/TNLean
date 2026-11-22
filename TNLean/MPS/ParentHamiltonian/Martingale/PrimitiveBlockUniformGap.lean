/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.PrimitiveBlockGapAtC1Range

/-!
# A block-injective parent-Hamiltonian gap uniform in all lengths

The eventual gap at the explicit common block-injectivity range extends to
all finite chain lengths. Each of the finitely many excluded Hamiltonians
has a positive lower norm bound on the orthogonal complement of its kernel;
taking a finite minimum gives one positive constant for the whole family.

This is the uniform-in-length conclusion in arXiv:2011.12127, Gaps subsection,
lines 2183--2187, at the range in PGVWC07, Theorem 12 (`2blocks.2`).
-/

open Filter
open scoped Topology ComplexOrder

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ} [NeZero d] [∀ j, NeZero (dim j)]

/-- Primitive inequivalent blocks with a common injectivity length have a
positive parent-Hamiltonian gap uniform over every finite chain length, at
each range satisfying PGVWC07, Theorem 12 (`2blocks.2`). -/
theorem exists_hamiltonian_parentRingInteraction_toTensorFromBlocks_uniform_gap_of_threeBlock_bound
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, Kraus.HasComplementaryFixedPointGap (A j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : dim j = dim i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i))
    {L₀ R : ℕ} (hL₀ : 0 < L₀) (hBlk : ∀ j, Kraus.IsNBlkInjective (A j) L₀)
    (hr : 2 ≤ r) (hR : 3 * (r - 1) * (L₀ + 1) + 1 ≤ R) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (N : ℕ) [NeZero N], ∀ z : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin
        (parentRingInteraction (toTensorFromBlocks (d := d) (μ := μ) A) R N).hamiltonian) z →
        z = 0 ∨ (γ : ℂ) ≤ z := by
  exact exists_hamiltonian_parentRingInteraction_toTensorFromBlocks_uniform_gap_of_ker_eq
    μ A hμ ρ hP hρ hDistinct (by omega) fun _ hW ↦
      ker_hamiltonian_parentChainInteraction_toTensorFromBlocks_eq_of_threeBlock_bound
        μ A hμ ρ hP hρ hDistinct hL₀ hBlk hr hR hW

end MPSTensor
