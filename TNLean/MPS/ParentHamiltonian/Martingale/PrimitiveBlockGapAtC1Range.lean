/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.PrimitiveBlockGapThreshold
import TNLean.MPS.ParentHamiltonian.PrimitiveBlockSharpOpenGroundSpace

/-!
# The parent-Hamiltonian gap at the common block-injectivity bound

For at least two inequivalent normalized primitive blocks, a common
block-injectivity length gives an explicit sufficient interaction range.
The open-chain kernel identity at that range allows comparison with an
arbitrarily long interaction already known to have a uniform gap.

## References

* PGVWC07, arXiv:quant-ph/0608197, Theorem 12 (`2blocks.2`),
  lines 1424--1454 of `MPSarchive.tex`.
* RMP, arXiv:2011.12127, Gaps subsection, lines 2183--2187 of
  `TN-Review-main.tex`.
* Nachtergaele, arXiv:cond-mat/9410110, Theorem 2.1(ii).
-/

open Filter
open scoped Topology ComplexOrder

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ} [NeZero d] [∀ j, NeZero (dim j)]

/-- The primitive-block parent Hamiltonian has a uniform periodic gap at every
range above the three-block bound determined by a common injectivity length,
as in PGVWC07, Theorem 12 (`2blocks.2`). The gap conclusion is stated in
arXiv:2011.12127, Gaps subsection, lines 2183--2187. -/
theorem exists_hamiltonian_parentRingInteraction_toTensorFromBlocks_gap_of_threeBlock_bound
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, Kraus.HasComplementaryFixedPointGap (A j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : dim j = dim i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i))
    {L₀ R : ℕ} (hL₀ : 0 < L₀) (hBlk : ∀ j, Kraus.IsNBlkInjective (A j) L₀)
    (hr : 2 ≤ r) (hR : 3 * (r - 1) * (L₀ + 1) + 1 ≤ R) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ N : ℕ in atTop, ∀ [NeZero N], ∀ z : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin
        (parentRingInteraction (toTensorFromBlocks (d := d) (μ := μ) A) R N).hamiltonian) z →
        z = 0 ∨ (γ : ℂ) ≤ z := by
  exact exists_hamiltonian_parentRingInteraction_toTensorFromBlocks_gap_of_ker_eq
    μ A hμ ρ hP hρ hDistinct (by omega) fun _ hW ↦
      ker_hamiltonian_parentChainInteraction_toTensorFromBlocks_eq_of_threeBlock_bound
        μ A hμ ρ hP hρ hDistinct hL₀ hBlk hr hR hW

end MPSTensor
