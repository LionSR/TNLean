/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.PrimitiveBlockGap
import TNLean.MPS.ParentHamiltonian.Martingale.FixedRangeGapTransfer
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
theorem exists_parentHamiltonianES_toTensorFromBlocks_gap_of_isPrimitiveMPS_of_threeBlock_bound
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, IsPrimitiveMPS (A j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : dim j = dim i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i))
    {L₀ R : ℕ} (hL₀ : 0 < L₀) (hBlk : ∀ j, Kraus.IsNBlkInjective (A j) L₀)
    (hr : 2 ≤ r) (hR : 3 * (r - 1) * (L₀ + 1) + 1 ≤ R) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ N : ℕ in atTop, ∀ v ∈
      (LinearMap.ker (parentHamiltonianES
        (toTensorFromBlocks (d := d) (μ := μ) A) R N))ᗮ,
      γ * ‖v‖ ≤ ‖parentHamiltonianES
        (toTensorFromBlocks (d := d) (μ := μ) A) R N v‖ := by
  obtain ⟨W, hRW, _, γ, hγ, hGap⟩ :=
    exists_ge_parentHamiltonianES_toTensorFromBlocks_gap_of_isPrimitiveMPS
      μ A hμ ρ hP hρ hDistinct (2 * R)
  exact exists_parentHamiltonianES_gap_of_larger_range
    (toTensorFromBlocks (d := d) (μ := μ) A) (by omega) hRW
    (ker_openParentHamiltonianES_toTensorFromBlocks_eq_groundSpaceES_of_threeBlock_bound
      μ A hμ ρ hP hρ hDistinct hL₀ hBlk hr hR (by omega)) hγ hGap

end MPSTensor
