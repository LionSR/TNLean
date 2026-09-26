/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.PrimitiveBlockGap
import TNLean.MPS.ParentHamiltonian.Martingale.FixedRangeGapTransfer

/-!
# Uniform gaps above an interaction threshold for primitive block sums

Every sufficiently long parent interaction of a finite family of inequivalent
normalized primitive tensors has a positive periodic gap, uniformly in the
chain length. The threshold is the open-chain kernel threshold. A comparison
on one longer interval transfers the gap from a constructed interaction range
to each prescribed range above this threshold.

## References

* Nachtergaele, arXiv:cond-mat/9410110, Theorem 2.1(ii), and Section 3,
  equations (3.12)--(3.16).
-/

open Filter
open scoped Topology ComplexOrder

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ} [NeZero d] [∀ j, NeZero (dim j)]

/-- Every interaction range above a fixed threshold gives a uniformly gapped
periodic parent Hamiltonian for a direct sum of inequivalent normalized
primitive blocks. The gap constant may depend on the interaction range.
This is the fixed-interaction consequence of Nachtergaele's Theorem 2.1(ii),
arXiv:cond-mat/9410110, with the open kernels of Section 3. -/
theorem exists_parentHamiltonianES_toTensorFromBlocks_gap_threshold_of_isPrimitiveMPS
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, IsPrimitiveMPS (A j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : dim j = dim i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i)) :
    ∃ R₀ : ℕ, 0 < R₀ ∧ ∀ R : ℕ, R₀ ≤ R → ∃ γ : ℝ, 0 < γ ∧
      ∀ᶠ N : ℕ in atTop, ∀ v ∈
        (LinearMap.ker (parentHamiltonianES
          (toTensorFromBlocks (d := d) (μ := μ) A) R N))ᗮ,
        γ * ‖v‖ ≤ ‖parentHamiltonianES
          (toTensorFromBlocks (d := d) (μ := μ) A) R N v‖ := by
  obtain ⟨R₀, hR₀, hKernel⟩ :=
    exists_ker_openParentHamiltonianES_toTensorFromBlocks_eq_groundSpaceES_of_isPrimitiveMPS
      μ A hμ ρ hP hρ hDistinct
  refine ⟨R₀, hR₀, fun R hR ↦ ?_⟩
  obtain ⟨W, hRW, _, γ, hγ, hGap⟩ :=
    exists_ge_parentHamiltonianES_toTensorFromBlocks_gap_of_isPrimitiveMPS
      μ A hμ ρ hP hρ hDistinct (2 * R)
  exact exists_parentHamiltonianES_gap_of_larger_range
    (toTensorFromBlocks (d := d) (μ := μ) A) (hR₀.trans_le hR) hRW
    (hKernel R W hR (by omega)) hγ hGap

end MPSTensor
