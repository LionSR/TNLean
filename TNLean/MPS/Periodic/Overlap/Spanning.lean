/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.SharedInfra.SectorDecomposition

/-!
# Spanning by the nonzero vectors of a sector decomposition

The multiplicity expansion expresses the state of a sector decomposition as
a linear combination of its basis-block states. Removing zero vectors does
not change this conclusion. This proves the spanning clause of
arXiv:1708.00029, Proposition 3.3, lines 604--608, at every chain length.
No periodicity or normalization assumption is needed for this clause.
-/

open scoped BigOperators
namespace MPSTensor

variable {d : ℕ}

/-- The state of an assembled tensor belongs to the span of its nonzero
basis-block states at every length.

Source: arXiv:1708.00029, Proposition 3.3, lines 604--608. The coefficients are
the sums of the length-th powers of the multiplicity entries. -/
theorem SectorDecomposition.mpvState_mem_span_nonzero (P : SectorDecomposition d) (N : ℕ) :
    mpvState P.toTensor N ∈ Submodule.span ℂ
      (Set.range (fun j : {j : Fin P.basisCount // mpvState (P.basis j) N ≠ 0} =>
        mpvState (P.basis j) N)) := by
  rw [P.mpvState_toTensor_eq_sum_coeff]
  refine Submodule.sum_mem _ fun j _ => ?_
  by_cases h : mpvState (P.basis j) N = 0
  · simp [h]
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, h⟩, rfl⟩)

end MPSTensor
