/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.SharedInfra.BlockAssembly
import TNLean.MPS.FundamentalTheorem.Arbitrary.Corollaries.BlockPermutation
import TNLean.MPS.FundamentalTheorem.Arbitrary.Corollaries.GaugeConversions
import TNLean.MPS.FundamentalTheorem.Arbitrary.Corollaries.WeightedSums

/-!
# Block sums with the same states are gauge equivalent

Let `X` and `Y` be tensors of bond dimension `D`, each gauge related to a block sum
`⨁_k μ_k C_k` with nonzero complex weights and irreducible blocks that have a nonzero letter. If
`X` and `Y` have the same states, they are gauge equivalent.

This contains the case of the irreducible form of arXiv:1708.00029 (Section 2.1, equation
`eq:irreducible-form`, lines 249–253, and the definition at lines 260–262), where the tensor is
such a block sum, the weights are positive and the transfer maps have spectral radius one; the
equality of the bond dimensions is part of the statement here. The relation
`Z A^i = Y B^i Y⁻¹`, `[A^i, Z] = 0` of `thm:bdequal` (lines 643–656) then holds with `Z = 1`; the
blockwise structure of `Z` in that theorem is not stated here.

## Main results

* `MPSTensor.gaugeEquiv_of_sameMPV_of_isGaugeRelated_toTensorFromBlocks`.

## References

* De las Cuevas, Cirac, Schuch, Pérez-García, arXiv:1708.00029, Definition (Irreducible form),
  lines 249–262, and `thm:bdequal`, lines 643–656.
-/

namespace MPSTensor

variable {d D : ℕ}

/-- **Block sums with the same states are gauge equivalent.** Let `X` be gauge related to
`⨁_k μ_k C_k` and `Y` to `⨁_l μ'_l C'_l`, with nonzero weights and irreducible blocks that have a
nonzero letter. If `X` and `Y` have the same states, they are gauge equivalent: the weighted
blocks are gauge related along a bijection of the block indices, hence so are the block sums. -/
theorem gaugeEquiv_of_sameMPV_of_isGaugeRelated_toTensorFromBlocks {r r' : ℕ} {dim : Fin r → ℕ}
    {dim' : Fin r' → ℕ} {blocks : ∀ k, MPSTensor d (dim k)} {blocks' : ∀ k, MPSTensor d (dim' k)}
    {μ : Fin r → ℂ} {μ' : Fin r' → ℂ} {X Y : MPSTensor d D}
    (hμ : ∀ k, μ k ≠ 0) (hμ' : ∀ k, μ' k ≠ 0)
    (hirr : ∀ k, Matrix.IsIrreducibleAction (blocks k)) (hlet : ∀ k, ∃ i, blocks k i ≠ 0)
    (hirr' : ∀ k, Matrix.IsIrreducibleAction (blocks' k)) (hlet' : ∀ k, ∃ i, blocks' k i ≠ 0)
    (hX : IsGaugeRelated (toTensorFromBlocks μ blocks) X)
    (hY : IsGaugeRelated (toTensorFromBlocks μ' blocks') Y) (h : SameMPV X Y) :
    GaugeEquiv X Y := by
  have hsum : ∀ N, 0 < N → ∀ σ : Fin N → Fin d,
      ∑ k, μ k ^ N * mpv (blocks k) σ = ∑ k, μ' k ^ N * mpv (blocks' k) σ := by
    intro N hN σ
    have e1 := hX.sameMPV₂Pos N hN σ
    have e2 := hY.sameMPV₂Pos N hN σ
    rw [mpv_toTensorFromBlocks_eq_sum] at e1 e2
    simp only [smul_eq_mul] at e1 e2
    rw [e1, e2]
    exact h N σ
  obtain ⟨τ, hτ⟩ := (forall_sum_pow_mul_mpv_eq_iff_exists_equiv_isGaugeRelated hirr hlet hirr'
    hlet' hμ hμ').1 hsum
  exact isGaugeRelated_iff_gaugeEquiv.1
    ((hX.symm.trans (isGaugeRelated_toTensorFromBlocks_of_equiv τ hτ)).trans hY)

end MPSTensor
