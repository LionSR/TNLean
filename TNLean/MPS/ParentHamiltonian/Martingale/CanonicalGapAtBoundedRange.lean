/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.CanonicalBoundedRangeGroundSpace
import TNLean.MPS.ParentHamiltonian.Martingale.ParentInteractionGap

/-!
# Uniform canonical parent gaps at a bounded interaction range

A canonical tensor of positive bond dimension \(D\) has a positive uniform
periodic parent-Hamiltonian gap at every interaction range \(R\geq 3D^5\).
The blocking estimate supplies a simultaneous injectivity length \(S\)
with \(S+1\leq 3D^5\), so the gap theorem requires no separate simultaneous
span assumption. The conclusion also holds for every fixed positive local
interaction with the prescribed parent kernel. The gap constant may depend
on the tensor, range, and fixed interaction, but not on the ring length.

Source: arXiv:1606.00608, lines 317--345, and arXiv:2011.12127,
Section IV.C, lines 2114--2129 and 2170--2187.

**Scope restriction (uniform interaction range):** The gap theorems here
assume the sufficient dimension estimate \(R\geq 3D^5\). The sharper
result uses \(R\geq S+1\) for the actual simultaneous injectivity length
\(S\); the bound here need not be optimal. These sufficient interaction
ranges are documented in `docs/paper-gaps/cpgsv21_block_parent_interaction_range.tex`.
The unrestricted assertion in arXiv:2011.12127, lines 2183--2187, is false
at shorter ranges; see `docs/paper-gaps/cpgsv21_short_range_parent_gap.tex`.
-/

namespace MPSTensor

variable {d D : ℕ} [NeZero d] [NeZero D]

/-- Every canonical parent Hamiltonian at interaction range
\(R\geq 3D^5\) has a positive gap uniform over the periodic chain length.
Source: arXiv:1606.00608, lines 317--345, and arXiv:2011.12127,
Section IV.C, lines 2114--2129 and 2183--2187. -/
theorem IsCPSVCanonicalForm.exists_parentHamiltonianES_uniform_gap_of_three_bondDim_pow_five_le
    {A : MPSTensor d D} (hA : IsCPSVCanonicalForm A) {R : ℕ}
    (hR : 3 * D ^ 5 ≤ R) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ N : ℕ, ∀ v ∈
      (LinearMap.ker (parentHamiltonianES A R N))ᗮ,
      γ * ‖v‖ ≤ ‖parentHamiltonianES A R N v‖ := by
  let data := Classical.choice hA
  obtain ⟨S, hS, hBound, hSpan⟩ :=
    data.exists_positive_wordTupleSpanTop_succ_le_three_bondDim_pow_five
  exact data.exists_parentHamiltonianES_uniform_gap_of_wordTupleSpanTop
    hS hSpan (hBound.trans hR)

/-- Every fixed positive parent interaction of a canonical tensor at range
\(R\geq 3D^5\) has a positive periodic gap independent of the chain length.
The constant may depend on the interaction. Source: arXiv:1606.00608,
lines 317--345, and arXiv:2011.12127, Section IV.C, lines 2170--2187. -/
theorem IsCPSVCanonicalForm.exists_parentInteraction_uniform_gap_of_three_bondDim_pow_five_le
    {A : MPSTensor d D} (hA : IsCPSVCanonicalForm A) {R : ℕ}
    (hR : 3 * D ^ 5 ≤ R)
    {h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R)}
    (hh : IsParentInteraction A R h) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ N : ℕ, ∀ v ∈
      (LinearMap.ker (periodicInteractionHamiltonianES h N))ᗮ,
      γ * ‖v‖ ≤ ‖periodicInteractionHamiltonianES h N v‖ := by
  obtain ⟨γ, hγ, hGap⟩ :=
    hA.exists_parentHamiltonianES_uniform_gap_of_three_bondDim_pow_five_le hR
  exact hh.exists_uniform_gap_of_canonical_gap
    (lt_of_lt_of_le (Nat.mul_pos (by omega) (Nat.pow_pos (NeZero.pos D))) hR) hγ hGap

end MPSTensor
