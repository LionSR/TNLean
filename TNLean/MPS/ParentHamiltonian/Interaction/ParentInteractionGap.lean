/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.ParentInteraction.FiniteIntervalGapComparison
import TNLean.MPS.ParentHamiltonian.Interaction.PeriodicInteraction
import QICLean.Spectral.Gap.PositiveComparisonGap
import TNLean.MPS.ParentHamiltonian.Gap.CanonicalGapAtSimultaneousInjectivity
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.CanonicalBoundedRangeGroundSpace

/-!
# Uniform gaps for fixed positive parent interactions

Every fixed positive parent interaction is comparable to the canonical parent
projection by positive constants independent of the chain length. Cyclic
translation and summation preserve the comparison and give equal periodic
kernels. Consequently the canonical gap transfers to the chosen interaction.

This is the projector reduction in CPGSV21, arXiv:2011.12127, Section IV.C,
lines 2170--2172, for the parent interactions defined at lines 1996--1999,
and supplies the gap assertion at lines 2183--2187. The interaction is fixed
before the chain length varies. For chains shorter than its range, the
periodic Hamiltonian is zero, as for the canonical interaction.

**Scope restriction (simultaneous injectivity range):**
`CPSVCanonicalFormData.exists_parentInteraction_uniform_gap_of_wordTupleSpanTop`
and `IsCPSVCanonicalForm.exists_bnt_parentInteraction_uniform_gap_of_wordTupleSpanTop`
prove the gap only at ranges \(R\geq S+1\), for a supplied \(S>0\) at which the
length-\(S\) word tuples of the normal representatives span the full product
matrix algebra (lines 2114--2129). The gap theorem at lines 2183--2187 is stated
for all parent Hamiltonians without a range hypothesis. The two comparison
theorems `IsParentInteraction.exists_pos_periodic_comparison` and
`IsParentInteraction.exists_uniform_gap_of_canonical_gap` carry no such
restriction. Documented in `docs/paper-gaps/cpgsv21_block_parent_interaction_range.tex`.

## Uniform canonical parent gaps at a bounded interaction range

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
The unrestricted assertion in arXiv:2011.12127, lines 2183--2187, fails
at some shorter ranges: a canonical tensor with three blocks has a gapless
two-site parent; see `docs/paper-gaps/cpgsv21_short_range_parent_gap.tex`.
-/

section

open scoped ComplexOrder

namespace MPSTensor

/-- A fixed positive parent interaction admits comparison constants uniform
over every periodic chain length. Source: CPGSV21, Section IV.C,
arXiv:2011.12127, lines 2170--2172. -/
theorem IsParentInteraction.exists_pos_periodic_comparison
    {d D R : ℕ} {A : MPSTensor d D}
    {h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R)}
    (hh : IsParentInteraction A R h) (hR : 0 < R) :
    ∃ κ C : ℝ, 0 < κ ∧ 0 < C ∧ ∀ N : ℕ,
      (κ : ℂ) • parentHamiltonianES A R N ≤ periodicInteractionHamiltonianES h N ∧
      periodicInteractionHamiltonianES h N ≤ (C : ℂ) • parentHamiltonianES A R N := by
  obtain ⟨κ, C, hκ, hC, hLower, hUpper⟩ := hh.exists_pos_comparison
  refine ⟨κ, C, hκ, hC, fun N ↦ ⟨?_, ?_⟩⟩
  · simpa only [periodicInteractionHamiltonianES_smul,
      periodicInteractionHamiltonianES_parentInteractionES A hR] using
      periodicInteractionHamiltonianES_mono hLower N
  · simpa only [periodicInteractionHamiltonianES_smul,
      periodicInteractionHamiltonianES_parentInteractionES A hR] using
      periodicInteractionHamiltonianES_mono hUpper N

/-- A uniform canonical gap transfers to any fixed positive parent interaction.
The constant may depend on the interaction but not on the volume.
Source: CPGSV21, Section IV.C, lines 2170--2172 and 2183--2187. -/
theorem IsParentInteraction.exists_uniform_gap_of_canonical_gap
    {d D R : ℕ} {A : MPSTensor d D}
    {h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R)}
    (hh : IsParentInteraction A R h) (hR : 0 < R) {γ : ℝ} (hγ : 0 < γ)
    (hGap : ∀ N : ℕ, ∀ v ∈ (LinearMap.ker (parentHamiltonianES A R N))ᗮ,
      γ * ‖v‖ ≤ ‖parentHamiltonianES A R N v‖) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, ∀ v ∈
      (LinearMap.ker (periodicInteractionHamiltonianES h N))ᗮ,
      δ * ‖v‖ ≤ ‖periodicInteractionHamiltonianES h N v‖ := by
  obtain ⟨κ, C, hκ, hC, hComp⟩ := hh.exists_pos_periodic_comparison hR
  refine ⟨κ * γ, mul_pos hκ hγ, fun N ↦ ?_⟩
  simpa only [div_one] using
    (parentHamiltonianES_isPositive A R N).norm_gap_of_smul_le_of_le_smul
      (periodicInteractionHamiltonianES_isPositive hh.isPositive N)
      (b := 1) hκ zero_lt_one hC hγ
      (by simpa only [Complex.ofReal_one, one_smul] using (hComp N).1)
      (by simpa only [Complex.ofReal_one, one_smul] using (hComp N).2)
      (hGap N)

/-- Every fixed positive parent interaction of a canonical tensor has a uniform
periodic gap at the supplied simultaneous injectivity range plus one.
Source: CPGSV21, Section IV.C, lines 2114--2129 and 2170--2187. -/
theorem CPSVCanonicalFormData.exists_parentInteraction_uniform_gap_of_wordTupleSpanTop
    {d D : ℕ} [NeZero d] {A : MPSTensor d D}
    (data : CPSVCanonicalFormData A) {S R : ℕ} (hS : 0 < S)
    (hSpan : WordTupleSpanTop
      (fun j ↦ data.blocks (data.representativeIndex j)) S)
    (hR : S + 1 ≤ R)
    {h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R)}
    (hh : IsParentInteraction A R h) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ N : ℕ, ∀ v ∈
      (LinearMap.ker (periodicInteractionHamiltonianES h N))ᗮ,
      γ * ‖v‖ ≤ ‖periodicInteractionHamiltonianES h N v‖ := by
  obtain ⟨γ, hγ, hGap⟩ :=
    data.exists_parentHamiltonianES_uniform_gap_of_wordTupleSpanTop hS hSpan hR
  exact hh.exists_uniform_gap_of_canonical_gap (by omega) hγ hGap

/-- One choice of normal representatives gives the uniform gap for every fixed
positive parent interaction at every admissible simultaneous injectivity range.
Source: CPGSV21, Section IV.C, lines 2114--2129 and 2170--2187. -/
theorem IsCPSVCanonicalForm.exists_bnt_parentInteraction_uniform_gap_of_wordTupleSpanTop
    {d D : ℕ} [NeZero d] {A : MPSTensor d D} (hA : IsCPSVCanonicalForm A) :
    ∃ (g : ℕ) (dim : Fin g → ℕ) (B : (j : Fin g) → MPSTensor d (dim j)),
      IsCPSVBasisOfNormalTensors A (fun j ↦ ⟨dim j, B j⟩) ∧
      ∀ {S R : ℕ}, 0 < S → WordTupleSpanTop B S → S + 1 ≤ R →
        ∀ h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R),
          IsParentInteraction A R h →
          ∃ γ : ℝ, 0 < γ ∧ ∀ N : ℕ, ∀ v ∈
            (LinearMap.ker (periodicInteractionHamiltonianES h N))ᗮ,
            γ * ‖v‖ ≤ ‖periodicInteractionHamiltonianES h N v‖ := by
  obtain ⟨g, dim, B, hB, hGap⟩ := hA.exists_bnt_uniform_gap_of_wordTupleSpanTop
  refine ⟨g, dim, B, hB, fun hS hSpan hR h hh ↦ ?_⟩
  obtain ⟨γ, hγ, hCanonical⟩ := hGap hS hSpan hR
  exact hh.exists_uniform_gap_of_canonical_gap (by omega) hγ hCanonical

end MPSTensor

end

section

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

end
