/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.ParentInteractionComparison
import TNLean.MPS.ParentHamiltonian.Martingale.PeriodicInteraction
import TNLean.MPS.ParentHamiltonian.Martingale.PositiveComparisonGap
import TNLean.MPS.ParentHamiltonian.Martingale.CanonicalGapAtSimultaneousInjectivity

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
-/

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
