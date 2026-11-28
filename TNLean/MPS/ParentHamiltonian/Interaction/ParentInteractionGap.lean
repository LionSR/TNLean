/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.ParentInteraction.OpenHamiltonian
import TNLean.MPS.ParentHamiltonian.Gap.Comparison.PeriodicRangeComparison
import QICLean.ManyBody.Hamiltonian.KernelGap
import QICLean.ManyBody.Hamiltonian.LocalTermTranslates
import QICLean.Spectral.Gap.PositiveComparisonGap
import TNLean.MPS.ParentHamiltonian.Gap.CanonicalGapAtSimultaneousInjectivity
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.CanonicalBoundedRangeGroundSpace
import TNLean.MPS.ParentHamiltonian.Gap.Comparison.OpenRangeComparison

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

It also contains the following results.

* `exists_toEuclideanLin_hamiltonian_chainTranslates_gap_of_canonical_gaps_of_eventual_kernel`
  (in `MPSTensor`):
  transfer of canonical gaps to a positive interaction.
-/

open MPTensor

section ParentInteractionGap

section

open scoped ComplexOrder MatrixOrder

namespace MPSTensor

/-- A fixed positive parent interaction admits comparison constants uniform
over every ring: its Hamiltonian is bounded below and above by multiples of the Hamiltonian of
the canonical parent interaction. Source: CPGSV21, Section IV.C,
arXiv:2011.12127, lines 2170--2172. -/
theorem IsParentInteraction.exists_pos_periodic_comparison
    {d D R : ℕ} {A : MPTensor α (Fin D)} {h : Matrix (Fin R → α) (Fin R → α) ℂ}
    (hh : IsParentInteraction A R (Matrix.toEuclideanLin h)) :
    ∃ κ C : ℝ, 0 < κ ∧ 0 < C ∧ ∀ (N : ℕ) [NeZero N],
      (κ : ℂ) • (parentRingInteraction A R N).hamiltonian ≤
          (ManyBody.Interaction.translationInvariant N h).hamiltonian ∧
        (ManyBody.Interaction.translationInvariant N h).hamiltonian ≤
          (C : ℂ) • (parentRingInteraction A R N).hamiltonian := by
  obtain ⟨κ, C, hκ, hC, hLower, hUpper⟩ :=
    hh.exists_pos_comparison_toEuclideanLin_toMatrix'_parentInteraction
  rw [← map_smul, Matrix.toEuclideanLin_le_toEuclideanLin_iff] at hLower hUpper
  refine ⟨κ, C, hκ, hC, fun N _ ↦ ⟨?_, ?_⟩⟩
  · rw [← ManyBody.Interaction.hamiltonian_translationInvariant_smul]
    exact ManyBody.Interaction.hamiltonian_translationInvariant_mono hLower
  · rw [← ManyBody.Interaction.hamiltonian_translationInvariant_smul]
    exact ManyBody.Interaction.hamiltonian_translationInvariant_mono hUpper

/-- A uniform gap of the canonical parent Hamiltonians transfers to any fixed positive parent
interaction: every eigenvalue other than zero of its Hamiltonian on a ring is at least a
constant that may depend on the interaction but not on the volume.
Source: CPGSV21, Section IV.C, lines 2170--2172 and 2183--2187. -/
theorem IsParentInteraction.exists_uniform_gap_of_canonical_gap
    {d D R : ℕ} {A : MPTensor α (Fin D)} {h : Matrix (Fin R → α) (Fin R → α) ℂ}
    (hh : IsParentInteraction A R (Matrix.toEuclideanLin h)) {γ : ℝ} (hγ : 0 < γ)
    (hGap : ∀ (N : ℕ) [NeZero N], ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentRingInteraction A R N).hamiltonian) μ →
        μ = 0 ∨ (γ : ℂ) ≤ μ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (N : ℕ) [NeZero N], ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (ManyBody.Interaction.translationInvariant N h).hamiltonian) μ →
        μ = 0 ∨ (δ : ℂ) ≤ μ := by
  obtain ⟨κ, C, hκ, hC, hComp⟩ := hh.exists_pos_periodic_comparison
  exact ⟨κ * γ, mul_pos hκ hγ, fun N _ ↦
    ManyBody.forall_hasEigenvalue_of_smul_le_of_le_smul
      (posSemidef_hamiltonian_parentRingInteraction A R N)
      (ManyBody.Interaction.posSemidef_hamiltonian_translationInvariant
        (Matrix.isPositive_toEuclideanLin_iff.mp hh.isPositive))
      hκ hC hγ (hComp N).1 (hComp N).2 (hGap N)⟩

/-- Every fixed positive parent interaction of a canonical tensor has a uniform
gap on the rings at the supplied simultaneous injectivity range plus one.
Source: CPGSV21, Section IV.C, lines 2114--2129 and 2170--2187. -/
theorem
    _root_.MPTensor.CPSVCanonicalFormData.exists_parentInteraction_uniform_gap_of_wordTupleSpanTop
    {d D : ℕ} [Nonempty α] {A : MPTensor α (Fin D)}
    (data : CPSVCanonicalFormData A) {S R : ℕ} (hS : 0 < S)
    (hSpan : WordTupleSpanTop
      (fun j ↦ data.blocks (data.representativeIndex j)) S)
    (hR : S + 1 ≤ R)
    {h : Matrix (Fin R → α) (Fin R → α) ℂ}
    (hh : IsParentInteraction A R (Matrix.toEuclideanLin h)) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (N : ℕ) [NeZero N], ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (ManyBody.Interaction.translationInvariant N h).hamiltonian) μ →
        μ = 0 ∨ (γ : ℂ) ≤ μ := by
  obtain ⟨γ, hγ, hGap⟩ :=
    data.exists_parentRingInteraction_uniform_gap_of_wordTupleSpanTop hS hSpan hR
  exact hh.exists_uniform_gap_of_canonical_gap hγ hGap

/-- One choice of normal representatives gives the uniform gap for every fixed
positive parent interaction at every admissible simultaneous injectivity range.
Source: CPGSV21, Section IV.C, lines 2114--2129 and 2170--2187. -/
theorem
    _root_.MPTensor.IsCPSVCanonicalForm.exists_bnt_parentInteraction_uniform_gap_of_wordTupleSpanTop
    {d D : ℕ} [Nonempty α] {A : MPTensor α (Fin D)} (hA : IsCPSVCanonicalForm A) :
    ∃ (g : ℕ) (dim : Fin g → ℕ) (B : (j : Fin g) → MPTensor α (Fin (dim j))),
      IsCPSVBasisOfNormalTensors A (fun j ↦ ⟨dim j, B j⟩) ∧
      ∀ {S R : ℕ}, 0 < S → WordTupleSpanTop B S → S + 1 ≤ R →
        ∀ h : Matrix (Fin R → α) (Fin R → α) ℂ,
          IsParentInteraction A R (Matrix.toEuclideanLin h) →
          ∃ γ : ℝ, 0 < γ ∧ ∀ (N : ℕ) [NeZero N], ∀ μ : ℂ, Module.End.HasEigenvalue
            (Matrix.toEuclideanLin
              (ManyBody.Interaction.translationInvariant N h).hamiltonian) μ →
              μ = 0 ∨ (γ : ℂ) ≤ μ := by
  obtain ⟨g, dim, B, hB, hGap⟩ := hA.exists_bnt_uniform_gap_of_wordTupleSpanTop
  refine ⟨g, dim, B, hB, fun hS hSpan hR h hh ↦ ?_⟩
  obtain ⟨γ, hγ, hCanonical⟩ := hGap hS hSpan hR
  exact hh.exists_uniform_gap_of_canonical_gap hγ hCanonical

end MPSTensor

end

section

open scoped ComplexOrder

namespace MPSTensor

variable {α : Type*} [Fintype α] [DecidableEq α] {D : ℕ} [Nonempty α] [NeZero D]

set_option linter.style.longLine false in
/-- Every canonical parent Hamiltonian at interaction range
\(R\geq 3D^5\) has a positive gap uniform over the periodic chain length.
Source: arXiv:1606.00608, lines 317--345, and arXiv:2011.12127,
Section IV.C, lines 2114--2129 and 2183--2187. -/
theorem
    _root_.MPTensor.IsCPSVCanonicalForm.exists_parentRingInteraction_uniform_gap_of_three_bondDim_pow_five_le
    {A : MPTensor α (Fin D)} (hA : IsCPSVCanonicalForm A) {R : ℕ}
    (hR : 3 * D ^ 5 ≤ R) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (N : ℕ) [NeZero N], ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentRingInteraction A R N).hamiltonian) μ →
        μ = 0 ∨ (γ : ℂ) ≤ μ := by
  let data := Classical.choice hA
  obtain ⟨S, hS, hBound, hSpan⟩ :=
    data.exists_positive_wordTupleSpanTop_succ_le_three_bondDim_pow_five
  exact data.exists_parentRingInteraction_uniform_gap_of_wordTupleSpanTop
    hS hSpan (hBound.trans hR)

set_option linter.style.longLine false in
/-- Every fixed positive parent interaction of a canonical tensor at range
\(R\geq 3D^5\) has a positive periodic gap independent of the chain length.
The constant may depend on the interaction. Source: arXiv:1606.00608,
lines 317--345, and arXiv:2011.12127, Section IV.C, lines 2170--2187. -/
theorem
    _root_.MPTensor.IsCPSVCanonicalForm.exists_parentInteraction_uniform_gap_of_three_bondDim_pow_five_le
    {A : MPTensor α (Fin D)} (hA : IsCPSVCanonicalForm A) {R : ℕ}
    (hR : 3 * D ^ 5 ≤ R)
    {h : Matrix (Fin R → α) (Fin R → α) ℂ}
    (hh : IsParentInteraction A R (Matrix.toEuclideanLin h)) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (N : ℕ) [NeZero N], ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (ManyBody.Interaction.translationInvariant N h).hamiltonian) μ →
        μ = 0 ∨ (γ : ℂ) ≤ μ := by
  obtain ⟨γ, hγ, hGap⟩ :=
    hA.exists_parentRingInteraction_uniform_gap_of_three_bondDim_pow_five_le hR
  exact hh.exists_uniform_gap_of_canonical_gap hγ hGap

end MPSTensor

end

end ParentInteractionGap

section OpenInteractionRangeComparison

/-!
## Transfer of canonical gaps to a positive interaction

Suppose the canonical parent Hamiltonians have exact MPS boundary kernels
and uniform gaps at every sufficiently large interaction range. Any positive
interaction whose open kernels eventually agree with those same spaces then
has one positive gap at every volume: every nonzero eigenvalue is at least it.

On one sufficiently long interval, finite dimensionality supplies a positive
multiple of the canonical excitation projection below the given Hamiltonian.
The interval comparison extends to larger chains with the usual window
multiplicity. The finitely many shorter chains require only their individual
finite-dimensional gaps. No relation between the given local kernel and the
MPS space at its interaction range is assumed.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2,
lines 933--947, condition C1, and Section 6, lines 2593--2675.

The transfer is stated for the open-chain translates of a local matrix
(`ManyBody.Interaction.chainTranslates`) and the parent interaction on the open chain.
-/

open Filter
open scoped Topology ComplexOrder
namespace MPSTensor
variable {α : Type*} [Fintype α] [DecidableEq α] {D : ℕ}

section Interaction

open ManyBody.Interaction (chainTranslates posSemidef_hamiltonian_chainTranslates)

/-- Uniform canonical gaps at all sufficiently large ranges transfer to the open-chain translates
of any positive semidefinite local matrix whose open kernels eventually equal the same MPS
boundary spaces. The gaps are stated above the kernels: every eigenvalue is `0` or at least the
gap. The conclusion holds at every volume above the actual kernel; neither a local
parent-kernel identity nor an injectivity hypothesis is required. Source: Nachtergaele,
arXiv:cond-mat/9410110, Theorem 1.2, lines 933--947, condition C1, lines 1030--1041, and
Section 6, lines 2593--2675. This is a generic finite-window criterion; canonical gaps are
explicit inputs. -/
theorem exists_toEuclideanLin_hamiltonian_chainTranslates_gap_of_canonical_gaps_of_eventual_kernel
    (A : MPTensor α (Fin D)) {R₀ : ℕ} (_hR₀ : 0 < R₀)
    (hCanonical : ∀ W, R₀ ≤ W →
      (∀ N, W ≤ N → LinearMap.ker (Matrix.toEuclideanLin
        (parentChainInteraction A W N).hamiltonian) = ((groundSpace A N).map (WithLp.linearEquiv 2 ℂ
            _).symm.toLinearMap)) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ N, ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (parentChainInteraction A W N).hamiltonian) μ →
          μ = 0 ∨ (δ : ℂ) ≤ μ)
    {R : ℕ} (h : Matrix (Fin R → α) (Fin R → α) ℂ) (hh : h.PosSemidef)
    (hKernel : ∀ᶠ N : ℕ in atTop,
      LinearMap.ker (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) =
        ((groundSpace A N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ N, ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) μ → μ = 0 ∨ (γ : ℂ) ≤ μ := by
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hKernel
  let W := max R (max N₀ R₀)
  have hBounds : R ≤ W ∧ N₀ ≤ W ∧ R₀ ≤ W := by omega
  obtain ⟨hCanonicalKernel, δ, hδ, hCanonicalGap⟩ := hCanonical W hBounds.2.2
  obtain ⟨κ, hκ, hLocal⟩ :=
    LinearMap.IsPositive.exists_pos_smul_orthogonal_ker_projection_le
      (Matrix.isPositive_toEuclideanLin_iff.mpr (posSemidef_hamiltonian_chainTranslates hh W))
  rw [hN₀ W hBounds.2.1, ← toEuclideanLin_toMatrix'_parentInteraction, ← map_smul,
    Matrix.toEuclideanLin_le_toEuclideanLin_iff] at hLocal
  refine Nat.exists_pos_forall_of_eventually
    (P := fun N γ => ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) μ → μ = 0 ∨ (γ : ℂ) ≤ μ)
    (fun N γ η hle hgap => ManyBody.forall_hasEigenvalue_mono hle hgap)
    (fun N => ManyBody.exists_pos_forall_hasEigenvalue
      (posSemidef_hamiltonian_chainTranslates hh N))
    (M := W) (δ := κ * δ / (W - R + 1 : ℕ))
    (div_pos (mul_pos hκ hδ) (Nat.cast_pos.mpr (by omega))) ?_
  intro N hN
  exact toEuclideanLin_hamiltonian_chainTranslates_gap_of_long_gap_at_length
    A h hh hBounds.1 hκ hLocal
    (hN₀ N (hBounds.2.1.trans hN)) (hCanonicalKernel N hN) (hCanonicalGap N)

end Interaction

end MPSTensor

end OpenInteractionRangeComparison
