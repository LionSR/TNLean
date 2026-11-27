/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Gap.PrimitiveBlockGap
import TNLean.MPS.ParentHamiltonian.Gap.Comparison.PeriodicRangeComparison
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.BlockWordSpanNormalization
import TNLean.MPS.CanonicalForm.BlockSeparation.BlockWordSpanPropagation
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.BlockOpenGroundSpace

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

## A uniform gap at the simultaneous block-injectivity range

The supplied simultaneous injectivity length is retained: every canonical
periodic parent Hamiltonian of range at least one more than this length has
a positive gap uniform over all chain lengths. No normalization or pairwise
inequivalence assumptions are imposed on the original blocks.

This combines the block-injective interaction range in CPGSV21,
arXiv:2011.12127, Section IV.C, lines 2114--2129, with its gap theorem,
lines 2183--2187. The finite-range periodic comparison is documented in
`docs/paper-gaps/knabe88_finite_range_coefficient.tex`.

**Scope restriction (simultaneous injectivity range):**
`exists_hamiltonian_parentRingInteraction_toTensorFromBlocks_uniform_gap_of_wordTupleSpanTop`
proves the gap only at ranges \(R\geq S+1\), for a supplied \(S>0\) at which the
length-\(S\) word tuples of the blocks span the full product matrix algebra
(lines 2114--2129). The gap theorem at lines 2183--2187 is stated for all parent
Hamiltonians without a range hypothesis. Documented in
`docs/paper-gaps/cpgsv21_block_parent_interaction_range.tex`.

## The parent-Hamiltonian gap at the common block-injectivity bound

For at least two inequivalent normalized primitive blocks, a common
block-injectivity length gives an explicit sufficient interaction range.
The open-chain kernel identity at that range allows comparison with an
arbitrarily long interaction already known to have a uniform gap.

### References

* PGVWC07, arXiv:quant-ph/0608197, Theorem 12 (`2blocks.2`),
  lines 1424--1454 of `MPSarchive.tex`.
* RMP, arXiv:2011.12127, Gaps subsection, lines 2183--2187 of
  `TN-Review-main.tex`.
* Nachtergaele, arXiv:cond-mat/9410110, Theorem 2.1(ii).

## A block-injective parent-Hamiltonian gap uniform in all lengths

The eventual gap at the explicit common block-injectivity range extends to
all finite chain lengths. Each of the finitely many excluded Hamiltonians
has a positive lower norm bound on the orthogonal complement of its kernel;
taking a finite minimum gives one positive constant for the whole family.

This is the uniform-in-length conclusion in arXiv:2011.12127, Gaps subsection,
lines 2183--2187, at the range in PGVWC07, Theorem 12 (`2blocks.2`).
-/

open MPTensor

section

open Filter
open scoped Topology ComplexOrder

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ} [NeZero d] [∀ j, NeZero (dim j)]

/-- A primitive-block parent Hamiltonian has an eventual uniform periodic gap
at every positive range whose open-chain parent Hamiltonians have the
open-chain ground space as kernel on all longer chains. The gap of a
constructed longer interaction is transferred to the given range. This is the
fixed-interaction consequence of Nachtergaele's Theorem 2.1(ii),
arXiv:cond-mat/9410110, with the open kernels of Section 3. -/
theorem exists_hamiltonian_parentRingInteraction_toTensorFromBlocks_gap_of_ker_eq
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, Kraus.HasComplementaryFixedPointGap (A j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : dim j = dim i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i))
    {R : ℕ} (hR : 0 < R)
    (hKernel : ∀ W, R ≤ W →
      LinearMap.ker
          (Matrix.toEuclideanLin
              (parentChainInteraction (toTensorFromBlocks (α := Fin d)
                (μ := μ) A) R W).hamiltonian) =
        groundSpaceES (toTensorFromBlocks (α := Fin d) (μ := μ) A) W) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ N : ℕ in atTop, ∀ [NeZero N], ∀ z : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin
        (parentRingInteraction (toTensorFromBlocks (α := Fin d) (μ := μ) A) R N).hamiltonian) z →
        z = 0 ∨ (γ : ℂ) ≤ z := by
  obtain ⟨W, hRW, _, γ, hγ, hGap⟩ :=
    exists_ge_hamiltonian_parentRingInteraction_toTensorFromBlocks_gap_of_fixedPointGap
      μ A hμ ρ hP hρ hDistinct (2 * R)
  exact exists_hamiltonian_parentRingInteraction_gap_of_larger_range
    (toTensorFromBlocks (α := Fin d) (μ := μ) A) hR hRW (hKernel W (by omega)) hγ hGap

/-- Under the hypotheses of
`exists_hamiltonian_parentRingInteraction_toTensorFromBlocks_gap_of_ker_eq`,
the gap holds uniformly over every chain length: each of the finitely many
shorter chains has its own positive gap. -/
theorem exists_hamiltonian_parentRingInteraction_toTensorFromBlocks_uniform_gap_of_ker_eq
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, Kraus.HasComplementaryFixedPointGap (A j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : dim j = dim i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i))
    {R : ℕ} (hR : 0 < R)
    (hKernel : ∀ W, R ≤ W →
      LinearMap.ker
          (Matrix.toEuclideanLin
              (parentChainInteraction (toTensorFromBlocks (α := Fin d)
                (μ := μ) A) R W).hamiltonian) =
        groundSpaceES (toTensorFromBlocks (α := Fin d) (μ := μ) A) W) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (N : ℕ) [NeZero N], ∀ z : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin
        (parentRingInteraction (toTensorFromBlocks (α := Fin d) (μ := μ) A) R N).hamiltonian) z →
        z = 0 ∨ (γ : ℂ) ≤ z := by
  obtain ⟨γ, hγ, hGap⟩ :=
    exists_hamiltonian_parentRingInteraction_toTensorFromBlocks_gap_of_ker_eq
      μ A hμ ρ hP hρ hDistinct hR hKernel
  obtain ⟨M, hM⟩ := hGap.exists_forall_of_atTop
  exact hamiltonian_parentRingInteraction_gap_of_eventual_gap
    (toTensorFromBlocks (α := Fin d) (μ := μ) A) R M hγ fun N _ hN ↦ hM N hN

/-- Every interaction range above a fixed threshold gives a uniformly gapped
periodic parent Hamiltonian for a direct sum of inequivalent normalized
primitive blocks. The gap constant may depend on the interaction range.
This is the fixed-interaction consequence of Nachtergaele's Theorem 2.1(ii),
arXiv:cond-mat/9410110, with the open kernels of Section 3. -/
theorem exists_hamiltonian_parentRingInteraction_toTensorFromBlocks_gap_threshold_of_fixedPointGap
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, Kraus.HasComplementaryFixedPointGap (A j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : dim j = dim i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i)) :
    ∃ R₀ : ℕ, 0 < R₀ ∧ ∀ R : ℕ, R₀ ≤ R → ∃ γ : ℝ, 0 < γ ∧
      ∀ᶠ N : ℕ in atTop, ∀ [NeZero N], ∀ z : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin
          (parentRingInteraction (toTensorFromBlocks (α := Fin d) (μ := μ) A) R N).hamiltonian) z →
          z = 0 ∨ (γ : ℂ) ≤ z := by
  obtain ⟨R₀, hR₀, hKernel⟩ :=
    exists_ker_hamiltonian_parentChainInteraction_toTensorFromBlocks_eq_groundSpaceES
      μ A hμ ρ hP hρ hDistinct
  exact ⟨R₀, hR₀, fun R hR ↦
    exists_hamiltonian_parentRingInteraction_toTensorFromBlocks_gap_of_ker_eq
      μ A hμ ρ hP hρ hDistinct (hR₀.trans_le hR) fun W hW ↦ hKernel R W hR hW⟩

end MPSTensor

end

section

open Filter
open scoped Topology ComplexOrder

namespace MPSTensor

/-- Simultaneous injectivity at length \(S\) gives a uniform periodic gap at
every range at least \(S + 1\), with no normalization hypotheses on the blocks.
Source: CPGSV21, arXiv:2011.12127, Section IV.C, lines 2114--2129 and 2183--2187. -/
theorem exists_hamiltonian_parentRingInteraction_toTensorFromBlocks_uniform_gap_of_wordTupleSpanTop
    {d r : ℕ} {dim : Fin r → ℕ} [NeZero d] [∀ j, NeZero (dim j)]
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0) {S R : ℕ} (hS : 0 < S)
    (hSpan : WordTupleSpanTop A S) (hR : S + 1 ≤ R) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (N : ℕ) [NeZero N], ∀ z : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin
        (parentRingInteraction (toTensorFromBlocks (α := Fin d) (μ := μ) A) R N).hamiltonian) z →
        z = 0 ∨ (γ : ℂ) ≤ z := by
  obtain ⟨B, ρ, hP, hρ, hSpanB, hGS, _⟩ :=
    exists_hasComplementaryFixedPointGap_family_of_wordTupleSpanTop A hS hSpan
  have hKernel : ∀ W, R ≤ W →
      LinearMap.ker
          (Matrix.toEuclideanLin
              (parentChainInteraction (toTensorFromBlocks (α := Fin d)
                (μ := μ) B) R W).hamiltonian) =
        groundSpaceES (toTensorFromBlocks (α := Fin d) (μ := μ) B) W :=
    fun W hRW ↦ ker_hamiltonian_parentChainInteraction_toTensorFromBlocks_eq_groundSpaceES
      μ B hμ (fun j ↦ (hP j).norm)
      (fun n hn ↦ wordTupleSpanTop_of_ge_of_tracePreserving B hSpanB
        (fun j ↦ (hP j).norm) hn) hR hRW
  obtain ⟨γ, hγ, hGap⟩ :=
    exists_hamiltonian_parentRingInteraction_toTensorFromBlocks_uniform_gap_of_ker_eq
      μ B hμ ρ hP hρ (fun i j hij h ↦ by
        simpa only [eqRec_eq_cast] using
          not_gaugePhaseEquiv_of_wordTupleSpanTop B hSpanB i j hij h) (by omega) hKernel
  refine ⟨γ, hγ, fun N _ ↦ ?_⟩
  rw [hamiltonian_parentRingInteraction_toTensorFromBlocks_eq_of_block_groundSpace_eq
    μ μ A B hμ hμ (fun j ↦ hGS j R) N]
  exact hGap N

end MPSTensor

end

section

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
        (parentRingInteraction (toTensorFromBlocks (α := Fin d) (μ := μ) A) R N).hamiltonian) z →
        z = 0 ∨ (γ : ℂ) ≤ z := by
  exact exists_hamiltonian_parentRingInteraction_toTensorFromBlocks_gap_of_ker_eq
    μ A hμ ρ hP hρ hDistinct (by omega) fun _ hW ↦
      ker_hamiltonian_parentChainInteraction_toTensorFromBlocks_eq_of_threeBlock_bound
        μ A hμ ρ hP hρ hDistinct hL₀ hBlk hr hR hW

end MPSTensor

end

section

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
        (parentRingInteraction (toTensorFromBlocks (α := Fin d) (μ := μ) A) R N).hamiltonian) z →
        z = 0 ∨ (γ : ℂ) ≤ z := by
  exact exists_hamiltonian_parentRingInteraction_toTensorFromBlocks_uniform_gap_of_ker_eq
    μ A hμ ρ hP hρ hDistinct (by omega) fun _ hW ↦
      ker_hamiltonian_parentChainInteraction_toTensorFromBlocks_eq_of_threeBlock_bound
        μ A hμ ρ hP hρ hDistinct hL₀ hBlk hr hR hW

end MPSTensor

end
