/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.ResidueCoverGapCriterion
import QICLean.Topology.UniformSelectionBounds
import QICLean.Analysis.OrthogonalKernelGap

/-!
# A uniform open gap from aligned gaps and residual covers

For an arbitrary tensor, an eventual gap at lengths divisible by a fixed
positive integer extends to all original lengths once the canonical kernels
are exact and the residual cover projection defects vanish uniformly along
every choice of the exterior lengths. The finitely many remaining volumes
are included by taking a positive finite minimum above their actual kernels.

The aligned gap, exact kernels, and projection limits are explicit hypotheses.
This is an auxiliary criterion, rather than a tensor-specific gap theorem.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6, Lemma commutation
(ii), and equations (3.12)--(3.16).
-/

open Filter
open scoped InnerProductSpace ComplexOrder
namespace MPSTensor
variable {d D R L N₀ : ℕ}

/-- An eventual aligned gap, exact canonical open kernels, and residual
cover projection limits imply a single gap at every original length: every eigenvalue of the
open-chain parent Hamiltonian is `0` or at least the gap. Source: Nachtergaele,
arXiv:cond-mat/9410110, Section 6, Lemma commutation (ii).
The three supplied estimates are explicit hypotheses of this criterion. -/
theorem exists_pos_hamiltonian_parentChainInteraction_gap_of_aligned_gap_of_residue_cover_limit
    (A : MPSTensor d D) (hR : 0 < R) (hL : 0 < L)
    (hKernel : ∀ N, R ≤ N →
      LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A R N).hamiltonian) =
          groundSpaceES A N)
    {γ : ℝ} (hγ : 0 < γ)
    (hAligned : ∀ n ≥ N₀, ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentChainInteraction A R (n * L)).hamiltonian) μ →
        μ = 0 ∨ (γ : ℂ) ≤ μ)
    (hDefect : ∀ K r : ℕ → ℕ, Tendsto (fun M =>
      ‖(groundSpaceES A (K M * L + M * L + r M)).starProjection -
        (leftBoundaryMapES A (K M * L + M * L) (r M)).range.starProjection.comp
          (reassocTailBoundaryMapES A (K M * L) (M * L) (r M)).range.starProjection‖)
      atTop (nhds 0)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N,
      ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (parentChainInteraction A R N).hamiltonian) μ →
          μ = 0 ∨ (δ : ℂ) ≤ μ := by
  let e (M : ℕ) (z : ℕ × ℕ) : ℝ :=
    ‖(groundSpaceES A (z.1 * L + M * L + z.2)).starProjection -
      (leftBoundaryMapES A (z.1 * L + M * L) z.2).range.starProjection.comp
        (reassocTailBoundaryMapES A (z.1 * L) (M * L) z.2).range.starProjection‖
  have hUniform : ∀ᶠ M in atTop, ∀ z, e M z ≤ (1 / 2 : ℝ) :=
    eventually_forall_le_of_tendsto_all_selections e
      (fun z => hDefect (fun M => (z M).1) (fun M => (z M).2)) (by norm_num)
  obtain ⟨M, hM, hRM⟩ := (hUniform.and (eventually_ge_atTop (max R N₀))).exists
  have hRW : R ≤ M * L :=
    (le_max_left R N₀).trans (hRM.trans (Nat.le_mul_of_pos_right M hL))
  have hLeft : ∀ K ≥ 0, ∀ μ : ℂ, Module.End.HasEigenvalue
    (Matrix.toEuclideanLin (parentChainInteraction A R (K * L + M * L)).hamiltonian) μ →
      μ = 0 ∨ (γ : ℂ) ≤ μ := by
    intro K _
    rw [← Nat.add_mul]
    exact hAligned (K + M) (by omega)
  obtain ⟨δ, hδ, hResidue⟩ :=
    exists_pos_hamiltonian_parentChainInteraction_gap_of_aligned_cover_defect
      A hR hL hRW hKernel hγ hLeft (fun K _ r _ => hM (K, r))
  have hTail := hamiltonian_parentChainInteraction_gap_all_large_of_residue_gaps A hL hResidue
  exact Nat.exists_pos_forall_of_eventually
    (P := fun N δ => ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentChainInteraction A R N).hamiltonian) μ →
        μ = 0 ∨ (δ : ℂ) ≤ μ)
    (fun N δ η hle hgap => ManyBody.forall_hasEigenvalue_mono hle hgap)
    (fun N => ManyBody.exists_pos_forall_hasEigenvalue
      (posSemidef_hamiltonian_parentChainInteraction A R N)) hδ hTail

end MPSTensor

