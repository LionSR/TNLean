/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.ResidualCoverProjectionDefect
import TNLean.MPS.ParentHamiltonian.Martingale.ResidueCoverGapLimit
import QICLean.Analysis.OrthogonalKernelGap

/-!
# A periodic tensor has a uniform original-chain open-parent gap

The canonical interaction range is chosen from the original cyclic
intersection. The residual cover projection estimate gives a uniform gap
at all sufficiently large volumes, including every residue modulo the
period. Finite-dimensional spectral bounds at the remaining finitely many
volumes give one constant for every volume. The gap is taken on the
complement of the actual Hamiltonian kernel, including below the interaction
range, where the Hamiltonian vanishes.

**Scope restriction (periodic tensor presentation):** The results concern
an explicitly supplied normalized periodic tensor. The passage from a
general GVBS presentation to this tensor presentation remains separate;
see docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2,
Lemma commutation (ii), equations (3.12)--(3.16), and Section 6.
-/

open scoped ComplexOrder
namespace MPSTensor
variable {d D m : ℕ}

/-- Periodicity alone derives a canonical original-chain interaction range,
exact open kernels above that range, and one gap at every volume: every eigenvalue of the
open-chain parent Hamiltonian is `0` or at least the gap.
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2,
Lemma commutation (ii), and Section 6, in the periodic tensor setting. -/
theorem IsPeriodic.exists_pos_hamiltonian_parentChainInteraction_gap
    {A : MPSTensor d D} (hA : IsPeriodic m A) :
    ∃ R : ℕ, 0 < R ∧
      (∀ N, R ≤ N → LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A R N).hamiltonian)
          = groundSpaceES A N) ∧
      ∃ δ : ℝ, 0 < δ ∧
        ∀ N, ∀ μ : ℂ, Module.End.HasEigenvalue
          (Matrix.toEuclideanLin (parentChainInteraction A R N).hamiltonian) μ →
            μ = 0 ∨ (δ : ℂ) ≤ μ := by
  let : NeZero d := ⟨hA.physDim_ne_zero⟩
  obtain ⟨R, hR, hKernel, N₀, _hRN, δ, hδ, hGap⟩ :=
    hA.exists_pos_hamiltonian_parentChainInteraction_gap_of_residue_cover_limit
      hA.residual_cover_projection_defect_tendsto_zero
  obtain ⟨γ, hγ, hAll⟩ := Nat.exists_pos_forall_of_eventually
    (P := fun N γ => ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentChainInteraction A R N).hamiltonian) μ →
        μ = 0 ∨ (γ : ℂ) ≤ μ)
    (fun N γ η hle hgap => ManyBody.forall_hasEigenvalue_mono hle hgap)
    (fun N => ManyBody.exists_pos_forall_hasEigenvalue
      (posSemidef_hamiltonian_parentChainInteraction A R N)) hδ hGap
  exact ⟨R, hR, hKernel, γ, hγ, hAll⟩

/-- A normalized periodic tensor admits a positive local matrix interaction
with exact original-chain open kernels and one gap above the kernel at every volume:
every eigenvalue of the open-chain Hamiltonian is `0` or at least the gap.
No interaction, faithful invariant matrix, or sector separation is supplied.
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2,
Lemma existenceinteraction, and Section 6, in the periodic tensor setting. -/
theorem IsPeriodic.exists_positive_parent_interaction_uniform_gap
    {A : MPSTensor d D} (hA : IsPeriodic m A) :
    ∃ R : ℕ, 0 < R ∧ ∃ h : Matrix (Cfg d R) (Cfg d R) ℂ,
      h.PosSemidef ∧
      (∀ N, R ≤ N → LinearMap.ker (Matrix.toEuclideanLin
        (ManyBody.Interaction.chainTranslates R N h).hamiltonian) = groundSpaceES A N) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ N, ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (ManyBody.Interaction.chainTranslates R N h).hamiltonian) μ →
          μ = 0 ∨ (δ : ℂ) ≤ μ := by
  obtain ⟨R, hR, hKernel, δ, hδ, hGap⟩ := hA.exists_pos_hamiltonian_parentChainInteraction_gap
  exact ⟨R, hR, LinearMap.toMatrix' (parentInteraction A R),
    posSemidef_toMatrix'_parentInteraction A R, hKernel, δ, hδ, hGap⟩

end MPSTensor
