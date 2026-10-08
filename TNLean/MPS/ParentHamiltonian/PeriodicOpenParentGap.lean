/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.ResidualCoverProjectionDefect
import TNLean.MPS.ParentHamiltonian.Martingale.ResidueCoverGapLimit
import TNLean.Algebra.OrthogonalKernelGap

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
exact open kernels above that range, and one norm gap at every volume.
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2,
Lemma commutation (ii), and Section 6, in the periodic tensor setting. -/
theorem IsPeriodic.exists_pos_openParentHamiltonianES_gap
    {A : MPSTensor d D} (hA : IsPeriodic m A) :
    ∃ R : ℕ, 0 < R ∧
      (∀ N, R ≤ N → LinearMap.ker (openParentHamiltonianES A R N) = groundSpaceES A N) ∧
      ∃ δ : ℝ, 0 < δ ∧
        ∀ N, ∀ v ∈ (LinearMap.ker (openParentHamiltonianES A R N))ᗮ,
          δ * ‖v‖ ≤ ‖openParentHamiltonianES A R N v‖ := by
  let : NeZero d := ⟨hA.physDim_ne_zero⟩
  obtain ⟨R, hR, hKernel, N₀, _hRN, δ, hδ, hGap⟩ :=
    hA.exists_pos_openParentHamiltonianES_gap_of_residue_cover_limit
      hA.residual_cover_projection_defect_tendsto_zero
  obtain ⟨γ, hγ, hAll⟩ := Nat.exists_pos_forall_of_eventually
    (P := fun N γ => ∀ v ∈ (LinearMap.ker (openParentHamiltonianES A R N))ᗮ,
      γ * ‖v‖ ≤ ‖openParentHamiltonianES A R N v‖)
    (fun N γ η hle hgap v hv =>
      (mul_le_mul_of_nonneg_right hle (norm_nonneg v)).trans (hgap v hv))
    (fun N => LinearMap.exists_pos_mul_norm_le_of_mem_orthogonal_ker
      (openParentHamiltonianES A R N)) hδ hGap
  exact ⟨R, hR, hKernel, γ, hγ, hAll⟩

/-- A normalized periodic tensor admits a positive local matrix interaction
with exact original-chain open kernels and one norm gap at every volume.
No interaction, faithful invariant matrix, or sector separation is supplied.
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2,
Lemma existenceinteraction, and Section 6, in the periodic tensor setting. -/
theorem IsPeriodic.exists_positive_parent_interaction_uniform_gap
    {A : MPSTensor d D} (hA : IsPeriodic m A) :
    ∃ R : ℕ, 0 < R ∧ ∃ h : Matrix (Cfg d R) (Cfg d R) ℂ,
      h.PosSemidef ∧
      (∀ N, R ≤ N → LinearMap.ker
        (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) = groundSpaceES A N) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ N, ∀ v ∈ (LinearMap.ker
        (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N))ᗮ,
        δ * ‖v‖ ≤ ‖openInteractionHamiltonianES (Matrix.toEuclideanLin h) N v‖ := by
  obtain ⟨R, hR, hKernel, δ, hδ, hGap⟩ := hA.exists_pos_openParentHamiltonianES_gap
  refine ⟨R, hR, canonicalParentInteractionMatrix A R,
    canonicalParentInteractionMatrix_posSemidef A R, ?_, δ, hδ, ?_⟩
  · simpa only [toEuclideanLin_canonicalParentInteractionMatrix,
      openInteractionHamiltonianES_parentInteractionES A hR] using hKernel
  · simpa only [toEuclideanLin_canonicalParentInteractionMatrix,
      openInteractionHamiltonianES_parentInteractionES A hR] using hGap

end MPSTensor
