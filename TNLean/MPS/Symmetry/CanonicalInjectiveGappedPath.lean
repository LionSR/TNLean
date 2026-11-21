/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Hamiltonian.KernelGap
import TNLean.MPS.Symmetry.InteractionHamiltonianSymmetry
import TNLean.MPS.Symmetry.ParentHamiltonianSymmetry
import TNLean.MPS.ParentHamiltonian.CompactParentGap

/-!
# Canonical parent interactions along an injective path

A continuous path of one-site injective tensors with a fixed on-site
unitary symmetry gives a symmetric gapped interaction path between its
canonical two-site parent interactions. The gap follows from compactness;
no finite-window bound is assumed.

**Scope restriction (one-site injective tensors):** this is the single-block,
one-site injective case of arXiv:1010.3732, Section II.C and Appendix A.
The source also treats several-block normal forms. Documented in
`docs/paper-gaps/spc11_uniform_gap_injective_scope.tex`.
-/

open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace MPSTensor

/-- For an injective tensor, a canonical parent norm gap is a gap above the zero ground energy.
Source: arXiv:1010.3732, Section II.C and Appendix A, spectral interpretation of the parent
gap. -/
theorem isGapped_hamiltonian_translationInvariant_parent
    {d D N : ℕ} [NeZero D] (A : MPSTensor d D) (hInj : Kraus.IsInjective A)
    (hN : 2 ≤ N) {δ : ℝ}
    (hGap : ∀ v ∈ (LinearMap.ker
        (Matrix.toEuclideanLin (parentRingInteraction A hN).hamiltonian))ᗮ,
      δ * ‖v‖ ≤ ‖Matrix.toEuclideanLin (parentRingInteraction A hN).hamiltonian v‖) :
    ManyBody.IsGapped (ManyBody.Interaction.translationInvariant hN
      (LinearMap.toMatrix' (parentInteraction A 2))).hamiltonian 0 δ := by
  exact (ManyBody.isGapped_zero_iff_norm
    (posSemidef_hamiltonian_parentRingInteraction A hN)).mpr
      ⟨groundSpace_hamiltonian_parentRingInteraction_two_ne_bot A hInj hN, hGap⟩

/-- A continuous one-site injective tensor path with fixed unitary on-site
symmetry determines a symmetric uniformly gapped path of its canonical
nearest-neighbor parent interactions. Source: arXiv:1010.3732, Section II.C
and Appendix A, single-block injective case. -/
noncomputable def canonicalInjectiveGappedPath
    {G : Type} [Group G] {d D : ℕ} [NeZero D]
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (A : ℝ → MPSTensor d D) (hA : ContinuousOn A (Set.Icc (0 : ℝ) 1))
    (hInj : ∀ γ ∈ Set.Icc (0 : ℝ) 1, Kraus.IsInjective (A γ))
    (hCov : ∀ γ ∈ Set.Icc (0 : ℝ) 1, ∀ g : G,
      GaugeEquiv (A γ) (rotatePhysical (U g) (A γ))) :
    SymmetricGappedInteractionPath U
      (LinearMap.toMatrix' (parentInteraction (A 0) 2))
      (LinearMap.toMatrix' (parentInteraction (A 1) 2)) where
  interaction γ := LinearMap.toMatrix' (parentInteraction (A γ) 2)
  interaction_zero := rfl
  interaction_one := rfl
  hermitian γ _ := (parentInteraction_toMatrix'_isStarProjection (A γ) 2).isSelfAdjoint
  norm_le_one γ _ := parentInteraction_toMatrix'_norm_le_one (A γ) 2
  continuous := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply continuous_toMatrix'_parentInteraction_family
      (fun γ : Set.Icc (0 : ℝ) 1 => A γ)
      (continuousOn_iff_continuous_domRestrict.mp hA) 2
    intro γ
    exact isNBlkInjective_of_le zero_lt_one
      (Kraus.isNBlkInjective_one_of_isInjective (hInj γ γ.property)) one_le_two
  gap := by
    let B : Set.Icc (0 : ℝ) 1 → MPSTensor d D := fun γ => A γ
    obtain ⟨δ, hδ, hGap⟩ :=
      exists_uniform_parentHamiltonianES_gap_of_compact_isInjective_all_lengths B
        (continuousOn_iff_continuous_domRestrict.mp hA)
        (fun γ => hInj γ γ.property) isCompact_univ
    refine ⟨δ, hδ, fun γ hγ N hN => ⟨0,
      isGapped_hamiltonian_translationInvariant_parent (A γ) (hInj γ hγ) hN ?_⟩⟩
    have hH : parentHamiltonianES (A γ) 2 N =
        Matrix.toEuclideanLin (parentRingInteraction (A γ) hN).hamiltonian :=
      parentHamiltonianES_eq_toEuclideanLin_sum_placeAlong_ringWindow (A γ) hN
    rw [← hH]
    exact hGap ⟨γ, hγ⟩ (Set.mem_univ _) N hN
  symmetric γ hγ g N hN := by
    rw [← onSiteTensorPow_eq_finKronecker]
    have hSym := hamiltonian_translationInvariant_commute_onSiteTensorPow (U g)
      (LinearMap.toMatrix' (parentInteraction (A γ) 2)) hN
      (parentInteraction_matrix_commute_onSiteTensorPow (A γ) (U g)
        (SetLike.coe_mem _) (hCov γ hγ g) 2)
    exact hSym

end MPSTensor
