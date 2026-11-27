/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Hamiltonian.KernelGap
import TNLean.MPS.ParentHamiltonian.Deformation.ParentHamiltonianSymmetry
import TNLean.MPS.ParentHamiltonian.Continuity.CompactParentGap
import TNLean.MPS.Symmetry.GappedPath.ExactMPSGappedPhase
import TNLean.MPS.FundamentalTheorem.InjectivePhase

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

## Exact ground-state realizations of canonical injective parent paths

A continuous one-site injective tensor family represents the unique ground
lines of its canonical two-site parents. The certificate uses the physical
interaction path but imposes no additional symmetry or virtual data.

Source: Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.C,
Appendix A, and Section II.F.2, lines 930–954.
-/

open MPTensor

section

open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace MPSTensor

/-- For an injective tensor, a lower bound on the nonzero eigenvalues of the canonical parent
Hamiltonian is a gap above the zero ground energy. Source: arXiv:1010.3732, Section II.C and
Appendix A, spectral interpretation of the parent gap. -/
theorem isGapped_hamiltonian_translationInvariant_parent
    {d D N : ℕ} [NeZero D] (A : MPSTensor d D) (hInj : Kraus.IsInjective A)
    (hN : 2 ≤ N) {δ : ℝ}
    (hGap : haveI : NeZero N := ⟨by omega⟩; ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (parentRingInteraction A 2 N).hamiltonian) μ →
      μ = 0 ∨ (δ : ℂ) ≤ μ) :
    haveI : NeZero N := ⟨by omega⟩;
    ManyBody.IsGapped (ManyBody.Interaction.translationInvariant N
      (LinearMap.toMatrix' (parentInteraction A 2))).hamiltonian 0 δ := by
  have : NeZero N := ⟨by omega⟩
  exact ManyBody.isGapped_zero_iff.mpr
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
  hermitian γ _ := (isStarProjection_toMatrix'_parentInteraction (A γ) 2).isSelfAdjoint
  norm_le_one γ _ := parentInteraction_toMatrix'_norm_le_one (A γ) 2
  continuous := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply continuous_toMatrix'_parentInteraction_family
      (fun γ : Set.Icc (0 : ℝ) 1 => A γ)
      (continuousOn_iff_continuous_domRestrict.mp hA) 2
    intro γ
    exact Kraus.isNBlkInjective_of_le zero_lt_one
      (Kraus.isNBlkInjective_one_of_isInjective (hInj γ γ.property)) one_le_two
  gap := by
    let B : Set.Icc (0 : ℝ) 1 → MPSTensor d D := fun γ => A γ
    obtain ⟨δ, hδ, hGap⟩ :=
      exists_uniform_hamiltonian_parentRingInteraction_gap_of_compact_isInjective_all_lengths B
        (continuousOn_iff_continuous_domRestrict.mp hA)
        (fun γ => hInj γ γ.property) isCompact_univ
    exact ⟨δ, hδ, fun γ hγ N hN => ⟨0, hGap ⟨γ, hγ⟩ (Set.mem_univ _) N hN⟩⟩
  symmetric γ hγ g N hN := by
    rw [← onSiteTensorPow_eq_piKronecker]
    have : NeZero N := ⟨by omega⟩
    have hSym := hamiltonian_translationInvariant_commute_onSiteTensorPow (N := N) (U g)
      (LinearMap.toMatrix' (parentInteraction (A γ) 2))
      (parentInteraction_matrix_commute_onSiteTensorPow (A γ) (U g)
        (SetLike.coe_mem _) (hCov γ hγ g) 2)
    exact hSym

end MPSTensor

end

section

open scoped Matrix

namespace MPSTensor

/-- The periodic two-site parent of a one-site injective tensor has the
periodic MPS line as its kernel. Source: arXiv:1010.3732, Appendix A,
single-block parent-Hamiltonian argument. -/
theorem hamiltonian_translationInvariant_parent_groundSpace_eq_span_mpv
    {d D N : ℕ} [NeZero D] (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    LinearMap.ker (Matrix.toEuclideanLin (ManyBody.Interaction.translationInvariant N
      (LinearMap.toMatrix' (parentInteraction A 2))).hamiltonian) =
      Submodule.span ℂ
        {(WithLp.linearEquiv 2 ℂ ((Fin N → Fin d) → ℂ)).symm (mpv A)} := by
  refine (ker_hamiltonian_parentRingInteraction_two_eq_range_periodicMpvLineMap A hA hN).trans ?_
  simpa only [periodicMpvLineMap] using
    ContinuousLinearMap.range_smulRight_apply
      (by norm_num : (1 : ℂ →L[ℂ] ℂ) ≠ 0)
      ((WithLp.linearEquiv 2 ℂ ((Fin N → Fin d) → ℂ)).symm (mpv A))

/-- A continuous one-site injective tensor family certifies the exact MPS
ground lines of any physical path with its canonical parent interactions.
Source: arXiv:1010.3732, Appendix A and Section II.F.2, lines 930–954. -/
noncomputable def exactMPSGroundPath_of_canonicalInjective
    {G : Type} [Group G] {d D : ℕ} [NeZero D]
    {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
    {h₀ h₁ : MPOTensor.ChainOperator d 2}
    (P : SymmetricGappedInteractionPath U h₀ h₁)
    (A : ℝ → MPSTensor d D) (hA : ContinuousOn A (Set.Icc (0 : ℝ) 1))
    (hInj : ∀ γ ∈ Set.Icc (0 : ℝ) 1, Kraus.IsInjective (A γ))
    (hP : ∀ γ ∈ Set.Icc (0 : ℝ) 1,
      P.interaction γ = LinearMap.toMatrix' (parentInteraction (A γ) 2)) :
    ExactMPSGroundPath P where
  bondDimension := D
  bondDimension_pos := NeZero.pos D
  tensor := A
  continuous := hA
  injective_representative γ hγ :=
    ⟨D, NeZero.pos D, le_rfl, A γ, hInj γ hγ, SamePositiveMpvRay.refl _⟩
  nonzero γ hγ N hN := by
    obtain ⟨σ, hσ⟩ := exists_mpv_ne_zero_of_isInjective (hInj γ hγ) hN
    exact fun hz => hσ (congrFun hz σ)
  ground_line γ hγ N hN := by
    have : NeZero N := ⟨by omega⟩
    rw [hP γ hγ]
    obtain ⟨Δ, hΔ, hpos⟩ := ManyBody.exists_pos_forall_hasEigenvalue
      (posSemidef_hamiltonian_parentRingInteraction (A γ) 2 N)
    have hGap := isGapped_hamiltonian_translationInvariant_parent (A γ) (hInj γ hγ) hN
      (δ := 0) (ManyBody.forall_hasEigenvalue_mono hΔ.le hpos)
    have hmem (μ : ℂ) : μ ∈ spectrum ℂ (ManyBody.Interaction.translationInvariant N
        (LinearMap.toMatrix' (parentInteraction (A γ) 2))).hamiltonian ↔
        Module.End.HasEigenvalue (Matrix.toEuclideanLin
          (ManyBody.Interaction.translationInvariant N
            (LinearMap.toMatrix' (parentInteraction (A γ) 2))).hamiltonian) μ := by
      rw [← Matrix.spectrum_toLpLin (p := 2), Module.End.hasEigenvalue_iff_mem_spectrum]
    refine ⟨0, (hmem 0).mpr (Module.End.hasEigenvalue_iff.mpr (by
      simpa only [ManyBody.groundSpace, Complex.ofReal_zero] using hGap.1)), fun z hz => ?_, ?_⟩
    · rcases hGap.2 z ((hmem z).mp hz) with h | h
      · simp [h]
      · simpa using (Complex.le_def.mp h).1
    simpa only [Complex.ofReal_zero, zero_smul, sub_zero] using
      hamiltonian_translationInvariant_parent_groundSpace_eq_span_mpv (A γ) (hInj γ hγ) hN

end MPSTensor

end
