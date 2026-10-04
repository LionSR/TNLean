/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.ExactMPSGappedPhase
import TNLean.MPS.Symmetry.CanonicalInjectiveGappedPath
import TNLean.MPS.FundamentalTheorem.InjectivePhase

/-!
# Exact ground-state realizations of canonical injective parent paths

A continuous one-site injective tensor family represents the unique ground
lines of its canonical two-site parents. The certificate uses the physical
interaction path but imposes no additional symmetry or virtual data.

Source: Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.C,
Appendix A, and Section II.F.2, lines 930–954.
-/

open scoped Matrix

namespace MPSTensor

/-- The periodic two-site parent of a one-site injective tensor has the
periodic MPS line as its kernel. Source: arXiv:1010.3732, Appendix A,
single-block parent-Hamiltonian argument. -/
theorem interactionHamiltonian_parent_groundSpace_eq_span_mpv
    {d D N : ℕ} [NeZero D] (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (hN : 2 ≤ N) :
    LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian
      (LinearMap.toMatrix' (parentInteraction A 2)) hN)) =
      Submodule.span ℂ
        {(WithLp.linearEquiv 2 ℂ ((Fin N → Fin d) → ℂ)).symm (mpv A)} := by
  rw [interactionHamiltonian,
    ← parentHamiltonianES_eq_toEuclideanLin_sum_embedLocalOperator A hN,
    ker_parentHamiltonianES_two_eq_range_periodicMpvLineMap A hA hN]
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
    rw [hP γ hγ]
    have hSpec := interactionHamiltonian_parent_spectrum_gap (A γ) (hInj γ hγ) hN
      (δ := 0) (fun v _ => by
        simpa only [zero_mul] using norm_nonneg (parentHamiltonianES (A γ) 2 N v))
    refine ⟨0, hSpec.1, fun z hz => (hSpec.2 z hz).1, ?_⟩
    simpa only [Complex.ofReal_zero, zero_smul, sub_zero] using
      interactionHamiltonian_parent_groundSpace_eq_span_mpv (A γ) (hInj γ hγ) hN

end MPSTensor
