/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.PolarDeformation
import TNLean.MPS.ParentHamiltonian.CompactParentGap
import TNLean.MPS.Symmetry.ParentHamiltonianSymmetry

/-!
# Uniform gap along the injective polar deformation

The polar path of a one-site injective tensor is continuous and remains
injective on the compact interval `[0, 1]`. The compact-family parent gap
therefore gives one positive gap above the zero ground energy for every
parameter and every periodic chain of at least two sites.

**Scope restriction (one-site injective tensors):** this is the single-block,
one-site injective case of arXiv:1010.3732, Section II.C and Appendix A,
lines 2475--2580. It uses canonical two-site parent projections.
Documented in `docs/paper-gaps/spc11_uniform_gap_injective_scope.tex`.

## References

- [arXiv:1010.3732](https://arxiv.org/abs/1010.3732) -- Schuch,
  Pérez-García, Cirac, *Classifying quantum phases using matrix product
  states and projected entangled pair states*, Section II.C and Appendix A
-/

open scoped Matrix

namespace MPSTensor

/-- The canonical parent Hamiltonians along the polar deformation of a
one-site injective tensor are gapped above their zero ground energy, with a
gap uniform in the parameter and the chain length. Source: arXiv:1010.3732,
Section II.C and Appendix A. -/
theorem exists_uniform_hamiltonian_parentRingInteraction_gap_polarDeformation
    {d D : ℕ} [NeZero D] {A : MPSTensor d D} (hA : Kraus.IsInjective A) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ γ ∈ Set.Icc (0 : ℝ) 1, ∀ N : ℕ, ∀ hN : 2 ≤ N,
      ManyBody.IsGapped (parentRingInteraction (polarDeformation A γ) hN).hamiltonian 0 δ := by
  let B : Set.Icc (0 : ℝ) 1 → MPSTensor d D := fun γ => polarDeformation A γ
  have hB : Continuous B := (continuous_polarDeformation A).comp continuous_subtype_val
  have hInj (γ : Set.Icc (0 : ℝ) 1) : Kraus.IsInjective (B γ) :=
    isInjective_polarDeformation hA γ.property
  obtain ⟨δ, hδ, hGap⟩ :=
    exists_uniform_parentHamiltonianES_gap_of_compact_isInjective_all_lengths
      B hB hInj isCompact_univ
  refine ⟨δ, hδ, fun γ hγ N hN => ?_⟩
  have hH : parentHamiltonianES (polarDeformation A γ) 2 N =
      Matrix.toEuclideanLin (parentRingInteraction (polarDeformation A γ) hN).hamiltonian :=
    parentHamiltonianES_eq_toEuclideanLin_sum_placeAlong_ringWindow _ hN
  refine (ManyBody.isGapped_zero_iff_norm
    (posSemidef_hamiltonian_parentRingInteraction (polarDeformation A γ) hN)).mpr
      ⟨groundSpace_hamiltonian_parentRingInteraction_two_ne_bot _ (hInj ⟨γ, hγ⟩) hN, ?_⟩
  rw [← hH]
  exact hGap ⟨γ, hγ⟩ (Set.mem_univ _) N hN

/-- Canonical parent interactions commute with the same on-site symmetry
throughout an injective polar deformation in unitary virtual gauge.
Source: arXiv:1010.3732, Section II.C, “Isometric form and symmetries”. -/
theorem commute_toMatrix'_parentInteraction_polarDeformation_onSiteTensorPow
    {d D : ℕ} {A : MPSTensor d D} (hA : Kraus.IsInjective A)
    (U : Matrix (Fin d) (Fin d) ℂ) (X : Matrix (Fin D) (Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hX : X ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hCov : rotatePhysical U A = fun i => X * A i * Xᴴ) (γ : ℝ) (L : ℕ) :
    Commute (LinearMap.toMatrix' (parentInteraction (polarDeformation A γ) L))
      (onSiteTensorPow L U) :=
  parentInteraction_matrix_commute_onSiteTensorPow _ U hU
    (gaugeEquiv_polarDeformation_of_unitary_covariance hA U X hU hX hCov γ) L

end MPSTensor
