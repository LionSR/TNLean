/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedPath.MPO.ArbitraryPhysicalMixedParentCommutation
import TNLean.MPS.Symmetry.MPOSymmetry.ParentHamiltonian.WeakHopfParentAverage

/-!
# The arbitrary-alphabet mixed path under a weak-Hopf representation

GLM23 extend the symmetrization of parent terms to MPO representations of
C*-weak Hopf algebras:

> "The previous symmetrization can be generalized to MPO representations of
> C*-weak Hopf algebras" (arXiv:2203.12563v3, `REsubmission.tex`, line 1279)

and carry it out in Appendix B, lines 2463--2466. Here the common operator
of the mixed path of Section 5 is assumed to be the operator tensor of a
weak-Hopf representation. The star structure of the representation then
gives adjoint closure of the boundary range, so the enlarged mixed path
Hamiltonian commutes with the common operator at every parameter of the
closed interval, with no separate closure hypothesis. On the open interval
the interaction is the ambient complement of the weak-Hopf average of the
support projection, which is the canonical parent `h_γ = 1 - Π_{S_γ}` of
lines 1689--1690: the symmetrized and the canonical parent terms coincide.

**Scope restriction (weak-Hopf representation of the common operator):**
the common operator of the mixed path is assumed to be the operator tensor
of a weak-Hopf representation. This is the hypothesis under which GLM23
state the symmetrization, line 1279 and Appendix B, line 2466; it is not a
result of Section 5, which does not construct such a representation for the
common operator, and the representation need not exist. See
`docs/paper-gaps/glm23_mixed_path_parent_commutation.tex`.

Source: Garre-Rubio–Lootens–Molnár, arXiv:2203.12563v3, Section 5,
`REsubmission.tex`, lines 1279, 1582, 1687–1692; Appendix B,
lines 2463–2466.
-/

open scoped Matrix

open ManyBody

namespace MPSTensor
namespace MPOSymmetry

variable {d₀ d₁ D₀ D₁ χ₀ χ₁ m N : ℕ}
variable {H : Type*} [Ring H] [Algebra ℂ H] [Coalgebra ℂ H] [StarRing H] [StarModule ℂ H]

variable (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁)
  (T₀ : MPOTensor d₀ χ₀) (T₁ : MPOTensor d₁ χ₁)
  (V₀ : Fin m → Matrix (Fin D₀) (Fin (χ₀ * D₀)) ℂ)
  (V₁ : Fin m → Matrix (Fin D₁) (Fin (χ₁ * D₁)) ℂ)
  (W₀ : Fin m → Matrix (Fin (χ₀ * D₀)) (Fin D₀) ℂ)
  (W₁ : Fin m → Matrix (Fin (χ₁ * D₁)) (Fin D₁) ℂ)
  {Wh : MPOTensor.WeakHopfRepresentation H ((((D₀ + D₁) * (D₀ + D₁)) + d₀) + d₁) (χ₀ + χ₁)}

/-- A weak-Hopf representation of the common operator makes its two-site
boundary range closed under conjugate transposition. Source:
arXiv:2203.12563v3, line 1279 and Appendix B, lines 2463–2466. -/
theorem exists_conjTranspose_mpoWithBoundary_arbitraryPhysicalMixedMPO_eq_of_weakHopf
    (hW : Wh.tensor = arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁)
    (X : Matrix (Fin (χ₀ + χ₁)) (Fin (χ₀ + χ₁)) ℂ) :
    ∃ Y : Matrix (Fin (χ₀ + χ₁)) (Fin (χ₀ + χ₁)) ℂ,
      (MPOTensor.mpoWithBoundary (arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁) X 2)ᴴ =
        MPOTensor.mpoWithBoundary (arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁) Y 2 := by
  obtain ⟨Y, hY⟩ := Wh.exists_conjTranspose_mpoWithBoundary_eq X
  exact ⟨Y, hW ▸ hY 2⟩

/-- On the closed interval, the enlarged mixed interaction commutes with every
two-site boundary operator of the common operator when that operator is the
tensor of a weak-Hopf representation. Source: arXiv:2203.12563v3,
lines 1279 and 1687–1692. -/
theorem arbitraryPhysicalMixedInteraction_commute_mpoWithBoundary_of_weakHopf
    [NeZero D₀] [NeZero D₁]
    (hInj₀ : Kraus.IsInjective A₀) (hInj₁ : Kraus.IsInjective A₁)
    (h₀ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₀ A₀)
      (fun _ : Fin m => A₀) V₀ W₀)
    (h₁ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₁ A₁)
      (fun _ : Fin m => A₁) V₁ W₁)
    (hW : Wh.tensor = arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁)
    {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (X : Matrix (Fin (χ₀ + χ₁)) (Fin (χ₀ + χ₁)) ℂ) :
    Commute (arbitraryPhysicalMixedInteraction A₀ A₁ γ)
      (MPOTensor.mpoWithBoundary (arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁) X 2) :=
  arbitraryPhysicalMixedInteraction_commute_mpoWithBoundary A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁
    hInj₀ hInj₁ h₀ h₁
    (exists_conjTranspose_mpoWithBoundary_arbitraryPhysicalMixedMPO_eq_of_weakHopf
      A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ hW) hγ X

/-- On every periodic ring of length at least two and at every parameter of
the closed interval, the enlarged mixed path Hamiltonian commutes with every
periodic boundary operator, with boundary commuting with the letters, of a
common operator that is the tensor of a weak-Hopf representation.
Source: arXiv:2203.12563v3, lines 1279, 1582 and 1687–1692. -/
theorem
    hamiltonian_arbitraryPhysicalMixedInteraction_commute_mpoWithBoundary_of_weakHopf
    [NeZero D₀] [NeZero D₁]
    (hInj₀ : Kraus.IsInjective A₀) (hInj₁ : Kraus.IsInjective A₁)
    (h₀ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₀ A₀)
      (fun _ : Fin m => A₀) V₀ W₀)
    (h₁ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₁ A₁)
      (fun _ : Fin m => A₁) V₁ W₁)
    (hW : Wh.tensor = arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁)
    {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (hN : 2 ≤ N)
    {X : Matrix (Fin (χ₀ + χ₁)) (Fin (χ₀ + χ₁)) ℂ}
    (hX : X ∈ MPOTensor.commutingBoundaryAlgebra
      (arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁)) :
    haveI : NeZero N := ⟨by omega⟩; Commute (Interaction.translationInvariant N
        (arbitraryPhysicalMixedInteraction A₀ A₁ γ)).hamiltonian
      (MPOTensor.mpoWithBoundary (arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁) X N) :=
  haveI : NeZero N := ⟨by omega⟩;
  hamiltonian_arbitraryPhysicalMixedInteraction_commute_mpoWithBoundary
    A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ hInj₀ hInj₁ h₀ h₁
    (exists_conjTranspose_mpoWithBoundary_arbitraryPhysicalMixedMPO_eq_of_weakHopf
      A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ hW) hγ hN hX

/-- On every periodic ring of length at least two and at every parameter of
the closed interval, the enlarged mixed path Hamiltonian commutes with the
periodic common operator when that operator is the tensor of a weak-Hopf
representation. Source: arXiv:2203.12563v3, lines 1279, 1582 and
1687–1692, with `defphase`, lines 1253–1259. -/
theorem hamiltonian_arbitraryPhysicalMixedInteraction_commute_mpo_of_weakHopf
    [NeZero D₀] [NeZero D₁]
    (hInj₀ : Kraus.IsInjective A₀) (hInj₁ : Kraus.IsInjective A₁)
    (h₀ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₀ A₀)
      (fun _ : Fin m => A₀) V₀ W₀)
    (h₁ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₁ A₁)
      (fun _ : Fin m => A₁) V₁ W₁)
    (hW : Wh.tensor = arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁)
    {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩; Commute (Interaction.translationInvariant N
        (arbitraryPhysicalMixedInteraction A₀ A₁ γ)).hamiltonian
      (MPOTensor.mpo (arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁) N) :=
  haveI : NeZero N := ⟨by omega⟩; hamiltonian_arbitraryPhysicalMixedInteraction_commute_mpo
    A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ hInj₀ hInj₁ h₀ h₁
    (exists_conjTranspose_mpoWithBoundary_arbitraryPhysicalMixedMPO_eq_of_weakHopf
      A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ hW) hγ hN


/-- On the open interval, the enlarged mixed interaction is the ambient
complement \(I-E(P_\gamma)\) of the weak-Hopf average of the two-site support
projection of the mixed tensor: the symmetrized parent term coincides with
the canonical parent `h_γ = 1 - Π_{S_γ}`. Source: arXiv:2203.12563v3,
lines 1279 and 1689–1690, and Appendix B, lines 2463–2466. -/
theorem toEuclideanLin_arbitraryPhysicalMixedInteraction_eq_one_sub_weakHopfAverage
    (hInj₀ : Kraus.IsInjective A₀) (hInj₁ : Kraus.IsInjective A₁)
    (h₀ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₀ A₀)
      (fun _ : Fin m => A₀) V₀ W₀)
    (h₁ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₁ A₁)
      (fun _ : Fin m => A₁) V₁ W₁)
    (hW : Wh.tensor = arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁)
    {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    Matrix.toEuclideanLin (arbitraryPhysicalMixedInteraction A₀ A₁ γ) =
      1 - Wh.weakHopfAverage 2
          ((MPSTensor.groundSpace (arbitraryPhysicalMixedInterpolation A₀ A₁ γ) 2).map
          (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap).starProjection.toLinearMap := by
  have hcompat : MPOTensor.IsBoundaryCompatible Wh.tensor
      (arbitraryPhysicalMixedInterpolation A₀ A₁ γ) := hW ▸
    isBoundaryCompatible_arbitraryPhysicalMixedInterpolation A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ h₀ h₁ γ
  rw [Wh.one_sub_weakHopfAverage_starProjection_eq_toEuclideanLin_toMatrix'_parentInteraction
      hcompat
      (Kraus.isNBlkInjective_one_of_isInjective
        (isInjective_arbitraryPhysicalMixedInterpolation A₀ A₁ hInj₀ hInj₁ hγ)) two_pos,
    arbitraryPhysicalMixedInteraction_eq_parent_of_mem_Ioo A₀ A₁ hγ]

end MPOSymmetry
end MPSTensor
