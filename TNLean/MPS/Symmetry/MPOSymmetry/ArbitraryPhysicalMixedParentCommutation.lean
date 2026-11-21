/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.BoundaryParentHamiltonian
import TNLean.MPS.Symmetry.MPOSymmetry.ArbitraryPhysicalMixedHermitianGauge
import TNLean.MPS.Symmetry.MPOSymmetry.ArbitraryPhysicalMixedMPO
import TNLean.MPS.Symmetry.MPOSymmetry.ArbitraryPhysicalMixedPathGap

/-!
# Commutation of the arbitrary-alphabet mixed path with its common MPO

GLM23 call the interpolation of Section 5 a symmetric path. Their
definition of a phase requires the path Hamiltonian to commute with the
MPO symmetry. Section 5 takes the canonical parent
`h_γ = 1 - Π_{S_γ}` of the interpolating tensor:

> "It is clear that the tensor $A(\gamma)$ defined in Eq.\ \eqref{defAgamma}
> is injective for $\gamma \in (0,1)$, so that the parent Hamiltonian
> $H_{A(\gamma)} \equiv H(\gamma)$ is gapped and has as unique ground state
> $|\psi_{A(\gamma)} \rangle$ within that region." (lines 1689–1690)

> "We remind that the local Hamiltonian terms are defined by
> $h_\gamma = \id - \Pi_{S_\gamma}$." (same paragraph)

Here the enlarged mixed interaction, which is the canonical two-site parent
of the enlarged mixed tensor on the open interval and continuous through both
endpoints, commutes with every boundary operator of the common MPO at every
parameter of the closed interval. Hence the periodic path Hamiltonian
commutes with the periodic common MPO at every length at least two.

**Scope restriction (adjoint closure):** the two-site boundary range of the
common MPO is assumed closed under conjugate transposition. The source
neither states nor proves this, and it does not follow from the exact
action decompositions, fusion decompositions, equal L matrices, or
injectivity: an explicit non-unitary involutive on-site symmetry satisfies
all of them while the canonical parent fails to commute. The source's
symmetrization, lines 1290–1320, would need a weak-Hopf integral that
Section 5 does not construct for the common MPO. See
`docs/paper-gaps/glm23_mixed_path_parent_commutation.tex`.

**Scope restriction (Z2, unitary on-site endpoints, Hermitian action gauges):**
the theorems of the section `HermitianGauge` discharge adjoint closure for
on-site endpoint operators with Hermitian on-site matrices, which covers
unitary `ℤ₂` symmetries, when both action gauges are proportional to
Hermitian matrices; the last of them derives this gauge condition for
endpoint tensors in canonical form. See
`docs/paper-gaps/glm23_mixed_path_parent_commutation.tex`, section
"Unitary on-site endpoints".

Source: Garre-Rubio–Lootens–Molnár, arXiv:2203.12563v3, Section 5,
`REsubmission.tex`, lines 1582, 1687–1692, with `defsym` and `defphase`,
lines 1240–1259.
-/

open scoped Matrix ComplexOrder

open ManyBody

namespace MPSTensor
namespace MPOSymmetry

variable {d₀ d₁ D₀ D₁ χ₀ χ₁ m N : ℕ}

section Commutation

variable (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁)
  (T₀ : MPOTensor d₀ χ₀) (T₁ : MPOTensor d₁ χ₁)
  (V₀ : Fin m → Matrix (Fin D₀) (Fin (χ₀ * D₀)) ℂ)
  (V₁ : Fin m → Matrix (Fin D₁) (Fin (χ₁ * D₁)) ℂ)
  (W₀ : Fin m → Matrix (Fin (χ₀ * D₀)) (Fin D₀) ℂ)
  (W₁ : Fin m → Matrix (Fin (χ₁ * D₁)) (Fin D₁) ℂ)

/-- On the open interval, the enlarged mixed interaction commutes with every
two-site boundary operator of the common MPO, given adjoint closure of that
boundary range. Source: arXiv:2203.12563, Section 5, lines 1687–1692. -/
theorem arbitraryPhysicalMixedInteraction_commute_mpoWithBoundary_of_mem_Ioo
    (h₀ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₀ A₀)
      (fun _ : Fin m => A₀) V₀ W₀)
    (h₁ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₁ A₁)
      (fun _ : Fin m => A₁) V₁ W₁)
    (hstar : ∀ X : Matrix (Fin (χ₀ + χ₁)) (Fin (χ₀ + χ₁)) ℂ,
      ∃ Y : Matrix (Fin (χ₀ + χ₁)) (Fin (χ₀ + χ₁)) ℂ,
        (MPOTensor.mpoWithBoundary (arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁) X 2)ᴴ =
          MPOTensor.mpoWithBoundary (arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁) Y 2)
    {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (X : Matrix (Fin (χ₀ + χ₁)) (Fin (χ₀ + χ₁)) ℂ) :
    Commute (arbitraryPhysicalMixedInteraction A₀ A₁ γ)
      (MPOTensor.mpoWithBoundary (arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁) X 2) := by
  rw [arbitraryPhysicalMixedInteraction_eq_parent_of_mem_Ioo A₀ A₁ hγ]
  exact (isBoundaryCompatible_arbitraryPhysicalMixedInterpolation A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁
    h₀ h₁ γ).parentInteraction_matrix_commute_mpoWithBoundary (by norm_num) hstar X

/-- An operator that commutes with the enlarged mixed interaction at every
parameter of the open interval commutes with it on the closed interval,
including both endpoints, because the interaction is continuous there.
Source: arXiv:2203.12563, Section 5, lines 1689–1692. -/
theorem arbitraryPhysicalMixedInteraction_commute_of_forall_mem_Ioo
    [NeZero D₀] [NeZero D₁]
    (hInj₀ : Kraus.IsInjective A₀) (hInj₁ : Kraus.IsInjective A₁)
    {B : MPOTensor.ChainOperator ((((D₀ + D₁) * (D₀ + D₁)) + d₀) + d₁) 2}
    (hB : ∀ γ ∈ Set.Ioo (0 : ℝ) 1, Commute (arbitraryPhysicalMixedInteraction A₀ A₁ γ) B)
    {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) :
    Commute (arbitraryPhysicalMixedInteraction A₀ A₁ γ) B := by
  have hf := continuous_arbitraryPhysicalMixedInteraction A₀ A₁ hInj₀ hInj₁
  have hclosed : IsClosed {t : ℝ | arbitraryPhysicalMixedInteraction A₀ A₁ t * B =
      B * arbitraryPhysicalMixedInteraction A₀ A₁ t} :=
    isClosed_eq (hf.matrix_mul continuous_const) (continuous_const.matrix_mul hf)
  rw [← closure_Ioo (zero_ne_one' ℝ)] at hγ
  exact closure_minimal (fun t ht ↦ (hB t ht).eq) hclosed hγ

/-- On the closed interval, including both endpoints where it is not the
canonical parent of the mixed tensor, the enlarged mixed interaction commutes
with every two-site boundary operator of the common MPO, given adjoint
closure of that boundary range. The endpoints follow by continuity.
Source: arXiv:2203.12563, Section 5, lines 1687–1692. -/
theorem arbitraryPhysicalMixedInteraction_commute_mpoWithBoundary
    [NeZero D₀] [NeZero D₁]
    (hInj₀ : Kraus.IsInjective A₀) (hInj₁ : Kraus.IsInjective A₁)
    (h₀ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₀ A₀)
      (fun _ : Fin m => A₀) V₀ W₀)
    (h₁ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₁ A₁)
      (fun _ : Fin m => A₁) V₁ W₁)
    (hstar : ∀ X : Matrix (Fin (χ₀ + χ₁)) (Fin (χ₀ + χ₁)) ℂ,
      ∃ Y : Matrix (Fin (χ₀ + χ₁)) (Fin (χ₀ + χ₁)) ℂ,
        (MPOTensor.mpoWithBoundary (arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁) X 2)ᴴ =
          MPOTensor.mpoWithBoundary (arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁) Y 2)
    {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (X : Matrix (Fin (χ₀ + χ₁)) (Fin (χ₀ + χ₁)) ℂ) :
    Commute (arbitraryPhysicalMixedInteraction A₀ A₁ γ)
      (MPOTensor.mpoWithBoundary (arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁) X 2) :=
  arbitraryPhysicalMixedInteraction_commute_of_forall_mem_Ioo A₀ A₁ hInj₀ hInj₁
    (fun _ ht ↦ arbitraryPhysicalMixedInteraction_commute_mpoWithBoundary_of_mem_Ioo
      A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ h₀ h₁ hstar ht X) hγ

/-- On every periodic ring of length at least two and at every parameter of
the closed interval, the enlarged mixed path Hamiltonian commutes with every
periodic boundary operator of the common MPO whose boundary commutes with
the MPO letters, given adjoint closure of the two-site boundary range.
Source: arXiv:2203.12563, Section 5, lines 1582 and 1687–1692, with
`defphase`, lines 1253–1259. -/
theorem hamiltonian_arbitraryPhysicalMixedInteraction_commute_mpoWithBoundary
    [NeZero D₀] [NeZero D₁]
    (hInj₀ : Kraus.IsInjective A₀) (hInj₁ : Kraus.IsInjective A₁)
    (h₀ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₀ A₀)
      (fun _ : Fin m => A₀) V₀ W₀)
    (h₁ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₁ A₁)
      (fun _ : Fin m => A₁) V₁ W₁)
    (hstar : ∀ X : Matrix (Fin (χ₀ + χ₁)) (Fin (χ₀ + χ₁)) ℂ,
      ∃ Y : Matrix (Fin (χ₀ + χ₁)) (Fin (χ₀ + χ₁)) ℂ,
        (MPOTensor.mpoWithBoundary (arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁) X 2)ᴴ =
          MPOTensor.mpoWithBoundary (arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁) Y 2)
    {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (hN : 2 ≤ N)
    {X : Matrix (Fin (χ₀ + χ₁)) (Fin (χ₀ + χ₁)) ℂ}
    (hX : X ∈ MPOTensor.commutingBoundaryAlgebra
      (arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁)) :
    haveI : NeZero N := ⟨by omega⟩; Commute (Interaction.translationInvariant N
        (arbitraryPhysicalMixedInteraction A₀ A₁ γ)).hamiltonian
      (MPOTensor.mpoWithBoundary (arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁) X N) :=
  haveI : NeZero N := ⟨by omega⟩; Commute.sum_left _ _ _ fun i _ =>
    MPOTensor.placeAlong_ringWindow_commute_mpoWithBoundary _ hN i _
      (arbitraryPhysicalMixedInteraction_commute_mpoWithBoundary
        A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ hInj₀ hInj₁ h₀ h₁ hstar hγ) hX

/-- On every periodic ring of length at least two and at every parameter of
the closed interval, the enlarged mixed path Hamiltonian commutes with the
periodic common MPO, given adjoint closure of its two-site boundary range.
Source: arXiv:2203.12563, Section 5, lines 1582 and 1687–1692, with
`defphase`, lines 1253–1259. -/
theorem hamiltonian_arbitraryPhysicalMixedInteraction_commute_mpo
    [NeZero D₀] [NeZero D₁]
    (hInj₀ : Kraus.IsInjective A₀) (hInj₁ : Kraus.IsInjective A₁)
    (h₀ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₀ A₀)
      (fun _ : Fin m => A₀) V₀ W₀)
    (h₁ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₁ A₁)
      (fun _ : Fin m => A₁) V₁ W₁)
    (hstar : ∀ X : Matrix (Fin (χ₀ + χ₁)) (Fin (χ₀ + χ₁)) ℂ,
      ∃ Y : Matrix (Fin (χ₀ + χ₁)) (Fin (χ₀ + χ₁)) ℂ,
        (MPOTensor.mpoWithBoundary (arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁) X 2)ᴴ =
          MPOTensor.mpoWithBoundary (arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁) Y 2)
    {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩; Commute (Interaction.translationInvariant N
        (arbitraryPhysicalMixedInteraction A₀ A₁ γ)).hamiltonian
      (MPOTensor.mpo (arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁) N) := by
  haveI : NeZero N := ⟨by omega⟩
  rw [← MPOTensor.mpoWithBoundary_one]
  exact hamiltonian_arbitraryPhysicalMixedInteraction_commute_mpoWithBoundary
    A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ hInj₀ hInj₁ h₀ h₁ hstar hγ hN (Subalgebra.one_mem _)

end Commutation

section HermitianGauge

variable (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁)
  (T₀ : MPOTensor d₀ 1) (T₁ : MPOTensor d₁ 1)
  (V₀ : Fin 1 → Matrix (Fin D₀) (Fin (1 * D₀)) ℂ)
  (V₁ : Fin 1 → Matrix (Fin D₁) (Fin (1 * D₁)) ℂ)
  (W₀ : Fin 1 → Matrix (Fin (1 * D₀)) (Fin D₀) ℂ)
  (W₁ : Fin 1 → Matrix (Fin (1 * D₁)) (Fin D₁) ℂ)

/-- On the closed interval, the enlarged mixed interaction commutes with every
two-site boundary operator of the common operator of on-site endpoint
symmetries with Hermitian on-site matrices, as for unitary `ℤ₂` symmetries,
when both action gauges are proportional to Hermitian matrices.
Source: arXiv:2203.12563, Section 5, lines 1687–1692, and
`docs/paper-gaps/glm23_mixed_path_parent_commutation.tex`, paragraph
"When closure holds". -/
theorem arbitraryPhysicalMixedInteraction_commute_mpoWithBoundary_of_isHermitian
    [NeZero D₀] [NeZero D₁]
    (hInj₀ : Kraus.IsInjective A₀) (hInj₁ : Kraus.IsInjective A₁)
    (hu₀ : (MPOTensor.physicalSlice T₀ 0 0).IsHermitian)
    (hu₁ : (MPOTensor.physicalSlice T₁ 0 0).IsHermitian)
    (h₀ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₀ A₀)
      (fun _ : Fin 1 => A₀) V₀ W₀)
    (h₁ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₁ A₁)
      (fun _ : Fin 1 => A₁) V₁ W₁)
    (hY₀ : ∃ c : ℂ, c ≠ 0 ∧ (c • bondOneActionGauge (W₀ 0)).IsHermitian)
    (hY₁ : ∃ c : ℂ, c ≠ 0 ∧ (c • bondOneActionGauge (W₁ 0)).IsHermitian)
    {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (X : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ) :
    Commute (arbitraryPhysicalMixedInteraction A₀ A₁ γ)
      (MPOTensor.mpoWithBoundary (arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁) X 2) :=
  arbitraryPhysicalMixedInteraction_commute_mpoWithBoundary A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁
    hInj₀ hInj₁ h₀ h₁ (fun X ↦ exists_conjTranspose_mpoWithBoundary_arbitraryPhysicalMixedMPO_eq
      A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ hu₀ hu₁ h₀ h₁ hY₀ hY₁ X 2) hγ X

/-- On every periodic ring of length at least two and at every parameter of
the closed interval, the enlarged mixed path Hamiltonian commutes with every
periodic boundary operator, with boundary commuting with the letters, of the
common operator of on-site endpoint symmetries with Hermitian on-site
matrices, when both action gauges are proportional to Hermitian matrices.
Source: arXiv:2203.12563, Section 5, lines 1582 and 1687–1692, and
`docs/paper-gaps/glm23_mixed_path_parent_commutation.tex`, paragraph
"When closure holds". -/
theorem
    interactionHamiltonian_arbitraryPhysicalMixedInteraction_commute_mpoWithBoundary_of_isHermitian
    [NeZero D₀] [NeZero D₁]
    (hInj₀ : Kraus.IsInjective A₀) (hInj₁ : Kraus.IsInjective A₁)
    (hu₀ : (MPOTensor.physicalSlice T₀ 0 0).IsHermitian)
    (hu₁ : (MPOTensor.physicalSlice T₁ 0 0).IsHermitian)
    (h₀ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₀ A₀)
      (fun _ : Fin 1 => A₀) V₀ W₀)
    (h₁ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₁ A₁)
      (fun _ : Fin 1 => A₁) V₁ W₁)
    (hY₀ : ∃ c : ℂ, c ≠ 0 ∧ (c • bondOneActionGauge (W₀ 0)).IsHermitian)
    (hY₁ : ∃ c : ℂ, c ≠ 0 ∧ (c • bondOneActionGauge (W₁ 0)).IsHermitian)
    {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (hN : 2 ≤ N)
    {X : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ}
    (hX : X ∈ MPOTensor.commutingBoundaryAlgebra
      (arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁)) :
    haveI : NeZero N := ⟨by omega⟩; Commute (Interaction.translationInvariant N
        (arbitraryPhysicalMixedInteraction A₀ A₁ γ)).hamiltonian
      (MPOTensor.mpoWithBoundary (arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁) X N) :=
  haveI : NeZero N := ⟨by omega⟩;
  hamiltonian_arbitraryPhysicalMixedInteraction_commute_mpoWithBoundary
    A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ hInj₀ hInj₁ h₀ h₁
    (fun X ↦ exists_conjTranspose_mpoWithBoundary_arbitraryPhysicalMixedMPO_eq
      A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ hu₀ hu₁ h₀ h₁ hY₀ hY₁ X 2) hγ hN hX

/-- On every periodic ring of length at least two and at every parameter of
the closed interval, the enlarged mixed path Hamiltonian commutes with the
periodic common operator of on-site endpoint symmetries with Hermitian
on-site matrices, when both action gauges are proportional to Hermitian
matrices. Source: arXiv:2203.12563, Section 5, lines 1582 and 1687–1692,
and `docs/paper-gaps/glm23_mixed_path_parent_commutation.tex`, paragraph
"When closure holds". -/
theorem hamiltonian_arbitraryPhysicalMixedInteraction_commute_mpo_of_isHermitian
    [NeZero D₀] [NeZero D₁]
    (hInj₀ : Kraus.IsInjective A₀) (hInj₁ : Kraus.IsInjective A₁)
    (hu₀ : (MPOTensor.physicalSlice T₀ 0 0).IsHermitian)
    (hu₁ : (MPOTensor.physicalSlice T₁ 0 0).IsHermitian)
    (h₀ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₀ A₀)
      (fun _ : Fin 1 => A₀) V₀ W₀)
    (h₁ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₁ A₁)
      (fun _ : Fin 1 => A₁) V₁ W₁)
    (hY₀ : ∃ c : ℂ, c ≠ 0 ∧ (c • bondOneActionGauge (W₀ 0)).IsHermitian)
    (hY₁ : ∃ c : ℂ, c ≠ 0 ∧ (c • bondOneActionGauge (W₁ 0)).IsHermitian)
    {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩; Commute (Interaction.translationInvariant N
        (arbitraryPhysicalMixedInteraction A₀ A₁ γ)).hamiltonian
      (MPOTensor.mpo (arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁) N) :=
  haveI : NeZero N := ⟨by omega⟩; hamiltonian_arbitraryPhysicalMixedInteraction_commute_mpo
    A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ hInj₀ hInj₁ h₀ h₁
    (fun X ↦ exists_conjTranspose_mpoWithBoundary_arbitraryPhysicalMixedMPO_eq
      A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ hu₀ hu₁ h₀ h₁ hY₀ hY₁ X 2) hγ hN

/-- **Unitary `ℤ₂` endpoints in canonical form.** Let both endpoint tensors
be injective with `E(1) = 1` and a positive definite fixed point of the
adjoint transfer map, and let on-site unitaries `u_p` with `u_p² = 1` act on
them. Then, on every periodic ring of length at least two and at every
parameter of the closed interval, the enlarged mixed path Hamiltonian
commutes with the periodic common operator. Source: arXiv:2203.12563,
Section 5, lines 1582 and 1687–1692; arXiv:0802.0447, Lemma 1 and
Theorem 2; and `docs/paper-gaps/glm23_mixed_path_parent_commutation.tex`,
paragraph "When closure holds". -/
theorem hamiltonian_arbitraryPhysicalMixedInteraction_commute_mpo_of_canonical
    [NeZero D₀] [NeZero D₁]
    (hInj₀ : Kraus.IsInjective A₀) (hInj₁ : Kraus.IsInjective A₁)
    (hNorm₀ : Kraus.transferMap A₀ 1 = 1) (hNorm₁ : Kraus.transferMap A₁ 1 = 1)
    {Λ₀ : Matrix (Fin D₀) (Fin D₀) ℂ} {Λ₁ : Matrix (Fin D₁) (Fin D₁) ℂ}
    (hΛ₀ : Λ₀.PosDef) (hΛ₁ : Λ₁.PosDef)
    (hΛfix₀ : Kraus.transferMap (fun i => (A₀ i)ᴴ) Λ₀ = Λ₀)
    (hΛfix₁ : Kraus.transferMap (fun i => (A₁ i)ᴴ) Λ₁ = Λ₁)
    (hu₀ : MPOTensor.physicalSlice T₀ 0 0 ∈ Matrix.unitaryGroup (Fin d₀) ℂ)
    (hu₁ : MPOTensor.physicalSlice T₁ 0 0 ∈ Matrix.unitaryGroup (Fin d₁) ℂ)
    (hu₀2 : MPOTensor.physicalSlice T₀ 0 0 * MPOTensor.physicalSlice T₀ 0 0 = 1)
    (hu₁2 : MPOTensor.physicalSlice T₁ 0 0 * MPOTensor.physicalSlice T₁ 0 0 = 1)
    (h₀ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₀ A₀)
      (fun _ : Fin 1 => A₀) V₀ W₀)
    (h₁ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₁ A₁)
      (fun _ : Fin 1 => A₁) V₁ W₁)
    {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩; Commute (Interaction.translationInvariant N
        (arbitraryPhysicalMixedInteraction A₀ A₁ γ)).hamiltonian
      (MPOTensor.mpo (arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁) N) :=
  haveI : NeZero N := ⟨by omega⟩;
  hamiltonian_arbitraryPhysicalMixedInteraction_commute_mpo_of_isHermitian
    A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ hInj₀ hInj₁
    (Matrix.isHermitian_of_mem_unitaryGroup_of_mul_self_eq_one hu₀ hu₀2)
    (Matrix.isHermitian_of_mem_unitaryGroup_of_mul_self_eq_one hu₁ hu₁2) h₀ h₁
    (exists_isHermitian_smul_bondOneActionGauge hInj₀ hNorm₀ hΛ₀ hΛfix₀ hu₀ hu₀2 h₀)
    (exists_isHermitian_smul_bondOneActionGauge hInj₁ hNorm₁ hΛ₁ hΛfix₁ hu₁ hu₁2 h₁) hγ hN

end HermitianGauge

end MPOSymmetry
end MPSTensor
