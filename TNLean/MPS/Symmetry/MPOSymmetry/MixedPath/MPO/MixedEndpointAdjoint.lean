/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Operator.Boundary.NormalAdjointBoundary
import TNLean.MPS.Symmetry.MPOSymmetry.MixedPath.MPO.ArbitraryPhysicalMixedHermitianGauge
import TNLean.MPS.Symmetry.MPOSymmetry.MixedPath.MPO.ArbitraryPhysicalMixedParentCommutation

/-!
# Physical adjoints of the mixed endpoint operator

Endpoint physical adjoint identities extend to the mixed operator when the
individual virtual slices of the action maps obey the same adjoint identities.
This is an explicit local criterion, stronger than closure of the endpoint
boundary ranges. It applies to dual pairs as well as self-adjoint data.

**Scope restriction (action-map adjoints):** the extra identities on the action
maps are not inferred from unitary endpoint operators. The mixed sectors retain
these maps even when a nonunitary virtual gauge is invisible in the physical
endpoint symmetry. See `docs/paper-gaps/glm23_mixed_endpoint_adjoint.tex`.

Source context: arXiv:2203.12563v3, Section 5, the mixed sectors preceding
`Agammasym`, lines 1600–1631. These are sufficient criteria, not source claims.

## Mixed parent commutation from endpoint adjoint identities

The local endpoint adjoint criterion supplies the two-site boundary closure
required by the mixed canonical parent. The conclusions hold on the closed
parameter interval, including its limiting interactions at the endpoints.

**Scope restriction (action-map adjoints):** self-adjoint physical slices and
self-adjoint fixed-MPO-index slices of all action maps are required. Endpoint
unitarity alone does not imply this criterion or the needed boundary closure.
See `docs/paper-gaps/glm23_mixed_endpoint_adjoint.tex` and
`docs/paper-gaps/glm23_mixed_path_parent_commutation.tex`.

Source context: arXiv:2203.12563v3, Section 5, lines 1687–1692.
-/

section

open scoped Matrix BigOperators

namespace MPSTensor.MPOSymmetry

variable {D₀ D₁ χ₀ χ₁ m : ℕ}

/-- The mixed operator respects a physical adjoint pair if both endpoint
operators and every fixed-MPO-index slice of their analysis and synthesis
maps respect that pair. The bond indices are not transposed. -/
theorem physicalAdjointTensor_mixedEndpointMPO
    (T₀ T₀' : MPOTensor (D₀ * D₀) χ₀) (T₁ T₁' : MPOTensor (D₁ * D₁) χ₁)
    (V₀ V₀' : Fin m → Matrix (Fin D₀) (Fin (χ₀ * D₀)) ℂ)
    (V₁ V₁' : Fin m → Matrix (Fin D₁) (Fin (χ₁ * D₁)) ℂ)
    (W₀ W₀' : Fin m → Matrix (Fin (χ₀ * D₀)) (Fin D₀) ℂ)
    (W₁ W₁' : Fin m → Matrix (Fin (χ₁ * D₁)) (Fin D₁) ℂ)
    (hT₀ : MPOTensor.physicalAdjointTensor T₀ = T₀')
    (hT₁ : MPOTensor.physicalAdjointTensor T₁ = T₁')
    (hV₀ : ∀ μ α r s, star (V₀ μ s (finProdFinEquiv (α, r))) =
      V₀' μ r (finProdFinEquiv (α, s)))
    (hV₁ : ∀ μ α r s, star (V₁ μ s (finProdFinEquiv (α, r))) =
      V₁' μ r (finProdFinEquiv (α, s)))
    (hW₀ : ∀ μ α r s, star (W₀ μ (finProdFinEquiv (α, s)) r) =
      W₀' μ (finProdFinEquiv (α, r)) s)
    (hW₁ : ∀ μ α r s, star (W₁ μ (finProdFinEquiv (α, s)) r) =
      W₁' μ (finProdFinEquiv (α, r)) s) :
    MPOTensor.physicalAdjointTensor (mixedEndpointMPO T₀ T₁ V₀ V₁ W₀ W₁) =
      mixedEndpointMPO T₀' T₁' V₀' V₁' W₀' W₁' := by
  have ht₀ : ∀ i j α β, star (T₀ (j, i) α β) = T₀' (i, j) α β :=
    fun i j α β => congrArg (fun T => T (i, j) α β) hT₀
  have ht₁ : ∀ i j α β, star (T₁ (j, i) α β) = T₁' (i, j) α β :=
    fun i j α β => congrArg (fun T => T (i, j) α β) hT₁
  ext ⟨i, j⟩ α β
  obtain ⟨⟨r, s⟩, rfl⟩ := (mixedEndpointPhysicalEquiv D₀ D₁).surjective i
  obtain ⟨⟨k, l⟩, rfl⟩ := (mixedEndpointPhysicalEquiv D₀ D₁).surjective j
  obtain ⟨α, rfl⟩ := finSumFinEquiv.surjective α
  obtain ⟨β, rfl⟩ := finSumFinEquiv.surjective β
  simp only [MPOTensor.physicalAdjointTensor_apply, mixedEndpointMPO_physicalEquiv,
    Matrix.submatrix_apply, Equiv.symm_apply_apply]
  cases r <;> cases s <;> cases k <;> cases l <;> cases α <;> cases β <;>
    simp [mixedEndpointMPOLetter, ht₀, ht₁, hV₀, hV₁, hW₀, hW₁, mul_comm]

section SelfAdjoint

variable {d₀ d₁ : ℕ}
  (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁)
  (T₀ : MPOTensor d₀ χ₀) (T₁ : MPOTensor d₁ χ₁)
  (V₀ : Fin m → Matrix (Fin D₀) (Fin (χ₀ * D₀)) ℂ)
  (V₁ : Fin m → Matrix (Fin D₁) (Fin (χ₁ * D₁)) ℂ)
  (W₀ : Fin m → Matrix (Fin (χ₀ * D₀)) (Fin D₀) ℂ)
  (W₁ : Fin m → Matrix (Fin (χ₁ * D₁)) (Fin D₁) ℂ)
  (hT₀ : MPOTensor.physicalAdjointTensor T₀ = T₀)
  (hT₁ : MPOTensor.physicalAdjointTensor T₁ = T₁)
  (hV₀ : ∀ μ α r s, star (V₀ μ s (finProdFinEquiv (α, r))) =
    V₀ μ r (finProdFinEquiv (α, s)))
  (hV₁ : ∀ μ α r s, star (V₁ μ s (finProdFinEquiv (α, r))) =
    V₁ μ r (finProdFinEquiv (α, s)))
  (hW₀ : ∀ μ α r s, star (W₀ μ (finProdFinEquiv (α, s)) r) =
    W₀ μ (finProdFinEquiv (α, r)) s)
  (hW₁ : ∀ μ α r s, star (W₁ μ (finProdFinEquiv (α, s)) r) =
    W₁ μ (finProdFinEquiv (α, r)) s)

include hT₀ hT₁ hV₀ hV₁ hW₀ hW₁ in
/-- Self-adjoint physical slices at the endpoints and self-adjoint virtual
slices of the action maps make the arbitrary-alphabet common tensor fixed
by the physical adjoint. Polar compression requires no extra hypothesis. -/
theorem physicalAdjointTensor_arbitraryPhysicalMixedMPO :
    MPOTensor.physicalAdjointTensor
        (arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁) =
      arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ := by
  unfold arbitraryPhysicalMixedMPO
  rw [MPOTensor.physicalAdjointTensor_changePhysicalBasis]
  congr 1
  exact physicalAdjointTensor_mixedEndpointMPO _ _ _ _ _ _ _ _ _ _ _ _
    (by simp only [polarSupportMPO,
      MPOTensor.physicalAdjointTensor_changePhysicalBasis, hT₀])
    (by simp only [polarSupportMPO,
      MPOTensor.physicalAdjointTensor_changePhysicalBasis, hT₁])
    hV₀ hV₁ hW₀ hW₁

include hT₀ hT₁ hV₀ hV₁ hW₀ hW₁ in
/-- Under the local endpoint adjoint criterion, the adjoint boundary is
entrywise complex conjugation at every length, including the empty chain.
In particular, this supplies the two-site closure used by the mixed parent. -/
theorem conjTranspose_mpoWithBoundary_arbitraryPhysicalMixedMPO
    (X : Matrix (Fin (χ₀ + χ₁)) (Fin (χ₀ + χ₁)) ℂ) (N : ℕ) :
    (MPOTensor.mpoWithBoundary
        (arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁) X N)ᴴ =
      MPOTensor.mpoWithBoundary
        (arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁)
        (X.map (starRingEnd ℂ)) N := by
  rw [MPOTensor.conjTranspose_mpoWithBoundary,
    physicalAdjointTensor_arbitraryPhysicalMixedMPO
      A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ hT₀ hT₁ hV₀ hV₁ hW₀ hW₁]

end SelfAdjoint

end MPSTensor.MPOSymmetry

end

section

open scoped Matrix

open ManyBody

namespace MPSTensor.MPOSymmetry

variable {d₀ d₁ D₀ D₁ χ₀ χ₁ m : ℕ}
  (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁)
  (T₀ : MPOTensor d₀ χ₀) (T₁ : MPOTensor d₁ χ₁)
  (V₀ : Fin m → Matrix (Fin D₀) (Fin (χ₀ * D₀)) ℂ)
  (V₁ : Fin m → Matrix (Fin D₁) (Fin (χ₁ * D₁)) ℂ)
  (W₀ : Fin m → Matrix (Fin (χ₀ * D₀)) (Fin D₀) ℂ)
  (W₁ : Fin m → Matrix (Fin (χ₁ * D₁)) (Fin D₁) ℂ)
  (hT₀ : MPOTensor.physicalAdjointTensor T₀ = T₀)
  (hT₁ : MPOTensor.physicalAdjointTensor T₁ = T₁)
  (hV₀ : ∀ μ α r s, star (V₀ μ s (finProdFinEquiv (α, r))) =
    V₀ μ r (finProdFinEquiv (α, s)))
  (hV₁ : ∀ μ α r s, star (V₁ μ s (finProdFinEquiv (α, r))) =
    V₁ μ r (finProdFinEquiv (α, s)))
  (hW₀ : ∀ μ α r s, star (W₀ μ (finProdFinEquiv (α, s)) r) =
    W₀ μ (finProdFinEquiv (α, r)) s)
  (hW₁ : ∀ μ α r s, star (W₁ μ (finProdFinEquiv (α, s)) r) =
    W₁ μ (finProdFinEquiv (α, r)) s)
  [NeZero D₀] [NeZero D₁]
  (hInj₀ : Kraus.IsInjective A₀) (hInj₁ : Kraus.IsInjective A₁)
  (h₀ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₀ A₀)
    (fun _ : Fin m => A₀) V₀ W₀)
  (h₁ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₁ A₁)
    (fun _ : Fin m => A₁) V₁ W₁)

include hT₀ hT₁ hV₀ hV₁ hW₀ hW₁ hInj₀ hInj₁ h₀ h₁

/-- Endpoint slice adjoints discharge the boundary-closure hypothesis for the
mixed interaction at every parameter of the closed interval. -/
theorem arbitraryPhysicalMixedInteraction_commute_of_endpoint_adjoint
    {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (X : Matrix (Fin (χ₀ + χ₁)) (Fin (χ₀ + χ₁)) ℂ) :
    Commute (arbitraryPhysicalMixedInteraction A₀ A₁ γ)
      (MPOTensor.mpoWithBoundary
        (arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁) X 2) := by
  apply arbitraryPhysicalMixedInteraction_commute_mpoWithBoundary
    A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ hInj₀ hInj₁ h₀ h₁ _ hγ X
  intro Y
  exact ⟨Y.map (starRingEnd ℂ),
    conjTranspose_mpoWithBoundary_arbitraryPhysicalMixedMPO
      A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ hT₀ hT₁ hV₀ hV₁ hW₀ hW₁ Y 2⟩

/-- Under endpoint slice adjoints, every periodic mixed path Hamiltonian of
length at least two commutes with the periodic common MPO. -/
theorem hamiltonian_arbitraryPhysicalMixedInteraction_commute_of_endpoint_adjoint
    {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) {N : ℕ} (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩; Commute (Interaction.translationInvariant N
        (arbitraryPhysicalMixedInteraction A₀ A₁ γ)).hamiltonian
      (MPOTensor.mpo (arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁) N) := by
  have : NeZero N := ⟨by omega⟩
  apply hamiltonian_arbitraryPhysicalMixedInteraction_commute_mpo
    A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ hInj₀ hInj₁ h₀ h₁ _ hγ hN
  intro Y
  exact ⟨Y.map (starRingEnd ℂ),
    conjTranspose_mpoWithBoundary_arbitraryPhysicalMixedMPO
      A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ hT₀ hT₁ hV₀ hV₁ hW₀ hW₁ Y 2⟩

end MPSTensor.MPOSymmetry

end
