/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.BlockedPolar
import TNLean.MPS.Symmetry.CommonPhysicalFixedPointGroundPath
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointPeriodicStateContinuity

/-!
# Mixed interpolation for arbitrary physical alphabets

The positive polar factors of two injective tensors have square physical
alphabets. Their mixed interpolation therefore defines a path in one common
physical space after an isometric inclusion. At each endpoint its periodic
vector is exactly that of the corresponding original tensor under its full
physical embedding, for every positive chain length.

The endpoint statements compare periodic vectors. The mixed endpoint letters
can retain off-diagonal virtual blocks, and their bond dimension need not
equal that of the original endpoint.

Source: Garre-Rubio–Lootens–Molnár, arXiv:2203.12563, Section 5,
`defAgamma`, lines 1586–1601 and 1687–1692. The polar-factor construction is
the tensor polar decomposition of arXiv:2307.01696, `eq:key_approximation`.
-/

open scoped BigOperators Matrix Topology

namespace MPSTensor

/-- The positive polar factor of an injective tensor is injective, because
physical mixing by its polar isometry recovers the original tensor.
Source context: arXiv:2307.01696, `eq:key_approximation`. -/
theorem isInjective_polarPosTensor {d D : ℕ} {A : MPSTensor d D}
    (hA : Kraus.IsInjective A) : Kraus.IsInjective (polarPosTensor A) := by
  apply isInjective_of_kraus_mixing_isInjective (polarPosTensor A) (polarIsoMatrix A)
  change Kraus.IsInjective (rotatePhysical (polarIsoMatrix A) (polarPosTensor A))
  rwa [rotatePhysical_polarIsoMatrix_polarPosTensor]

private theorem eq_rotatePhysical_coordinateInclusion_of_apply
    {d m D : ℕ} (A : MPSTensor d D) (B : MPSTensor m D) (e : Fin d ↪ Fin m)
    (hon : ∀ q, B (e q) = A q) (hoff : ∀ p, p ∉ Set.range e → B p = 0) :
    B = rotatePhysical (Matrix.coordinateInclusion e) A := by
  classical
  funext p
  by_cases hp : p ∈ Set.range e
  · obtain ⟨q, rfl⟩ := hp
    rw [hon]
    simp [rotatePhysical, Matrix.coordinateInclusion, e.injective.eq_iff]
  · rw [hoff p hp]
    simp [rotatePhysical, Matrix.coordinateInclusion,
      show ∀ q, p ≠ e q from fun q h => hp ⟨q, h.symm⟩]

namespace MPOSymmetry

variable {d₀ d₁ D₀ D₁ N : ℕ}

/-- Extending the first square-alphabet tensor by zero is the physical
coordinate inclusion of the first diagonal sector.
Source: arXiv:2203.12563, Section 5, `defAgamma`, lines 1586–1601. -/
theorem mixedEndpointLeftTensor_eq_rotatePhysical
    (A₀ : MPSTensor (D₀ * D₀) D₀) (D₁ : ℕ) :
    mixedEndpointLeftTensor A₀ D₁ =
      rotatePhysical
        (Matrix.coordinateInclusion (sptPhysicalEmbedding (Fin.castAddEmb D₁))) A₀ := by
  apply eq_rotatePhysical_coordinateInclusion_of_apply
  · intro p
    obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective p
    simp [mixedEndpointLeftTensor, sptPhysicalEmbedding]
  · intro p hp
    obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective p
    obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective a
    obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective b
    rcases a with a | a <;> rcases b with b | b
    · exact (hp ⟨finProdFinEquiv (a, b), by simp [sptPhysicalEmbedding]⟩).elim
    all_goals simp [mixedEndpointLeftTensor]

/-- Extending the second square-alphabet tensor by zero is the physical
coordinate inclusion of the second diagonal sector.
Source: arXiv:2203.12563, Section 5, `defAgamma`, lines 1586–1601. -/
theorem mixedEndpointRightTensor_eq_rotatePhysical
    (A₁ : MPSTensor (D₁ * D₁) D₁) (D₀ : ℕ) :
    mixedEndpointRightTensor A₁ D₀ =
      rotatePhysical
        (Matrix.coordinateInclusion (sptPhysicalEmbedding (Fin.natAddEmb D₀))) A₁ := by
  apply eq_rotatePhysical_coordinateInclusion_of_apply
  · intro p
    obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective p
    simp [mixedEndpointRightTensor_apply, sptPhysicalEmbedding]
  · intro p hp
    obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective p
    obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective a
    obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective b
    rcases a with a | a <;> rcases b with b | b
    · simp [mixedEndpointRightTensor_apply]
    · simp [mixedEndpointRightTensor_apply]
    · simp [mixedEndpointRightTensor_apply]
    · exact (hp ⟨finProdFinEquiv (a, b), by simp [sptPhysicalEmbedding]⟩).elim

/-- The embedded first positive polar factor recovers the full physical
embedding of the original first tensor.
Source context: arXiv:2203.12563, Section 5, `defAgamma`. -/
theorem rotatePhysical_mixedEndpointLeftTensor_polarPosTensor
    (d₁ D₁ : ℕ) {A₀ : MPSTensor d₀ D₀} (h₀ : Kraus.IsInjective A₀) :
    rotatePhysical (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁)
        (mixedEndpointLeftTensor (polarPosTensor A₀) D₁) =
      rotatePhysical (commonPhysicalEmbeddingLeft d₁ D₁ A₀) A₀ := by
  rw [mixedEndpointLeftTensor_eq_rotatePhysical, rotatePhysical_rotatePhysical,
    ← commonPhysicalEmbeddingLeft_mul_polarIsoMatrix d₁ D₁ h₀,
    ← rotatePhysical_rotatePhysical, rotatePhysical_polarIsoMatrix_polarPosTensor]

/-- The embedded second positive polar factor recovers the full physical
embedding of the original second tensor.
Source context: arXiv:2203.12563, Section 5, `defAgamma`. -/
theorem rotatePhysical_mixedEndpointRightTensor_polarPosTensor
    (d₀ D₀ : ℕ) {A₁ : MPSTensor d₁ D₁} (h₁ : Kraus.IsInjective A₁) :
    rotatePhysical (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁)
        (mixedEndpointRightTensor (polarPosTensor A₁) D₀) =
      rotatePhysical (commonPhysicalEmbeddingRight d₀ D₀ A₁) A₁ := by
  rw [mixedEndpointRightTensor_eq_rotatePhysical, rotatePhysical_rotatePhysical,
    ← commonPhysicalEmbeddingRight_mul_polarIsoMatrix d₀ D₀ h₁,
    ← rotatePhysical_rotatePhysical, rotatePhysical_polarIsoMatrix_polarPosTensor]

/-- The mixed interpolation of the positive polar factors, included in a
common physical space containing the two original alphabets.
Source: arXiv:2203.12563, Section 5, `defAgamma`, lines 1586–1601. -/
noncomputable def arbitraryPhysicalMixedInterpolation
    (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁) (γ : ℝ) :
    MPSTensor (((D₀ + D₁) * (D₀ + D₁) + d₀) + d₁) (D₀ + D₁) :=
  rotatePhysical (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁)
    (mixedEndpointInterpolation (polarPosTensor A₀) (polarPosTensor A₁) γ)

/-- The arbitrary-alphabet mixed tensor varies continuously on the real
line. Source: arXiv:2203.12563, Section 5, `defAgamma`. -/
theorem continuous_arbitraryPhysicalMixedInterpolation
    (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁) :
    Continuous (arbitraryPhysicalMixedInterpolation A₀ A₁) :=
  (continuous_rotatePhysical _).comp (continuous_mixedEndpointInterpolation _ _)

/-- The common-space mixed tensor is injective at every interior parameter.
Source: arXiv:2203.12563, Section 5, line 1691. -/
theorem isInjective_arbitraryPhysicalMixedInterpolation
    (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)
    {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    Kraus.IsInjective (arbitraryPhysicalMixedInterpolation A₀ A₁ γ) :=
  isInjective_kraus_isometry _ _ (commonFixedPointInclusion_isometry _ _ _)
    (isInjective_mixedEndpointInterpolation _ _
      (isInjective_polarPosTensor h₀) (isInjective_polarPosTensor h₁) hγ)

/-- At zero, the periodic vector is exactly that of the embedded original
first tensor at every positive length. The larger mixed bond space is
retained in the tensor path. Source: arXiv:2203.12563, Section 5,
`defAgamma`, lines 1586–1601. -/
theorem mpv_arbitraryPhysicalMixedInterpolation_zero
    (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁)
    (h₀ : Kraus.IsInjective A₀) (hN : 0 < N) :
    (mpv (arbitraryPhysicalMixedInterpolation A₀ A₁ 0) :
      NSiteSpace (((D₀ + D₁) * (D₀ + D₁) + d₀) + d₁) N) =
      mpv (rotatePhysical (commonPhysicalEmbeddingLeft d₁ D₁ A₀) A₀) := by
  rw [← rotatePhysical_mixedEndpointLeftTensor_polarPosTensor d₁ D₁ h₀]
  funext σ
  simp only [arbitraryPhysicalMixedInterpolation, mpv_rotatePhysical]
  rw [mpv_mixedEndpointInterpolation_zero _ _ hN]

/-- At one, the periodic vector is exactly that of the embedded original
second tensor at every positive length. Source: arXiv:2203.12563,
Section 5, `defAgamma`, lines 1586–1601. -/
theorem mpv_arbitraryPhysicalMixedInterpolation_one
    (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁)
    (h₁ : Kraus.IsInjective A₁) (hN : 0 < N) :
    (mpv (arbitraryPhysicalMixedInterpolation A₀ A₁ 1) :
      NSiteSpace (((D₀ + D₁) * (D₀ + D₁) + d₀) + d₁) N) =
      mpv (rotatePhysical (commonPhysicalEmbeddingRight d₀ D₀ A₁) A₁) := by
  rw [← rotatePhysical_mixedEndpointRightTensor_polarPosTensor d₀ D₀ h₁]
  funext σ
  simp only [arbitraryPhysicalMixedInterpolation, mpv_rotatePhysical]
  rw [mpv_mixedEndpointInterpolation_one _ _ hN]

/-- The periodic vector of the common-space interpolation never vanishes
on the closed interval for rings of length at least two.
Source: arXiv:2203.12563, Section 5, lines 1687–1692. -/
theorem mpv_arbitraryPhysicalMixedInterpolation_ne_zero [NeZero D₀] [NeZero D₁]
    (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)
    (γ : unitInterval) (hN : 2 ≤ N) :
    (mpv (arbitraryPhysicalMixedInterpolation A₀ A₁ γ) :
      NSiteSpace (((D₀ + D₁) * (D₀ + D₁) + d₀) + d₁) N) ≠ 0 :=
  mpv_rotatePhysical_isometry_ne_zero _ (commonFixedPointInclusion_isometry _ _ _) _
    (mpv_mixedEndpointInterpolation_ne_zero _ _
      (isInjective_polarPosTensor h₀) (isInjective_polarPosTensor h₁) γ hN)

end MPOSymmetry
end MPSTensor
