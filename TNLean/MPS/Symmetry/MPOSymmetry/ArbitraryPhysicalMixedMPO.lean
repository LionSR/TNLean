/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalBasisAction
import TNLean.MPS.Symmetry.MPOSymmetry.ArbitraryPhysicalMixedInterpolation
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointMPOAction
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointMPOFusion

/-!
# The common MPO symmetry of the arbitrary-alphabet mixed path

GLM23 begins its interpolation by restricting each local physical space to
the span of the virtual MPS tensor, so that it becomes `ℂ^{D_p} ⊗ ℂ^{D_p}`.
For a tensor `A_p` with an arbitrary physical alphabet, this restriction is
the polar factorization `A_p = F_p B_p`. Each endpoint operator `T` is
compressed to `F_pᴴ T F_p` on the physical legs.

An exact action decomposition of `T` on `A_p` compresses to one on `B_p`
with the same action maps; no injectivity is needed. When `A_p` is
one-site injective, the letters of `B_p` are linearly independent, and the
action decomposition itself forces `T` to preserve the physical support of
`A_p`. Fusion decompositions therefore compress as well. The restriction of
the source is thus derived, not imposed.

The square-alphabet mixed operator of the compressed endpoints is included
in the common physical space by the same isometry `J` that includes the
mixed tensor. Its exact action on the enlarged mixed tensor holds at every
real parameter, including both endpoints. At the endpoints, the periodic
states of the fully embedded original tensors are eigenvectors with the
common action multiplicity. Equal chosen raw L matrices give exact fusion
with the original multiplicities. The action maps are literally those of
the square-alphabet construction, so the L-symbol identities of that
construction apply verbatim.

Hamiltonian commutation, operator injectivity in the enlarged space, and
the degenerate ground-space construction are not asserted here.

Source: Garre-Rubio–Lootens–Molnár, arXiv:2203.12563v3, Section 5,
`REsubmission.tex`, lines 1584–1586 (physical restriction), `defAgamma`,
`Agammasym`, lines 1586–1665, and the fusion discussion at lines 1667–1685.
-/

open scoped Matrix BigOperators

open MPOTensor.PhysicalSectorFactorization (changePhysicalBasis)

namespace MPSTensor

variable {d D χ : ℕ}

/-- The adjoint polar isometry recovers the positive polar tensor; no
injectivity is needed. Source context: arXiv:2307.01696,
`eq:key_approximation`. -/
theorem rotatePhysical_conjTranspose_polarIsoMatrix (A : MPSTensor d D) :
    rotatePhysical (polarIsoMatrix A)ᴴ A = polarPosTensor A := by
  calc rotatePhysical (polarIsoMatrix A)ᴴ A =
        rotatePhysical (polarIsoMatrix A)ᴴ
          (rotatePhysical (polarIsoMatrix A) (polarPosTensor A)) := by
        rw [rotatePhysical_polarIsoMatrix_polarPosTensor]
    _ = polarPosTensor A := by
        rw [rotatePhysical_rotatePhysical, conjTranspose_polarIsoMatrix_mul_polarIsoMatrix,
          rotatePhysical_polarSupportMatrix]

/-- The polar support projection fixes the original tensor. Source context:
arXiv:2307.01696, `eq:key_approximation`. -/
theorem rotatePhysical_polarIsoMatrix_mul_conjTranspose (A : MPSTensor d D) :
    rotatePhysical (polarIsoMatrix A * (polarIsoMatrix A)ᴴ) A = A := by
  rw [← rotatePhysical_rotatePhysical, rotatePhysical_conjTranspose_polarIsoMatrix,
    rotatePhysical_polarIsoMatrix_polarPosTensor]

/-- The `D²` letters of the positive polar tensor of a one-site injective
tensor are linearly independent. Source context: arXiv:2203.12563,
lines 1584–1586, and arXiv:2307.01696, `eq:key_approximation`. -/
theorem linearIndependent_polarPosTensor {A : MPSTensor d D} (hA : Kraus.IsInjective A) :
    LinearIndependent ℂ (polarPosTensor A) :=
  linearIndependent_of_top_le_span_of_card_eq_finrank (isInjective_polarPosTensor hA).ge
    (by simp [Module.finrank_matrix])

/-- The compression of an operator tensor to the physical support of `A`,
`F T F` with the adjoint polar isometry `F` on the outgoing leg. Source:
arXiv:2203.12563, Section 5, lines 1584–1586. -/
noncomputable def polarSupportMPO (A : MPSTensor d D) (T : MPOTensor d χ) :
    MPOTensor (D * D) χ :=
  changePhysicalBasis (polarIsoMatrix A)ᴴ T

/-- An exact action decomposition of an operator on a tensor compresses to
the positive polar tensor with the same action maps. Injectivity is not
needed. Source: arXiv:2203.12563, lines 1584–1586, with `fusiontensors2`
and `eq:orthoV`. -/
theorem isBiorthogonalDecomposition_polarSupportMPO {ι : Type*} [Fintype ι]
    {A : MPSTensor d D} {T : MPOTensor d χ}
    {V : ι → Matrix (Fin D) (Fin (χ * D)) ℂ} {W : ι → Matrix (Fin (χ * D)) (Fin D) ℂ}
    (h : IsBiorthogonalDecomposition (MPOTensor.actTensor T A) (fun _ : ι => A) V W) :
    IsBiorthogonalDecomposition
      (MPOTensor.actTensor (polarSupportMPO A T) (polarPosTensor A))
      (fun _ : ι => polarPosTensor A) V W := by
  have h' : IsBiorthogonalDecomposition
      (MPOTensor.actTensor T (rotatePhysical (polarIsoMatrix A)ᴴᴴ (polarPosTensor A)))
      (fun _ : ι => A) V W := by
    rw [Matrix.conjTranspose_conjTranspose, rotatePhysical_polarIsoMatrix_polarPosTensor]
    exact h
  simpa only [rotatePhysical_conjTranspose_polarIsoMatrix, polarSupportMPO] using
    h'.actTensor_changePhysicalBasis (polarIsoMatrix A)ᴴ T (polarPosTensor A)

/-- An exact action decomposition on a one-site injective tensor forces the
operator to preserve the physical support: `F Fᴴ T F = T F` on every
physical slice. Source: arXiv:2203.12563, lines 1584–1586, the restriction
of the local Hilbert space to the span of the tensor. -/
theorem polarIsoMatrix_mul_physicalSlice_of_isBiorthogonalDecomposition
    {ι : Type*} [Fintype ι] {A : MPSTensor d D} (hA : Kraus.IsInjective A)
    {T : MPOTensor d χ}
    {V : ι → Matrix (Fin D) (Fin (χ * D)) ℂ} {W : ι → Matrix (Fin (χ * D)) (Fin D) ℂ}
    (h : IsBiorthogonalDecomposition (MPOTensor.actTensor T A) (fun _ : ι => A) V W)
    (β α : Fin χ) :
    polarIsoMatrix A * (polarIsoMatrix A)ᴴ * MPOTensor.physicalSlice T β α *
        polarIsoMatrix A =
      MPOTensor.physicalSlice T β α * polarIsoMatrix A := by
  have h' : IsBiorthogonalDecomposition
      (MPOTensor.actTensor T (rotatePhysical (polarIsoMatrix A) (polarPosTensor A)))
      (fun _ : ι => A) V W := by
    rw [rotatePhysical_polarIsoMatrix_polarPosTensor]
    exact h
  exact MPOTensor.physicalSlice_mul_eq_of_isBiorthogonalDecomposition T (polarIsoMatrix A)
    (polarPosTensor A) (linearIndependent_polarPosTensor hA) _ h'
    (fun _ => rotatePhysical_polarIsoMatrix_mul_conjTranspose A) β α

/-- A fusion decomposition of two operators compresses to the physical
support of a one-site injective tensor, provided the second operator acts
on that tensor by an exact decomposition. Source: arXiv:2203.12563,
lines 1584–1586, with `fusiontensors` and `eq:orthoW`. -/
theorem IsBiorthogonalDecomposition.mulTensor_polarSupportMPO
    {ι κ : Type*} [Fintype ι] [Fintype κ] {δ : ι → ℕ} {D₁ D₂ : ℕ}
    {A : MPSTensor d D} (hA : Kraus.IsInjective A)
    {M : MPOTensor d D₁} {N : MPOTensor d D₂} {O : ∀ c : ι, MPOTensor d (δ c)}
    {V : ∀ c, Matrix (Fin (δ c)) (Fin (D₁ * D₂)) ℂ}
    {W : ∀ c, Matrix (Fin (D₁ * D₂)) (Fin (δ c)) ℂ}
    {V' : κ → Matrix (Fin D) (Fin (D₂ * D)) ℂ} {W' : κ → Matrix (Fin (D₂ * D)) (Fin D) ℂ}
    (h : IsBiorthogonalDecomposition (MPOTensor.mulTensor M N).toMPSTensor
      (fun c => (O c).toMPSTensor) V W)
    (hN : IsBiorthogonalDecomposition (MPOTensor.actTensor N A) (fun _ : κ => A) V' W') :
    IsBiorthogonalDecomposition
      (MPOTensor.mulTensor (polarSupportMPO A M) (polarSupportMPO A N)).toMPSTensor
      (fun c => (polarSupportMPO A (O c)).toMPSTensor) V W :=
  h.mulTensor_changePhysicalBasis _ M N fun β α => by
    rw [Matrix.conjTranspose_conjTranspose]
    exact polarIsoMatrix_mul_physicalSlice_of_isBiorthogonalDecomposition hA hN β α

namespace MPOSymmetry

variable {d₀ d₁ D₀ D₁ χ₀ χ₁ m : ℕ}

/-- The common MPO of the arbitrary-alphabet mixed path: the square-alphabet
mixed operator of the support-compressed endpoint operators, included in
the common physical space. Source: arXiv:2203.12563, Section 5,
lines 1584–1586 and 1600–1631. -/
noncomputable def arbitraryPhysicalMixedMPO
    (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁)
    (T₀ : MPOTensor d₀ χ₀) (T₁ : MPOTensor d₁ χ₁)
    (V₀ : Fin m → Matrix (Fin D₀) (Fin (χ₀ * D₀)) ℂ)
    (V₁ : Fin m → Matrix (Fin D₁) (Fin (χ₁ * D₁)) ℂ)
    (W₀ : Fin m → Matrix (Fin (χ₀ * D₀)) (Fin D₀) ℂ)
    (W₁ : Fin m → Matrix (Fin (χ₁ * D₁)) (Fin D₁) ℂ) :
    MPOTensor ((((D₀ + D₁) * (D₀ + D₁)) + d₀) + d₁) (χ₀ + χ₁) :=
  changePhysicalBasis (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁)
    (mixedEndpointMPO (polarSupportMPO A₀ T₀) (polarSupportMPO A₁ T₁) V₀ V₁ W₀ W₁)

section Action

variable (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁)
  (T₀ : MPOTensor d₀ χ₀) (T₁ : MPOTensor d₁ χ₁)
  (V₀ : Fin m → Matrix (Fin D₀) (Fin (χ₀ * D₀)) ℂ)
  (V₁ : Fin m → Matrix (Fin D₁) (Fin (χ₁ * D₁)) ℂ)
  (W₀ : Fin m → Matrix (Fin (χ₀ * D₀)) (Fin D₀) ℂ)
  (W₁ : Fin m → Matrix (Fin (χ₁ * D₁)) (Fin D₁) ℂ)
  (h₀ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₀ A₀)
    (fun _ : Fin m => A₀) V₀ W₀)
  (h₁ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₁ A₁)
    (fun _ : Fin m => A₁) V₁ W₁)

include h₀ h₁ in
/-- The common MPO acts on the arbitrary-alphabet mixed tensor by an exact
biorthogonal decomposition into `m` copies of that tensor, at every real
parameter and with the square-alphabet mixed action maps. Neither
injectivity nor a nonzero interpolation weight is assumed.
Source: arXiv:2203.12563, `Agammasym`, lines 1632–1665. -/
theorem isBiorthogonalDecomposition_arbitraryPhysicalMixedInterpolation (γ : ℝ) :
    IsBiorthogonalDecomposition
      (MPOTensor.actTensor (arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁)
        (arbitraryPhysicalMixedInterpolation A₀ A₁ γ))
      (fun _ : Fin m => arbitraryPhysicalMixedInterpolation A₀ A₁ γ)
      (fun μ => mixedEndpointMPOAnalysis (V₀ μ) (V₁ μ))
      (fun μ => mixedEndpointMPOSynthesis (W₀ μ) (W₁ μ)) := by
  have hmix := isBiorthogonalDecomposition_mixedEndpointInterpolation
    (polarSupportMPO A₀ T₀) (polarSupportMPO A₁ T₁) (polarPosTensor A₀) (polarPosTensor A₁)
    V₀ V₁ W₀ W₁ (isBiorthogonalDecomposition_polarSupportMPO h₀)
    (isBiorthogonalDecomposition_polarSupportMPO h₁) γ
  have hJ : rotatePhysical (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁)ᴴ
      (arbitraryPhysicalMixedInterpolation A₀ A₁ γ) =
        mixedEndpointInterpolation (polarPosTensor A₀) (polarPosTensor A₁) γ := by
    rw [arbitraryPhysicalMixedInterpolation, rotatePhysical_rotatePhysical,
      commonFixedPointInclusion_isometry, rotatePhysical_one]
  have hmix' : IsBiorthogonalDecomposition
      (MPOTensor.actTensor
        (mixedEndpointMPO (polarSupportMPO A₀ T₀) (polarSupportMPO A₁ T₁) V₀ V₁ W₀ W₁)
        (rotatePhysical (commonFixedPointInclusion ((D₀ + D₁) * (D₀ + D₁)) d₀ d₁)ᴴ
          (arbitraryPhysicalMixedInterpolation A₀ A₁ γ)))
      (fun _ : Fin m =>
        mixedEndpointInterpolation (polarPosTensor A₀) (polarPosTensor A₁) γ)
      (fun μ => mixedEndpointMPOAnalysis (V₀ μ) (V₁ μ))
      (fun μ => mixedEndpointMPOSynthesis (W₀ μ) (W₁ μ)) := by
    rw [hJ]
    exact hmix
  exact hmix'.actTensor_changePhysicalBasis _ _ _

include h₀ h₁ in
/-- The common MPO preserves the arbitrary-boundary mixed states, with one
boundary transport valid at every positive length.
Source: arXiv:2203.12563, `eq:compatible` and `Agammasym`. -/
theorem isBoundaryCompatible_arbitraryPhysicalMixedInterpolation (γ : ℝ) :
    MPOTensor.IsBoundaryCompatible (arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁)
      (arbitraryPhysicalMixedInterpolation A₀ A₁ γ) :=
  MPOTensor.isBoundaryCompatible_of_biorthogonalDecomposition _ _ _ _
    (isBiorthogonalDecomposition_arbitraryPhysicalMixedInterpolation
      A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ h₀ h₁ γ)

include h₀ h₁ in
/-- At every real parameter and every positive length, the periodic mixed
state is an eigenvector of the common MPO with eigenvalue the action
multiplicity. Source: arXiv:2203.12563, `Agammasym` and `eq:orthoV`. -/
theorem mpo_mulVec_arbitraryPhysicalMixedInterpolation (γ : ℝ) {L : ℕ} (hL : 0 < L) :
    MPOTensor.mpo (arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁) L *ᵥ
        (fun σ : Fin L → Fin ((((D₀ + D₁) * (D₀ + D₁)) + d₀) + d₁) =>
          mpv (arbitraryPhysicalMixedInterpolation A₀ A₁ γ) σ) =
      (m : ℂ) • (fun σ => mpv (arbitraryPhysicalMixedInterpolation A₀ A₁ γ) σ) := by
  rw [MPOTensor.mpo_mulVec_mpv]
  funext σ
  have h := isBiorthogonalDecomposition_arbitraryPhysicalMixedInterpolation
    A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ h₀ h₁ γ
  have ht := h.trace_mul_evalWord 1 (List.ofFn σ)
    (by rw [Ne, List.ofFn_eq_nil_iff]; omega)
  simpa [mpv, coeff, Matrix.mul_one, h.retract, nsmul_eq_mul] using ht

include h₀ h₁ in
/-- At parameter zero, the periodic state of the fully embedded original
first tensor is an eigenvector of the common MPO at every positive length.
Only injectivity of the first tensor is used. Source: arXiv:2203.12563,
`Agammasym` and lines 1586–1601. -/
theorem mpo_mulVec_mpv_commonPhysicalEmbeddingLeft (hInj₀ : Kraus.IsInjective A₀)
    {L : ℕ} (hL : 0 < L) :
    MPOTensor.mpo (arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁) L *ᵥ
        (fun σ : Fin L → Fin ((((D₀ + D₁) * (D₀ + D₁)) + d₀) + d₁) =>
          mpv (rotatePhysical (commonPhysicalEmbeddingLeft d₁ D₁ A₀) A₀) σ) =
      (m : ℂ) • (fun σ => mpv (rotatePhysical (commonPhysicalEmbeddingLeft d₁ D₁ A₀) A₀) σ) := by
  have hmpv := mpv_arbitraryPhysicalMixedInterpolation_zero (N := L) A₀ A₁ hInj₀ hL
  have hfun : (fun σ : Fin L → Fin ((((D₀ + D₁) * (D₀ + D₁)) + d₀) + d₁) =>
      mpv (rotatePhysical (commonPhysicalEmbeddingLeft d₁ D₁ A₀) A₀) σ) =
        fun σ => mpv (arbitraryPhysicalMixedInterpolation A₀ A₁ 0) σ :=
    funext fun σ => (congrFun hmpv σ).symm
  rw [hfun]
  exact mpo_mulVec_arbitraryPhysicalMixedInterpolation A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ h₀ h₁ 0 hL

include h₀ h₁ in
/-- At parameter one, the periodic state of the fully embedded original
second tensor is an eigenvector of the common MPO at every positive length.
Only injectivity of the second tensor is used. Source: arXiv:2203.12563,
`Agammasym` and lines 1586–1601. -/
theorem mpo_mulVec_mpv_commonPhysicalEmbeddingRight (hInj₁ : Kraus.IsInjective A₁)
    {L : ℕ} (hL : 0 < L) :
    MPOTensor.mpo (arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁) L *ᵥ
        (fun σ : Fin L → Fin ((((D₀ + D₁) * (D₀ + D₁)) + d₀) + d₁) =>
          mpv (rotatePhysical (commonPhysicalEmbeddingRight d₀ D₀ A₁) A₁) σ) =
      (m : ℂ) • (fun σ => mpv (rotatePhysical (commonPhysicalEmbeddingRight d₀ D₀ A₁) A₁) σ) := by
  have hmpv := mpv_arbitraryPhysicalMixedInterpolation_one (N := L) A₀ A₁ hInj₁ hL
  have hfun : (fun σ : Fin L → Fin ((((D₀ + D₁) * (D₀ + D₁)) + d₀) + d₁) =>
      mpv (rotatePhysical (commonPhysicalEmbeddingRight d₀ D₀ A₁) A₁) σ) =
        fun σ => mpv (arbitraryPhysicalMixedInterpolation A₀ A₁ 1) σ :=
    funext fun σ => (congrFun hmpv σ).symm
  rw [hfun]
  exact mpo_mulVec_arbitraryPhysicalMixedInterpolation A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ h₀ h₁ 1 hL

end Action

section Fusion

variable {r : ℕ} {χ₀ χ₁ : Fin r → ℕ}
  {N : Fin r → Fin r → Fin r → ℕ} {m : Fin r → ℕ}
  (O₀ : ∀ a, MPOTensor d₀ (χ₀ a)) (O₁ : ∀ a, MPOTensor d₁ (χ₁ a))
  (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁)
  (VF₀ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₀ c)) (Fin (χ₀ a * χ₀ b)) ℂ)
  (WF₀ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₀ a * χ₀ b)) (Fin (χ₀ c)) ℂ)
  (VA₀ : ∀ a, Fin (m a) → Matrix (Fin D₀) (Fin (χ₀ a * D₀)) ℂ)
  (WA₀ : ∀ a, Fin (m a) → Matrix (Fin (χ₀ a * D₀)) (Fin D₀) ℂ)
  (VF₁ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₁ c)) (Fin (χ₁ a * χ₁ b)) ℂ)
  (WF₁ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₁ a * χ₁ b)) (Fin (χ₁ c)) ℂ)
  (VA₁ : ∀ a, Fin (m a) → Matrix (Fin D₁) (Fin (χ₁ a * D₁)) ℂ)
  (WA₁ : ∀ a, Fin (m a) → Matrix (Fin (χ₁ a * D₁)) (Fin D₁) ℂ)
  (hF₀ : ∀ a b,
    IsBiorthogonalDecomposition (MPOTensor.mulTensor (O₀ a) (O₀ b)).toMPSTensor
      (fun q : (c : Fin r) × Fin (N a b c) ↦ (O₀ q.1).toMPSTensor)
      (fun q ↦ VF₀ a b q.1 q.2) (fun q ↦ WF₀ a b q.1 q.2))
  (hA₀ : ∀ a, IsBiorthogonalDecomposition (MPOTensor.actTensor (O₀ a) A₀)
    (fun _ : Fin (m a) ↦ A₀) (VA₀ a) (WA₀ a))
  (hF₁ : ∀ a b,
    IsBiorthogonalDecomposition (MPOTensor.mulTensor (O₁ a) (O₁ b)).toMPSTensor
      (fun q : (c : Fin r) × Fin (N a b c) ↦ (O₁ q.1).toMPSTensor)
      (fun q ↦ VF₁ a b q.1 q.2) (fun q ↦ WF₁ a b q.1 q.2))
  (hA₁ : ∀ a, IsBiorthogonalDecomposition (MPOTensor.actTensor (O₁ a) A₁)
    (fun _ : Fin (m a) ↦ A₁) (VA₁ a) (WA₁ a))
  (hInj₀ : Kraus.IsInjective A₀) (hInj₁ : Kraus.IsInjective A₁)
  (hD₀ : 0 < D₀) (hD₁ : 0 < D₁)

include hF₀ hA₀ hF₁ hA₁ hInj₀ hInj₁ hD₀ hD₁ in
/-- The common MPOs of the arbitrary-alphabet path fuse exactly into copies
of the labelled common MPOs, with the original fusion multiplicities and
the square-alphabet mixed fusion maps. Equal chosen raw L matrices are
required only for the selected pair of labels; physical-support invariance
is derived from the action decompositions.
Source: arXiv:2203.12563, lines 1584–1586 and 1667–1685. -/
theorem isBiorthogonalDecomposition_arbitraryPhysicalMixedMPO (a b : Fin r)
    (hL : MPOTensor.actionLMatrix WF₀ (fun a (_ _ : Fin 1) ↦ VA₀ a)
        (fun a _ _ ↦ WA₀ a) a b 0 0 =
      MPOTensor.actionLMatrix WF₁ (fun a (_ _ : Fin 1) ↦ VA₁ a)
        (fun a _ _ ↦ WA₁ a) a b 0 0) :
    IsBiorthogonalDecomposition
      (MPOTensor.mulTensor
        (arbitraryPhysicalMixedMPO A₀ A₁ (O₀ a) (O₁ a) (VA₀ a) (VA₁ a) (WA₀ a) (WA₁ a))
        (arbitraryPhysicalMixedMPO A₀ A₁ (O₀ b) (O₁ b) (VA₀ b) (VA₁ b)
          (WA₀ b) (WA₁ b))).toMPSTensor
      (fun q : (c : Fin r) × Fin (N a b c) ↦
        (arbitraryPhysicalMixedMPO A₀ A₁ (O₀ q.1) (O₁ q.1) (VA₀ q.1) (VA₁ q.1)
          (WA₀ q.1) (WA₁ q.1)).toMPSTensor)
      (fun q ↦ mixedEndpointMPOFusionAnalysis (VF₀ a b q.1 q.2) (VF₁ a b q.1 q.2))
      (fun q ↦ mixedEndpointMPOFusionSynthesis (WF₀ a b q.1 q.2) (WF₁ a b q.1 q.2)) := by
  have hsq := isBiorthogonalDecomposition_mixedEndpointMPO
    (fun a ↦ polarSupportMPO A₀ (O₀ a)) (fun a ↦ polarSupportMPO A₁ (O₁ a))
    (polarPosTensor A₀) (polarPosTensor A₁) VF₀ WF₀ VA₀ WA₀ VF₁ WF₁ VA₁ WA₁
    (fun a b ↦ (hF₀ a b).mulTensor_polarSupportMPO hInj₀ (hA₀ b))
    (fun a ↦ isBiorthogonalDecomposition_polarSupportMPO (hA₀ a))
    (fun a b ↦ (hF₁ a b).mulTensor_polarSupportMPO hInj₁ (hA₁ b))
    (fun a ↦ isBiorthogonalDecomposition_polarSupportMPO (hA₁ a))
    (isInjective_polarPosTensor hInj₀) (isInjective_polarPosTensor hInj₁) hD₀ hD₁ a b hL
  unfold arbitraryPhysicalMixedMPO
  rw [MPOTensor.mulTensor_changePhysicalBasis _ (commonFixedPointInclusion_isometry _ _ _)]
  exact hsq.toMPSTensor_changePhysicalBasis _ _

include hF₀ hA₀ hF₁ hA₁ hInj₀ hInj₁ hD₀ hD₁ in
/-- With equal chosen raw L matrices, the common MPOs of the arbitrary-
alphabet path satisfy the original fusion rules at every positive length.
Source: arXiv:2203.12563, `fusiontensors` and lines 1667–1685. -/
theorem isMPOFusionAlgebra_arbitraryPhysicalMixedMPO
    (hL : ∀ a b, MPOTensor.actionLMatrix WF₀ (fun a (_ _ : Fin 1) ↦ VA₀ a)
        (fun a _ _ ↦ WA₀ a) a b 0 0 =
      MPOTensor.actionLMatrix WF₁ (fun a (_ _ : Fin 1) ↦ VA₁ a)
        (fun a _ _ ↦ WA₁ a) a b 0 0) :
    MPOTensor.IsMPOFusionAlgebra
      (fun a ↦ arbitraryPhysicalMixedMPO A₀ A₁ (O₀ a) (O₁ a) (VA₀ a) (VA₁ a)
        (WA₀ a) (WA₁ a)) N :=
  MPOTensor.isMPOFusionAlgebra_of_biorthogonalDecompositions
    (fun a b c μ ↦ mixedEndpointMPOFusionAnalysis (VF₀ a b c μ) (VF₁ a b c μ))
    (fun a b c μ ↦ mixedEndpointMPOFusionSynthesis (WF₀ a b c μ) (WF₁ a b c μ))
    (fun a b ↦ isBiorthogonalDecomposition_arbitraryPhysicalMixedMPO
      O₀ O₁ A₀ A₁ VF₀ WF₀ VA₀ WA₀ VF₁ WF₁ VA₁ WA₁
      hF₀ hA₀ hF₁ hA₁ hInj₀ hInj₁ hD₀ hD₁ a b (hL a b))

include hA₀ hA₁ in
/-- Along the whole real line of parameters, the arbitrary-alphabet mixed
tensor is symmetric under the common MPO family, each label acting with its
action multiplicity. Source: arXiv:2203.12563, lines 567–568 and
`Agammasym`. -/
theorem isMPOSymmetric_arbitraryPhysicalMixedInterpolation (γ : ℝ) :
    MPOTensor.IsMPOSymmetric
      (fun a ↦ arbitraryPhysicalMixedMPO A₀ A₁ (O₀ a) (O₁ a) (VA₀ a) (VA₁ a)
        (WA₀ a) (WA₁ a))
      (arbitraryPhysicalMixedInterpolation A₀ A₁ γ) (fun a ↦ (m a : ℂ)) :=
  fun a _ hL ↦ mpo_mulVec_arbitraryPhysicalMixedInterpolation A₀ A₁ (O₀ a) (O₁ a)
    (VA₀ a) (VA₁ a) (WA₀ a) (WA₁ a) (hA₀ a) (hA₁ a) γ hL

end Fusion

end MPOSymmetry
end MPSTensor
