/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointMPOWeights
import TNLean.MPS.MPDO.BoundaryClosedness

/-!
# Exact action covariance of the mixed endpoint interpolation

The MPO constructed from exact endpoint action decompositions acts on the
actual mixed tensor of GLM23 `defAgamma`. Its action decomposes into the
same number of copies of that tensor for every real parameter, including
both endpoints. The construction requires neither injectivity nor nonzero
interpolation weights nor completeness on the enlarged acted bond.

Arbitrary-boundary compatibility and the positive-length periodic
eigenvector equation follow from this exact local identity. These results
do not establish fusion closedness, equal L-symbols, physical adjoint
closure, Hamiltonian commutation, or symmetric-phase equivalence.

Source: Garre-Rubio–Lootens–Molnár, arXiv:2203.12563v3,
`fusiontensors2`, `eq:orthoV`, and `Agammasym`, lines 458–490,
1269, and 1584–1665.
-/

open scoped Matrix BigOperators Kronecker

namespace MPSTensor.MPOSymmetry

variable {D₀ D₁ χ₀ χ₁ m : ℕ}

private theorem endpoint_action_entry {D χ : ℕ}
    (T : MPOTensor (D * D) χ) (A : MPSTensor (D * D) D)
    (V : Fin m → Matrix (Fin D) (Fin (χ * D)) ℂ)
    (W : Fin m → Matrix (Fin (χ * D)) (Fin D) ℂ)
    (h : IsBiorthogonalDecomposition (MPOTensor.actTensor T A) (fun _ : Fin m => A) V W)
    (r s i j : Fin D) (α β : Fin χ) :
    (∑ k : Fin D, ∑ l : Fin D,
      T (finProdFinEquiv (r, s)) (finProdFinEquiv (k, l)) α β *
        A (finProdFinEquiv (k, l)) i j) =
      ∑ μ, (W μ * A (finProdFinEquiv (r, s)) * V μ)
        (finProdFinEquiv (α, i)) (finProdFinEquiv (β, j)) := by
  have hh := congrArg
    (fun M : Matrix (Fin (χ * D)) (Fin (χ * D)) ℂ =>
      M (finProdFinEquiv (α, i)) (finProdFinEquiv (β, j)))
    (h.letter (finProdFinEquiv (r, s)))
  simp only [MPOTensor.actTensor, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.sum_apply, Matrix.kroneckerMap_apply] at hh
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type] at hh
  exact hh

set_option maxHeartbeats 800000 in
-- The six independent sector indices give 64 finite cases in this coordinate identity.
/-- Entrywise reconstruction of the unweighted mixed action. The two
nonzero diagonal cases use the supplied endpoint reconstruction; the
cross cases are precisely the defining synthesis-analysis contractions.
Source: GLM23, `Agammasym`, lines 1632–1665. -/
theorem mixedEndpointMPOLetter_action
    (T₀ : MPOTensor (D₀ * D₀) χ₀) (T₁ : MPOTensor (D₁ * D₁) χ₁)
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (V₀ : Fin m → Matrix (Fin D₀) (Fin (χ₀ * D₀)) ℂ)
    (V₁ : Fin m → Matrix (Fin D₁) (Fin (χ₁ * D₁)) ℂ)
    (W₀ : Fin m → Matrix (Fin (χ₀ * D₀)) (Fin D₀) ℂ)
    (W₁ : Fin m → Matrix (Fin (χ₁ * D₁)) (Fin D₁) ℂ)
    (h₀ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₀ A₀)
      (fun _ : Fin m => A₀) V₀ W₀)
    (h₁ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₁ A₁)
      (fun _ : Fin m => A₁) V₁ W₁)
    (r s i j : Fin D₀ ⊕ Fin D₁) (α β : Fin χ₀ ⊕ Fin χ₁) :
    (∑ k : Fin D₀ ⊕ Fin D₁, ∑ l : Fin D₀ ⊕ Fin D₁,
      mixedEndpointMPOLetter T₀ T₁ V₀ V₁ W₀ W₁ r s k l α β *
        mixedEndpointLetter A₀ A₁ k l i j) =
      ∑ μ, (mixedEndpointSynthesis (W₀ μ) (W₁ μ) *
        mixedEndpointLetter A₀ A₁ r s * mixedEndpointAnalysis (V₀ μ) (V₁ μ))
          (α, i) (β, j) := by
  classical
  cases r <;> cases s <;> cases i <;> cases j <;> cases α <;> cases β <;>
    simp only [Fintype.sum_sum_type, mixedEndpointMPOLetter, mixedEndpointLetter,
      mixedEndpointSynthesis, mixedEndpointAnalysis, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.mul_apply, Matrix.single_apply, ite_and, mul_ite, ite_mul,
      Finset.sum_mul, Matrix.zero_apply, zero_mul, mul_zero, Finset.sum_const_zero,
      zero_add, add_zero, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr,
      Sum.inr_ne_inl, and_false, false_and, ite_false, ite_true,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel,
      Finset.mem_univ, mul_one]
  · simpa [Matrix.mul_apply, Finset.sum_mul] using
      endpoint_action_entry T₀ A₀ V₀ W₀ h₀ _ _ _ _ _ _
  · simpa [Matrix.mul_apply, Finset.sum_mul] using
      endpoint_action_entry T₁ A₁ V₁ W₁ h₁ _ _ _ _ _ _

/-- Exact reconstruction in the standard coordinates of the unweighted
mixed tensor. Source: GLM23, `Agammasym`, before right multiplication by
the interpolation weight. -/
theorem actTensor_mixedEndpointBase
    (T₀ : MPOTensor (D₀ * D₀) χ₀) (T₁ : MPOTensor (D₁ * D₁) χ₁)
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (V₀ : Fin m → Matrix (Fin D₀) (Fin (χ₀ * D₀)) ℂ)
    (V₁ : Fin m → Matrix (Fin D₁) (Fin (χ₁ * D₁)) ℂ)
    (W₀ : Fin m → Matrix (Fin (χ₀ * D₀)) (Fin D₀) ℂ)
    (W₁ : Fin m → Matrix (Fin (χ₁ * D₁)) (Fin D₁) ℂ)
    (h₀ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₀ A₀)
      (fun _ : Fin m => A₀) V₀ W₀)
    (h₁ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₁ A₁)
      (fun _ : Fin m => A₁) V₁ W₁)
    (p : Fin ((D₀ + D₁) * (D₀ + D₁))) :
    MPOTensor.actTensor (mixedEndpointMPO T₀ T₁ V₀ V₁ W₀ W₁)
      (mixedEndpointBase A₀ A₁) p =
      ∑ μ, mixedEndpointMPOSynthesis (W₀ μ) (W₁ μ) *
        mixedEndpointBase A₀ A₁ p * mixedEndpointMPOAnalysis (V₀ μ) (V₁ μ) := by
  classical
  obtain ⟨⟨r, s⟩, rfl⟩ := (mixedEndpointPhysicalEquiv D₀ D₁).surjective p
  ext a b
  obtain ⟨⟨α, i⟩, rfl⟩ := (mixedEndpointActedEquiv χ₀ χ₁ D₀ D₁).surjective a
  obtain ⟨⟨β, j⟩, rfl⟩ := (mixedEndpointActedEquiv χ₀ χ₁ D₀ D₁).surjective b
  simp only [MPOTensor.actTensor, Matrix.submatrix_apply, Matrix.sum_apply,
    Matrix.kroneckerMap_apply]
  rw [← (mixedEndpointPhysicalEquiv D₀ D₁).sum_comp, Fintype.sum_prod_type]
  simp only [mixedEndpointMPO_physicalEquiv, mixedEndpointBase_physicalEquiv,
    mixedEndpointMPOSynthesis, mixedEndpointMPOAnalysis,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    mixedEndpointActedEquiv, Equiv.trans_apply, Equiv.prodCongr_apply,
    Equiv.symm_apply_apply]
  simpa [Equiv.symm_trans, Equiv.prodCongr_symm] using
    mixedEndpointMPOLetter_action T₀ T₁ A₀ A₁ V₀ V₁ W₀ W₁ h₀ h₁ r s i j α β

/-- Exact biorthogonal action on the actual mixed interpolation for every
real parameter. Both endpoint decompositions have the same multiplicity.
There are no injectivity, gap, nonzero-weight, or ambient-completeness
hypotheses. Source: GLM23, `Agammasym`, lines 1632–1665. -/
theorem isBiorthogonalDecomposition_mixedEndpointInterpolation
    (T₀ : MPOTensor (D₀ * D₀) χ₀) (T₁ : MPOTensor (D₁ * D₁) χ₁)
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (V₀ : Fin m → Matrix (Fin D₀) (Fin (χ₀ * D₀)) ℂ)
    (V₁ : Fin m → Matrix (Fin D₁) (Fin (χ₁ * D₁)) ℂ)
    (W₀ : Fin m → Matrix (Fin (χ₀ * D₀)) (Fin D₀) ℂ)
    (W₁ : Fin m → Matrix (Fin (χ₁ * D₁)) (Fin D₁) ℂ)
    (h₀ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₀ A₀)
      (fun _ : Fin m => A₀) V₀ W₀)
    (h₁ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₁ A₁)
      (fun _ : Fin m => A₁) V₁ W₁) (γ : ℝ) :
    IsBiorthogonalDecomposition
      (MPOTensor.actTensor (mixedEndpointMPO T₀ T₁ V₀ V₁ W₀ W₁)
        (mixedEndpointInterpolation A₀ A₁ γ))
      (fun _ : Fin m => mixedEndpointInterpolation A₀ A₁ γ)
      (fun μ => mixedEndpointMPOAnalysis (V₀ μ) (V₁ μ))
      (fun μ => mixedEndpointMPOSynthesis (W₀ μ) (W₁ μ)) where
  retract μ := by
    rw [mixedEndpointMPOAnalysis_mul_synthesis, h₀.retract μ, h₁.retract μ,
      Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
  orthogonal μ ν hμν := by
    rw [mixedEndpointMPOAnalysis_mul_synthesis,
      h₀.orthogonal μ ν hμν, h₁.orthogonal μ ν hμν, Matrix.fromBlocks_zero]
    rfl
  letter p := by
    change MPOTensor.actTensor (mixedEndpointMPO T₀ T₁ V₀ V₁ W₀ W₁)
      (fun j => mixedEndpointBase A₀ A₁ j * bondInterpolationMatrix D₀ D₁ γ) p =
        ∑ μ, mixedEndpointMPOSynthesis (W₀ μ) (W₁ μ) *
          (mixedEndpointBase A₀ A₁ p * bondInterpolationMatrix D₀ D₁ γ) *
            mixedEndpointMPOAnalysis (V₀ μ) (V₁ μ)
    rw [MPOTensor.actTensor_right_mul,
      actTensor_mixedEndpointBase T₀ T₁ A₀ A₁ V₀ V₁ W₀ W₁ h₀ h₁,
      Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro μ _
    rw [Matrix.mul_assoc, mixedEndpointMPOAnalysis_mul_weight]
    simp only [Matrix.mul_assoc]

/-- The constructed mixed MPO preserves arbitrary-boundary mixed states
with one boundary transport valid at every positive length.
Source: GLM23, `eq:compatible` and `Agammasym`. -/
theorem isBoundaryCompatible_mixedEndpointInterpolation
    (T₀ : MPOTensor (D₀ * D₀) χ₀) (T₁ : MPOTensor (D₁ * D₁) χ₁)
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (V₀ : Fin m → Matrix (Fin D₀) (Fin (χ₀ * D₀)) ℂ)
    (V₁ : Fin m → Matrix (Fin D₁) (Fin (χ₁ * D₁)) ℂ)
    (W₀ : Fin m → Matrix (Fin (χ₀ * D₀)) (Fin D₀) ℂ)
    (W₁ : Fin m → Matrix (Fin (χ₁ * D₁)) (Fin D₁) ℂ)
    (h₀ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₀ A₀)
      (fun _ : Fin m => A₀) V₀ W₀)
    (h₁ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₁ A₁)
      (fun _ : Fin m => A₁) V₁ W₁) (γ : ℝ) :
    MPOTensor.IsBoundaryCompatible (mixedEndpointMPO T₀ T₁ V₀ V₁ W₀ W₁)
      (mixedEndpointInterpolation A₀ A₁ γ) :=
  MPOTensor.isBoundaryCompatible_of_biorthogonalDecomposition _ _ _ _
    (isBiorthogonalDecomposition_mixedEndpointInterpolation
      T₀ T₁ A₀ A₁ V₀ V₁ W₀ W₁ h₀ h₁ γ)

/-- At each positive chain length, the actual periodic mixed state is an
eigenvector with eigenvalue the common action multiplicity. The vector is
not assumed nonzero. Source: GLM23, `Agammasym` and `eq:orthoV`. -/
theorem mpo_mulVec_mixedEndpointInterpolation
    (T₀ : MPOTensor (D₀ * D₀) χ₀) (T₁ : MPOTensor (D₁ * D₁) χ₁)
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (V₀ : Fin m → Matrix (Fin D₀) (Fin (χ₀ * D₀)) ℂ)
    (V₁ : Fin m → Matrix (Fin D₁) (Fin (χ₁ * D₁)) ℂ)
    (W₀ : Fin m → Matrix (Fin (χ₀ * D₀)) (Fin D₀) ℂ)
    (W₁ : Fin m → Matrix (Fin (χ₁ * D₁)) (Fin D₁) ℂ)
    (h₀ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₀ A₀)
      (fun _ : Fin m => A₀) V₀ W₀)
    (h₁ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₁ A₁)
      (fun _ : Fin m => A₁) V₁ W₁) (γ : ℝ) {L : ℕ} (hL : 0 < L) :
    MPOTensor.mpo (mixedEndpointMPO T₀ T₁ V₀ V₁ W₀ W₁) L *ᵥ
        (fun σ : Fin L → Fin ((D₀ + D₁) * (D₀ + D₁)) =>
          mpv (mixedEndpointInterpolation A₀ A₁ γ) σ) =
      (m : ℂ) • (fun σ => mpv (mixedEndpointInterpolation A₀ A₁ γ) σ) := by
  rw [MPOTensor.mpo_mulVec_mpv]
  funext σ
  have h := isBiorthogonalDecomposition_mixedEndpointInterpolation
    T₀ T₁ A₀ A₁ V₀ V₁ W₀ W₁ h₀ h₁ γ
  have ht := h.trace_mul_evalWord 1 (List.ofFn σ)
    (by rw [Ne, List.ofFn_eq_nil_iff]; omega)
  simpa [mpv, coeff, Matrix.mul_one, h.retract, nsmul_eq_mul] using ht

end MPSTensor.MPOSymmetry
