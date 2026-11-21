/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.WeakHopfParentAverage
import TNLean.MPS.Symmetry.MPOSymmetry.ArbitraryPhysicalMixedPathGap
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointMPOAction
import TNLean.MPS.Symmetry.BoundaryParentHamiltonian

/-!
# Weak-Hopf averaging on the active mixed physical space

Given a weak-Hopf realization of the active common MPO, the literal average
of the continuous mixed interaction is `Q - 1 + h`, including both endpoints.
Adding the missing `1 - Q` penalty recovers exactly `h`. Thus the completed
path is continuous and positive and its periodic Hamiltonian commutes with the
common MPO at every length at least two. No adjoint-closure premise is used.

**Scope restriction (supplied active realization):** the realization is an
explicit hypothesis, not a reconstruction from fusion
and F-symbols. It is imposed on the active square alphabet, not on the
zero-padded enlarged alphabet, where unital realization is impossible.
Source: arXiv:2203.12563v3, Section 5 and Appendix B. See the separate note
`docs/paper-gaps/glm23_mixed_weak_hopf_realization.tex`.
-/

open scoped Matrix TensorProduct ComplexOrder

open ManyBody

noncomputable section

namespace MPOTensor.WeakHopfRepresentation

variable {H : Type*} [Ring H] [Algebra ℂ H] [Coalgebra ℂ H]
  [StarRing H] [StarModule ℂ H] {d D n : ℕ}

/-- The integral average in matrix coordinates. -/
def averageMatrix (W : WeakHopfRepresentation H d D) (n : ℕ)
    (P : ChainOperator d n) : ChainOperator d n :=
  Matrix.toEuclideanLin.symm (W.weakHopfAverage n (Matrix.toEuclideanLin P))

/-- A finite Sweedler decomposition computes the matrix average. -/
theorem averageMatrix_eq_sum (W : WeakHopfRepresentation H d D)
    {ι : Type*} (𝓡 : Coalgebra.Repr ℂ W.integral ι) (P : ChainOperator d n) :
    W.averageMatrix n P = ∑ i ∈ 𝓡.index,
      W.rep n (𝓡.left i) * P * W.rep n (W.pullThrough (𝓡.right i)) := by
  apply Matrix.toEuclideanLin.injective
  simp only [averageMatrix, LinearEquiv.apply_symm_apply, W.weakHopfAverage_eq_sum 𝓡,
    map_sum, Matrix.toEuclideanLin, Matrix.toLpLin_mul_same]
  rfl

/-- The integral average is continuous in the local interaction. -/
theorem continuous_averageMatrix (W : WeakHopfRepresentation H d D) (n : ℕ) :
    Continuous (W.averageMatrix n) := by
  change Continuous (fun P => W.averageMatrix n P)
  simp_rw [W.averageMatrix_eq_sum (Coalgebra.Repr.arbitrary ℂ W.integral)]
  fun_prop

/-- In finite dimension the represented unit commutes with every boundary
operator, because each boundary operator represents an algebra element. -/
theorem rep_one_commute_mpoWithBoundary [FiniteDimensional ℂ H]
    (W : WeakHopfRepresentation H d D) (hn : 0 < n)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    Commute (W.rep n 1) (mpoWithBoundary W.tensor X n) := by
  obtain ⟨x, hx⟩ := exists_weakHopfRep_eq_mpoWithBoundary W.phys.toLinearMap W.virt X
  have he : mpoWithBoundary W.tensor X n = W.rep n x := hx n
  rw [he]
  change W.rep n 1 * W.rep n x = W.rep n x * W.rep n 1
  rw [← W.rep_mul hn, ← W.rep_mul hn, one_mul, mul_one]

end MPOTensor.WeakHopfRepresentation

attribute [local instance] MPSTensor.groundSpaceES_hasOrthogonalProjection

namespace MPSTensor.MPOSymmetry

variable {H : Type*} [Ring H] [Algebra ℂ H] [Coalgebra ℂ H]
  [StarRing H] [StarModule ℂ H] {D₀ D₁ χ₀ χ₁ m N : ℕ}

variable (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
  (T₀ : MPOTensor (D₀ * D₀) χ₀) (T₁ : MPOTensor (D₁ * D₁) χ₁)
  (V₀ : Fin m → Matrix (Fin D₀) (Fin (χ₀ * D₀)) ℂ)
  (V₁ : Fin m → Matrix (Fin D₁) (Fin (χ₁ * D₁)) ℂ)
  (W₀ : Fin m → Matrix (Fin (χ₀ * D₀)) (Fin D₀) ℂ)
  (W₁ : Fin m → Matrix (Fin (χ₁ * D₁)) (Fin D₁) ℂ)
  (W : MPOTensor.WeakHopfRepresentation H ((D₀ + D₁) * (D₀ + D₁)) (χ₀ + χ₁))

/-- The ambient completion of the literal integral average on the active
physical space. The correction is necessary because the average is nonunital. -/
def mixedWeakHopfCompletedInteraction (γ : ℝ) :=
  W.averageMatrix 2 (mixedEndpointInteractionMatrix A₀ A₁ γ) + (1 - W.rep 2 1)

variable (h₀ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₀ A₀)
    (fun _ : Fin m => A₀) V₀ W₀)
  (h₁ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₁ A₁)
    (fun _ : Fin m => A₁) V₁ W₁)
  (hW : W.tensor = mixedEndpointMPO T₀ T₁ V₀ V₁ W₀ W₁)
  (hInj₀ : Kraus.IsInjective A₀) (hInj₁ : Kraus.IsInjective A₁)

include h₀ h₁ hW hInj₀ hInj₁ in
/-- In the interior, the literal average differs from the canonical parent
by precisely the missing represented-unit projection. -/
theorem averageMatrix_mixedEndpointInteraction_of_mem_Ioo
    {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    W.averageMatrix 2 (mixedEndpointInteractionMatrix A₀ A₁ γ) =
      W.rep 2 1 - 1 + mixedEndpointInteractionMatrix A₀ A₁ γ := by
  have hc : MPOTensor.IsBoundaryCompatible W.tensor (mixedEndpointInterpolation A₀ A₁ γ) := by
    rw [hW]
    exact isBoundaryCompatible_mixedEndpointInterpolation
      T₀ T₁ A₀ A₁ V₀ V₁ W₀ W₁ h₀ h₁ γ
  have hi := Kraus.isNBlkInjective_one_of_isInjective
    (isInjective_mixedEndpointInterpolation A₀ A₁ hInj₀ hInj₁ hγ)
  apply Matrix.toEuclideanLin.injective
  simp only [MPOTensor.WeakHopfRepresentation.averageMatrix, LinearEquiv.apply_symm_apply,
    map_add, map_sub, toEuclideanLin_mixedEndpointInteractionMatrix,
    mixedEndpointParentInteraction_eq_parentInteractionES A₀ A₁ hγ,
    LinearMap.coe_toContinuousLinearMap]
  rw [W.weakHopfAverage_parentInteractionES hc hi (by decide), parentInteractionES,
    Submodule.starProjection_orthogonal']
  have hone : Matrix.toEuclideanLin (1 : MPOTensor.ChainOperator
      ((D₀ + D₁) * (D₀ + D₁)) 2) = 1 := by
    simp [Matrix.toEuclideanLin]
    rfl
  rw [hone]
  change Matrix.toEuclideanLin (W.rep 2 1) -
      (groundSpaceES (mixedEndpointInterpolation A₀ A₁ γ) 2).starProjection.toLinearMap =
    Matrix.toEuclideanLin (W.rep 2 1) - 1 +
      (1 - (groundSpaceES (mixedEndpointInterpolation A₀ A₁ γ) 2).starProjection.toLinearMap)
  abel

include h₀ h₁ hW hInj₀ hInj₁ in
/-- Continuity extends the average formula through the rank-changing endpoints.
The endpoint interaction uses the extended support, not the endpoint tensor's
canonical support. -/
theorem averageMatrix_mixedEndpointInteraction [NeZero D₀] [NeZero D₁]
    {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) :
    W.averageMatrix 2 (mixedEndpointInteractionMatrix A₀ A₁ γ) =
      W.rep 2 1 - 1 + mixedEndpointInteractionMatrix A₀ A₁ γ := by
  have hc := continuous_mixedEndpointInteractionMatrix A₀ A₁ hInj₀ hInj₁
  have hs : Set.Ioo (0 : ℝ) 1 ⊆ {γ | W.averageMatrix 2
      (mixedEndpointInteractionMatrix A₀ A₁ γ) =
        W.rep 2 1 - 1 + mixedEndpointInteractionMatrix A₀ A₁ γ} := fun γ hγ =>
    averageMatrix_mixedEndpointInteraction_of_mem_Ioo
      A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ W h₀ h₁ hW hInj₀ hInj₁ hγ
  rw [← closure_Ioo (zero_ne_one' ℝ)] at hγ
  exact Set.EqOn.closure hs ((W.continuous_averageMatrix 2).comp hc)
    (continuous_const.add hc) hγ

include h₀ h₁ hW hInj₀ hInj₁ in
/-- Completion restores the existing continuous parent path exactly. -/
theorem mixedWeakHopfCompletedInteraction_eq [NeZero D₀] [NeZero D₁]
    {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) :
    mixedWeakHopfCompletedInteraction A₀ A₁ W γ =
      mixedEndpointInteractionMatrix A₀ A₁ γ := by
  rw [mixedWeakHopfCompletedInteraction, averageMatrix_mixedEndpointInteraction
    A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ W h₀ h₁ hW hInj₀ hInj₁ hγ]
  abel

include hInj₀ hInj₁ in
/-- The completed path is continuous, even outside the interpolation interval. -/
theorem continuous_mixedWeakHopfCompletedInteraction [NeZero D₀] [NeZero D₁] :
    Continuous (mixedWeakHopfCompletedInteraction A₀ A₁ W) :=
  ((W.continuous_averageMatrix 2).comp
    (continuous_mixedEndpointInteractionMatrix A₀ A₁ hInj₀ hInj₁)).add continuous_const

include h₀ h₁ hW hInj₀ hInj₁ in
/-- The completed average is positive on the closed interval. -/
theorem mixedWeakHopfCompletedInteraction_posSemidef [NeZero D₀] [NeZero D₁]
    {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) :
    (mixedWeakHopfCompletedInteraction A₀ A₁ W γ).PosSemidef := by
  rw [mixedWeakHopfCompletedInteraction_eq
    A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ W h₀ h₁ hW hInj₀ hInj₁ hγ]
  exact mixedEndpointInteractionMatrix_posSemidef A₀ A₁ γ

include h₀ h₁ hW hInj₀ hInj₁ in
/-- The completed active interaction commutes with every boundary operator,
including at both endpoints. Adjoint closure follows from the realization. -/
theorem mixedWeakHopfCompletedInteraction_commute [NeZero D₀] [NeZero D₁]
    {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (X : Matrix (Fin (χ₀ + χ₁)) (Fin (χ₀ + χ₁)) ℂ) :
    Commute (mixedWeakHopfCompletedInteraction A₀ A₁ W γ)
      (MPOTensor.mpoWithBoundary W.tensor X 2) := by
  rw [mixedWeakHopfCompletedInteraction_eq
    A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ W h₀ h₁ hW hInj₀ hInj₁ hγ]
  set B := MPOTensor.mpoWithBoundary W.tensor X 2
  have hc := continuous_mixedEndpointInteractionMatrix A₀ A₁ hInj₀ hInj₁
  have hs : Set.Ioo (0 : ℝ) 1 ⊆ {γ | mixedEndpointInteractionMatrix A₀ A₁ γ * B =
      B * mixedEndpointInteractionMatrix A₀ A₁ γ} := by
    intro t ht
    have hcompat : MPOTensor.IsBoundaryCompatible W.tensor
        (mixedEndpointInterpolation A₀ A₁ t) := by
      rw [hW]
      exact isBoundaryCompatible_mixedEndpointInterpolation
        T₀ T₁ A₀ A₁ V₀ V₁ W₀ W₁ h₀ h₁ t
    have hcomm := hcompat.parentInteractionES_commute_mpoWithBoundary (by decide)
      (fun Z => let ⟨Y, hY⟩ := W.exists_conjTranspose_mpoWithBoundary_eq Z
        ⟨Y, hY 2⟩) X
    have hp : Matrix.toEuclideanLin (mixedEndpointInteractionMatrix A₀ A₁ t) =
        parentInteractionES (mixedEndpointInterpolation A₀ A₁ t) 2 := by
      rw [toEuclideanLin_mixedEndpointInteractionMatrix,
        mixedEndpointParentInteraction_eq_parentInteractionES A₀ A₁ ht]
      rfl
    rw [← hp] at hcomm
    apply Matrix.toEuclideanLin.injective
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
      Module.End.mul_eq_comp] using hcomm.eq
  rw [← closure_Ioo (zero_ne_one' ℝ)] at hγ
  exact Set.EqOn.closure hs (hc.matrix_mul continuous_const)
    (continuous_const.matrix_mul hc) hγ

include h₀ h₁ hW hInj₀ hInj₁ in
/-- For finite-dimensional weak-Hopf data the literal, uncompleted average
also commutes with all two-site boundary operators. This asserts no gap. -/
theorem averageMatrix_mixedEndpointInteraction_commute
    [FiniteDimensional ℂ H] [NeZero D₀] [NeZero D₁]
    {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (X : Matrix (Fin (χ₀ + χ₁)) (Fin (χ₀ + χ₁)) ℂ) :
    Commute (W.averageMatrix 2 (mixedEndpointInteractionMatrix A₀ A₁ γ))
      (MPOTensor.mpoWithBoundary W.tensor X 2) := by
  have hc := mixedWeakHopfCompletedInteraction_commute
    A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ W h₀ h₁ hW hInj₀ hInj₁ hγ X
  rw [mixedWeakHopfCompletedInteraction_eq
    A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ W h₀ h₁ hW hInj₀ hInj₁ hγ] at hc
  rw [averageMatrix_mixedEndpointInteraction
    A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ W h₀ h₁ hW hInj₀ hInj₁ hγ]
  exact ((W.rep_one_commute_mpoWithBoundary (by decide) X).sub_left
    (Commute.one_left _)).add_left hc

include h₀ h₁ hW hInj₀ hInj₁ in
/-- Every periodic completed active Hamiltonian commutes with the common MPO
on rings of length at least two. -/
theorem hamiltonian_mixedWeakHopfCompletedInteraction_commute
    [NeZero D₀] [NeZero D₁] {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩; Commute (Interaction.translationInvariant N
        (mixedWeakHopfCompletedInteraction A₀ A₁ W γ)).hamiltonian
      (MPOTensor.mpo W.tensor N) := by
  have : NeZero N := ⟨by omega⟩
  rw [← MPOTensor.mpoWithBoundary_one]
  exact Commute.sum_left _ _ _ fun i _ =>
    MPOTensor.placeAlong_ringWindow_commute_mpoWithBoundary _ hN i _
      (mixedWeakHopfCompletedInteraction_commute
        A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ W h₀ h₁ hW hInj₀ hInj₁ hγ)
      (Subalgebra.one_mem _)

include h₀ h₁ hW hInj₀ hInj₁ in
/-- The periodic sum of literal active averages commutes with the periodic
common MPO on every ring of length at least two. No spectral claim is made. -/
theorem hamiltonian_averageMatrix_mixedEndpointInteraction_commute
    [FiniteDimensional ℂ H] [NeZero D₀] [NeZero D₁]
    {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩; Commute (Interaction.translationInvariant N
      (W.averageMatrix 2 (mixedEndpointInteractionMatrix A₀ A₁ γ))).hamiltonian
      (MPOTensor.mpo W.tensor N) := by
  have : NeZero N := ⟨by omega⟩
  rw [← MPOTensor.mpoWithBoundary_one]
  exact Commute.sum_left _ _ _ fun i _ =>
    MPOTensor.placeAlong_ringWindow_commute_mpoWithBoundary _ hN i _
      (averageMatrix_mixedEndpointInteraction_commute
        A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ W h₀ h₁ hW hInj₀ hInj₁ hγ)
      (Subalgebra.one_mem _)

end MPSTensor.MPOSymmetry
