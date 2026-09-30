/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.BondProductEndpointPeriodicGroundSpace
import TNLean.MPS.Symmetry.ParentHamiltonianSymmetry
import TNLean.MPS.Symmetry.ProjectiveDirectSum
import TNLean.MPS.Symmetry.InjectiveParentGappedPath

/-!
# Symmetry of the first embedded fixed-point endpoint

The first matrix-unit fixed point occupies the first summand of the common
physical space. Its canonical parent Hamiltonian commutes with the physical
action induced by the common-factor virtual direct sum.

Source: arXiv:1010.3732, Section II.F.2, equation `eq:1d-sym:jointsym`.
-/

open scoped Matrix
open TNLean.Algebra

namespace MPSTensor

private theorem directSum_X_apply
    {G : Type*} [Group G] {D₀ D₁ : ℕ} {ω : ScalarCocycle G}
    (ρ₀ : ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : ProjectiveRepresentation (D := D₁) ω) (g : G)
    (a b : Fin D₀ ⊕ Fin D₁) :
    ((ρ₀.directSum ρ₁).X g : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ)
      (finSumFinEquiv a) (finSumFinEquiv b) =
      (Matrix.fromBlocks (ρ₀.X g).val 0 0 (ρ₁.X g).val) a b := by
  change (Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (ρ₀.X g).val 0 0 (ρ₁.X g).val))
    (finSumFinEquiv a) (finSumFinEquiv b) = _
  simp

private theorem directSum_X_inv_apply
    {G : Type*} [Group G] {D₀ D₁ : ℕ} {ω : ScalarCocycle G}
    (ρ₀ : ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : ProjectiveRepresentation (D := D₁) ω) (g : G)
    (a b : Fin D₀ ⊕ Fin D₁) :
    (((ρ₀.directSum ρ₁).X g)⁻¹ : GL (Fin (D₀ + D₁)) ℂ).val
      (finSumFinEquiv a) (finSumFinEquiv b) =
      (Matrix.fromBlocks (ρ₀.X g).inv 0 0 (ρ₁.X g).inv) a b := by
  change (Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (ρ₀.X g).inv 0 0 (ρ₁.X g).inv))
    (finSumFinEquiv a) (finSumFinEquiv b) = _
  simp

private theorem directSum_onSite_apply_first
    {G : Type*} [Group G] {D₀ D₁ : ℕ} {ω : ScalarCocycle G}
    (ρ₀ : ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : ProjectiveRepresentation (D := D₁) ω) (g : G)
    (a b : Fin D₀ ⊕ Fin D₁) (c d : Fin D₀) :
    (ρ₀.directSum ρ₁).onSiteMatrix g
      (finProdFinEquiv (finSumFinEquiv a, finSumFinEquiv b))
      (finProdFinEquiv (finSumFinEquiv (Sum.inl c),
        finSumFinEquiv (Sum.inl d))) =
      match a, b with
      | Sum.inl a, Sum.inl b => ρ₀.onSiteMatrix g
          (finProdFinEquiv (a, b)) (finProdFinEquiv (c, d))
      | _, _ => 0 := by
  cases a <;> cases b <;>
    simp only [ProjectiveRepresentation.onSiteMatrix_apply_pairs,
      directSum_X_apply, directSum_X_inv_apply]
  all_goals simp

private theorem mul_leftPhysicalIsometry_apply_pair (D₀ D₁ : ℕ)
    (U : Matrix (Fin ((D₀ + D₁) * (D₀ + D₁)))
      (Fin ((D₀ + D₁) * (D₀ + D₁))) ℂ)
    (p : Fin ((D₀ + D₁) * (D₀ + D₁))) (c d : Fin D₀) :
    (U * leftPhysicalIsometry D₀ D₁) p (finProdFinEquiv (c, d)) =
      U p (finProdFinEquiv
        (finSumFinEquiv (Sum.inl c), finSumFinEquiv (Sum.inl d))) := by
  classical
  rw [Matrix.mul_apply]
  let q : Fin ((D₀ + D₁) * (D₀ + D₁)) := finProdFinEquiv
    (finSumFinEquiv (Sum.inl c), finSumFinEquiv (Sum.inl d))
  calc
    (∑ j, U p j * leftPhysicalIsometry D₀ D₁ j (finProdFinEquiv (c, d))) =
        U p q * leftPhysicalIsometry D₀ D₁ q (finProdFinEquiv (c, d)) := by
      apply Finset.sum_eq_single q
      · intro j _ hj
        rw [leftPhysicalIsometry_apply_pair]
        have hneq : j ≠ finProdFinEquiv
            (finSumFinEquiv (Sum.inl c), finSumFinEquiv (Sum.inl d)) := by
          simpa only [q] using hj
        change j ≠ finProdFinEquiv (Fin.castAdd D₁ c, Fin.castAdd D₁ d) at hneq
        simp [hneq]
      · simp
    _ = U p q := by simp [q, leftPhysicalIsometry_apply_pair]

/-- The first-summand physical inclusion intertwines the induced on-site
actions. Source: arXiv:1010.3732, Section II.F.2,
equation `eq:1d-sym:jointsym`. -/
theorem leftPhysicalIsometry_intertwines_onSiteMatrix
    {G : Type*} [Group G] {D₀ D₁ : ℕ} {ω : ScalarCocycle G}
    (ρ₀ : ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : ProjectiveRepresentation (D := D₁) ω) (g : G) :
    (ρ₀.directSum ρ₁).onSiteMatrix g * leftPhysicalIsometry D₀ D₁ =
      leftPhysicalIsometry D₀ D₁ * ρ₀.onSiteMatrix g := by
  classical
  let U : Matrix (Fin ((D₀ + D₁) * (D₀ + D₁)))
      (Fin ((D₀ + D₁) * (D₀ + D₁))) ℂ :=
    (ρ₀.directSum ρ₁).onSiteMatrix g
  let U₀ : Matrix (Fin (D₀ * D₀)) (Fin (D₀ * D₀)) ℂ := ρ₀.onSiteMatrix g
  change U * leftPhysicalIsometry D₀ D₁ = leftPhysicalIsometry D₀ D₁ * U₀
  ext p q
  obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨c, d⟩, rfl⟩ := finProdFinEquiv.surjective q
  rw [mul_leftPhysicalIsometry_apply_pair]
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective a
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective b
  cases a <;> cases b
  all_goals
    conv_rhs =>
      rw [Matrix.mul_apply]
      rw [← (finProdFinEquiv : Fin D₀ × Fin D₀ ≃ Fin (D₀ * D₀)).sum_comp]
    simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      Fintype.sum_prod_type, leftPhysicalIsometry_apply_pair,
      EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq, Fin.castAdd_inj,
      ite_mul, one_mul, zero_mul]
  case inl.inl a b =>
    conv_rhs => simp only [ite_and, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simpa [U, U₀] using directSum_onSite_apply_first ρ₀ ρ₁ g
      (Sum.inl a) (Sum.inl b) c d
  case inl.inr a b =>
    have hne (x : Fin D₀) : Fin.natAdd D₀ b ≠ Fin.castAdd D₁ x := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
      omega
    conv_rhs => simp only [hne, and_false, ite_false, Finset.sum_const_zero]
    simpa [U] using directSum_onSite_apply_first ρ₀ ρ₁ g
      (Sum.inl a) (Sum.inr b) c d
  case inr.inl a b =>
    have hne (x : Fin D₀) : Fin.natAdd D₀ a ≠ Fin.castAdd D₁ x := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
      omega
    conv_rhs => simp only [hne, false_and, ite_false, Finset.sum_const_zero]
    simpa [U] using directSum_onSite_apply_first ρ₀ ρ₁ g
      (Sum.inr a) (Sum.inl b) c d
  case inr.inr a b =>
    have hne (x : Fin D₀) : Fin.natAdd D₀ a ≠ Fin.castAdd D₁ x := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
      omega
    conv_rhs => simp only [hne, false_and, ite_false, Finset.sum_const_zero]
    simpa [U] using directSum_onSite_apply_first ρ₀ ρ₁ g
      (Sum.inr a) (Sum.inr b) c d

/-- The first embedded endpoint has exact virtual covariance under the common
direct-sum on-site action. Source: arXiv:1010.3732, Section II.F.2. -/
theorem leftEmbeddedMatrixUnitFixedPoint_gaugeEquiv_rotatePhysical
    {G : Type*} [Group G] {D₀ D₁ : ℕ} [NeZero D₀] {ω : ScalarCocycle G}
    (ρ₀ : ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : ProjectiveRepresentation (D := D₁) ω) (g : G) :
    GaugeEquiv (leftEmbeddedMatrixUnitFixedPoint D₀ D₁)
      (rotatePhysical ((ρ₀.directSum ρ₁).onSiteMatrix g)
        (leftEmbeddedMatrixUnitFixedPoint D₀ D₁)) := by
  rw [leftEmbeddedMatrixUnitFixedPoint_eq_physicalEmbedding]
  apply gaugeEquiv_physicalEmbedding_of_intertwining
    _ (leftPhysicalIsometry D₀ D₁) (ρ₀.onSiteMatrix g)
    ((ρ₀.directSum ρ₁).onSiteMatrix g)
    (leftPhysicalIsometry_intertwines_onSiteMatrix ρ₀ ρ₁ g)
  let c : ℂ := (↑(Real.sqrt (D₀ : ℝ)) : ℂ)⁻¹
  refine ⟨ρ₀.X g⁻¹, fun p => ?_⟩
  have h := twistedTensor_matrixUnitFixedPoint ρ₀ g p
  dsimp only [twistedTensor] at h
  simpa only [c, ProjectiveRepresentation.adjoint, rotatePhysical, Finset.smul_sum, smul_smul,
    Matrix.mul_smul, Matrix.smul_mul, mul_comm c] using
    congrArg (fun M : Matrix (Fin D₀) (Fin D₀) ℂ => c • M) h

/-- The canonical periodic parent Hamiltonian of the first embedded endpoint
commutes with the common on-site physical symmetry. Source:
arXiv:1010.3732, Section II.F.2, equation `eq:1d-sym:jointsym`. -/
theorem leftEmbeddedMatrixUnitFixedPoint_parent_commute_onSite
    {G : Type*} [Group G] {D₀ D₁ : ℕ} [NeZero D₀] {ω : ScalarCocycle G}
    (ρ₀ : ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : ProjectiveRepresentation (D := D₁) ω)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈
      Matrix.unitaryGroup (Fin D₀) ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈
      Matrix.unitaryGroup (Fin D₁) ℂ)
    (g : G) (N : ℕ) (hN : 2 ≤ N) :
    Commute (interactionHamiltonian
        (canonicalParentMatrix (leftEmbeddedMatrixUnitFixedPoint D₀ D₁)) hN)
      (Matrix.finKronecker fun _ : Fin N => (ρ₀.directSum ρ₁).onSiteMatrix g) := by
  rw [← onSiteTensorPow_eq_finKronecker]
  unfold interactionHamiltonian
  apply (commute_iff_eq _ _).2
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact (embedLocalOperator_commute_onSiteTensorPow
    ((ρ₀.directSum ρ₁).onSiteMatrix g) 2 hN i
    (canonicalParentMatrix (leftEmbeddedMatrixUnitFixedPoint D₀ D₁))
    (parentInteraction_matrix_commute_onSiteTensorPow
      (leftEmbeddedMatrixUnitFixedPoint D₀ D₁)
      ((ρ₀.directSum ρ₁).onSiteMatrix g)
      (weightedMatrixUnitInterpolation_physical_unitary ρ₀ ρ₁ h₀ h₁ g)
      (leftEmbeddedMatrixUnitFixedPoint_gaugeEquiv_rotatePhysical ρ₀ ρ₁ g) 2)).eq

end MPSTensor
