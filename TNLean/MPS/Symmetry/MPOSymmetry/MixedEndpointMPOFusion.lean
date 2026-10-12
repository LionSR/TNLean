/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointMPOFusionMaps
import TNLean.MPS.MPDO.BoundaryActionCrossFusionEntries
import TNLean.MPS.MPDO.BoundaryMultiplicity

/-!
# Exact fusion of the mixed endpoint MPO

The actual mixed endpoint operators inherit exact biorthogonal fusion from
endpoint fusion and action decompositions with equal actual raw L matrices.
The fusion maps retain the matching virtual sectors and annihilate the
unmatched sectors. Arbitrary-boundary products and periodic fusion follow.

Equality of the chosen raw L matrices is already-aligned data. No common
F matrix, operator injectivity, or ambient completeness is assumed. The
construction does not prove gauge alignment, mixed-operator injectivity,
physical adjoint closure, Hamiltonian symmetry, or full classification.

Source: Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3,
`REsubmission.tex`, lines 1667--1685, using `fusiontensors`, `eq:orthoW`,
`fusiontensors2`, `eq:orthoV`, and `eq:F_symbol2`.
-/

open scoped Matrix BigOperators Kronecker

namespace MPSTensor.MPOSymmetry

private theorem endpoint_fusion_entry {d r : ℕ} {χ : Fin r → ℕ}
    {N : Fin r → Fin r → Fin r → ℕ}
    (O : ∀ a, MPOTensor d (χ a))
    (VF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ c)) (Fin (χ a * χ b)) ℂ)
    (WF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ)
    (a b : Fin r)
    (h : IsBiorthogonalDecomposition (MPOTensor.mulTensor (O a) (O b)).toMPSTensor
      (fun q : (c : Fin r) × Fin (N a b c) ↦ (O q.1).toMPSTensor)
      (fun q ↦ VF a b q.1 q.2) (fun q ↦ WF a b q.1 q.2))
    (i j : Fin d) (α γ : Fin (χ a)) (β δ : Fin (χ b)) :
    (∑ k, O a i k α γ * O b k j β δ) =
      ∑ c, ∑ μ : Fin (N a b c),
        (WF a b c μ * (O c i j * VF a b c μ))
          (finProdFinEquiv (α, β)) (finProdFinEquiv (γ, δ)) := by
  have he := congrArg
    (fun Z ↦ Z (finProdFinEquiv (α, β)) (finProdFinEquiv (γ, δ)))
    (h.letter (finProdFinEquiv (i, j)))
  simpa only [MPOTensor.toMPSTensor, finProdFinEquiv_divNat,
    finProdFinEquiv_modNat, MPOTensor.mulTensor, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.sum_apply, Matrix.kroneckerMap_apply,
    Fintype.sum_sigma, Matrix.mul_assoc] using he

section Fusion

variable {r D₀ D₁ : ℕ} {χ₀ χ₁ : Fin r → ℕ}
  {N : Fin r → Fin r → Fin r → ℕ} {m : Fin r → ℕ}
  (O₀ : ∀ a, MPOTensor (D₀ * D₀) (χ₀ a))
  (O₁ : ∀ a, MPOTensor (D₁ * D₁) (χ₁ a))
  (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
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
/-- Fusion reconstruction in the direct-sum physical and bond coordinates.
The two diagonal sectors use endpoint fusion; the cross sectors use the
actual L relations. Source: GLM23, lines 1667--1685. -/
theorem mixedEndpointMPOLetter_fusion (a b : Fin r)
    (hL : MPOTensor.actionLMatrix WF₀ (fun a (_ _ : Fin 1) ↦ VA₀ a)
        (fun a _ _ ↦ WA₀ a) a b 0 0 =
      MPOTensor.actionLMatrix WF₁ (fun a (_ _ : Fin 1) ↦ VA₁ a)
        (fun a _ _ ↦ WA₁ a) a b 0 0)
    (r s k l : Fin D₀ ⊕ Fin D₁)
    (α γ : Fin (χ₀ a) ⊕ Fin (χ₁ a)) (β δ : Fin (χ₀ b) ⊕ Fin (χ₁ b)) :
    (∑ u : Fin D₀ ⊕ Fin D₁, ∑ v : Fin D₀ ⊕ Fin D₁,
      mixedEndpointMPOLetter (O₀ a) (O₁ a) (VA₀ a) (VA₁ a) (WA₀ a) (WA₁ a)
        r s u v α γ *
      mixedEndpointMPOLetter (O₀ b) (O₁ b) (VA₀ b) (VA₁ b) (WA₀ b) (WA₁ b)
        u v k l β δ) =
      ∑ c, ∑ μ : Fin (N a b c),
        (mixedEndpointFusionSynthesis (WF₀ a b c μ) (WF₁ a b c μ) *
          mixedEndpointMPOLetter (O₀ c) (O₁ c) (VA₀ c) (VA₁ c) (WA₀ c) (WA₁ c)
            r s k l *
          mixedEndpointFusionAnalysis (VF₀ a b c μ) (VF₁ a b c μ)) (α, β) (γ, δ) := by
  classical
  simp_rw [Matrix.mul_assoc]
  cases r <;> cases s <;> cases k <;> cases l <;>
    simp only [Matrix.mul_apply,
      Fintype.sum_sum_type, mixedEndpointMPOLetter, zero_mul, mul_zero,
      Finset.sum_const_zero, zero_add, add_zero]
  all_goals
    cases α <;> cases β <;> cases γ <;> cases δ <;>
      simp only [mixedEndpointFusionAnalysis, mixedEndpointFusionSynthesis,
        zero_mul, mul_zero, Finset.sum_const_zero]
  · simpa only [Matrix.mul_apply, ← finProdFinEquiv.sum_comp,
      Fintype.sum_prod_type] using
      endpoint_fusion_entry O₀ VF₀ WF₀ a b (hF₀ a b) _ _ _ _ _ _
  · simpa only [Finset.mul_sum, Finset.sum_mul, mul_assoc] using
      MPOTensor.crossEndpoint_fusion_entry_of_actionLMatrix_eq
      VF₀ WF₀ VA₀ WA₀ VF₁ WF₁ VA₁ WA₁ hF₀ hA₀ hF₁ hA₁
      hInj₀ hInj₁ hD₀ hD₁ a b hL _ _ _ _ _ _ _ _
  · simpa only [Finset.mul_sum, Finset.sum_mul, mul_assoc] using
      MPOTensor.crossEndpoint_fusion_entry_of_actionLMatrix_eq
      VF₁ WF₁ VA₁ WA₁ VF₀ WF₀ VA₀ WA₀ hF₁ hA₁ hF₀ hA₀
      hInj₁ hInj₀ hD₁ hD₀ a b hL.symm _ _ _ _ _ _ _ _
  · simpa only [Matrix.mul_apply, ← finProdFinEquiv.sum_comp,
      Fintype.sum_prod_type] using
      endpoint_fusion_entry O₁ VF₁ WF₁ a b (hF₁ a b) _ _ _ _ _ _


include hF₀ hA₀ hF₁ hA₁ hInj₀ hInj₁ hD₀ hD₁ in
/-- The actual mixed MPOs have exact biorthogonal fusion into copies of
labelled mixed MPOs, with the original fusion multiplicities. Equal raw L
matrices are required only for the selected pair of labels.
Source: GLM23, `fusiontensors`, `eq:orthoW`, and lines 1667--1685. -/
theorem isBiorthogonalDecomposition_mixedEndpointMPO (a b : Fin r)
    (hL : MPOTensor.actionLMatrix WF₀ (fun a (_ _ : Fin 1) ↦ VA₀ a)
        (fun a _ _ ↦ WA₀ a) a b 0 0 =
      MPOTensor.actionLMatrix WF₁ (fun a (_ _ : Fin 1) ↦ VA₁ a)
        (fun a _ _ ↦ WA₁ a) a b 0 0) :
    IsBiorthogonalDecomposition
      (MPOTensor.mulTensor
        (mixedEndpointMPO (O₀ a) (O₁ a) (VA₀ a) (VA₁ a) (WA₀ a) (WA₁ a))
        (mixedEndpointMPO (O₀ b) (O₁ b) (VA₀ b) (VA₁ b) (WA₀ b) (WA₁ b))).toMPSTensor
      (fun q : (c : Fin r) × Fin (N a b c) ↦
        (mixedEndpointMPO (O₀ q.1) (O₁ q.1) (VA₀ q.1) (VA₁ q.1)
          (WA₀ q.1) (WA₁ q.1)).toMPSTensor)
      (fun q ↦ mixedEndpointMPOFusionAnalysis (VF₀ a b q.1 q.2) (VF₁ a b q.1 q.2))
      (fun q ↦ mixedEndpointMPOFusionSynthesis (WF₀ a b q.1 q.2) (WF₁ a b q.1 q.2)) where
  retract q := by
    rw [mixedEndpointMPOFusionAnalysis_mul_synthesis, (hF₀ a b).retract q,
      (hF₁ a b).retract q, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
  orthogonal q t hqt := by
    rw [mixedEndpointMPOFusionAnalysis_mul_synthesis,
      (hF₀ a b).orthogonal q t hqt, (hF₁ a b).orthogonal q t hqt,
      Matrix.fromBlocks_zero]
    rfl
  letter p := by
    classical
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective p
    simp only [MPOTensor.toMPSTensor, finProdFinEquiv_divNat, finProdFinEquiv_modNat]
    obtain ⟨⟨r, s⟩, rfl⟩ := (mixedEndpointPhysicalEquiv D₀ D₁).surjective i
    obtain ⟨⟨k, l⟩, rfl⟩ := (mixedEndpointPhysicalEquiv D₀ D₁).surjective j
    ext x y
    obtain ⟨⟨α, β⟩, rfl⟩ :=
      (mixedEndpointActedEquiv (χ₀ a) (χ₁ a) (χ₀ b) (χ₁ b)).surjective x
    obtain ⟨⟨γ, δ⟩, rfl⟩ :=
      (mixedEndpointActedEquiv (χ₀ a) (χ₁ a) (χ₀ b) (χ₁ b)).surjective y
    simp only [MPOTensor.mulTensor, Matrix.submatrix_apply, Matrix.sum_apply,
      Matrix.kroneckerMap_apply]
    rw [← (mixedEndpointPhysicalEquiv D₀ D₁).sum_comp, Fintype.sum_prod_type]
    simp only [mixedEndpointMPO_physicalEquiv, mixedEndpointMPOFusion_sandwich,
      Matrix.submatrix_apply, Equiv.symm_apply_apply, mixedEndpointActedEquiv,
      Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply, Equiv.symm_apply_apply]
    simpa only [Equiv.symm_trans, Equiv.prodCongr_symm, Equiv.trans_apply,
      Equiv.prodCongr_apply, Prod.map_apply, Equiv.symm_apply_apply,
      Fintype.sum_sigma] using
      mixedEndpointMPOLetter_fusion O₀ O₁ A₀ A₁ VF₀ WF₀ VA₀ WA₀ VF₁ WF₁ VA₁ WA₁
        hF₀ hA₀ hF₁ hA₁ hInj₀ hInj₁ hD₀ hD₁ a b hL r s k l α γ β δ

include hF₀ hA₀ hF₁ hA₁ hInj₀ hInj₁ hD₀ hD₁ in
/-- Products of arbitrary-boundary mixed operators have one explicit output
boundary per fusion channel, valid at every positive length. This is a
family-wise formula and does not assert single-tensor boundary closedness.
Source: GLM23, `algcond`, `fusiontensors`, and lines 1667--1685. -/
theorem mpoWithBoundary_mixedEndpointMPO_mul (a b : Fin r)
    (hL : MPOTensor.actionLMatrix WF₀ (fun a (_ _ : Fin 1) ↦ VA₀ a)
        (fun a _ _ ↦ WA₀ a) a b 0 0 =
      MPOTensor.actionLMatrix WF₁ (fun a (_ _ : Fin 1) ↦ VA₁ a)
        (fun a _ _ ↦ WA₁ a) a b 0 0)
    (X : Matrix (Fin (χ₀ a + χ₁ a)) (Fin (χ₀ a + χ₁ a)) ℂ)
    (Y : Matrix (Fin (χ₀ b + χ₁ b)) (Fin (χ₀ b + χ₁ b)) ℂ)
    {L : ℕ} (hLength : 0 < L) :
    let T := fun a ↦ mixedEndpointMPO (O₀ a) (O₁ a) (VA₀ a) (VA₁ a) (WA₀ a) (WA₁ a)
    MPOTensor.mpoWithBoundary (T a) X L * MPOTensor.mpoWithBoundary (T b) Y L =
      ∑ c, ∑ μ : Fin (N a b c), MPOTensor.mpoWithBoundary (T c)
        (mixedEndpointMPOFusionAnalysis (VF₀ a b c μ) (VF₁ a b c μ) *
          MPOTensor.productBoundary X Y *
          mixedEndpointMPOFusionSynthesis (WF₀ a b c μ) (WF₁ a b c μ)) L := by
  classical
  let T := fun a ↦ mixedEndpointMPO (O₀ a) (O₁ a) (VA₀ a) (VA₁ a) (WA₀ a) (WA₁ a)
  simpa only [Fintype.sum_sigma] using
    MPOTensor.mpoWithBoundary_mul_eq_sum_of_biorthogonalDecomposition
      (T a) (T b) (fun q : (c : Fin r) × Fin (N a b c) ↦ T q.1)
      (fun q ↦ mixedEndpointMPOFusionAnalysis (VF₀ a b q.1 q.2) (VF₁ a b q.1 q.2))
      (fun q ↦ mixedEndpointMPOFusionSynthesis (WF₀ a b q.1 q.2) (WF₁ a b q.1 q.2))
      (isBiorthogonalDecomposition_mixedEndpointMPO
        O₀ O₁ A₀ A₁ VF₀ WF₀ VA₀ WA₀ VF₁ WF₁ VA₁ WA₁
        hF₀ hA₀ hF₁ hA₁ hInj₀ hInj₁ hD₀ hD₁ a b hL) X Y hLength

include hF₀ hA₀ hF₁ hA₁ hInj₀ hInj₁ hD₀ hD₁ in
/-- The mixed operator family has exactly the endpoint fusion coefficients
at every positive periodic length. Source: GLM23, `fusiontensors` and
lines 1667--1685. -/
theorem isMPOFusionAlgebra_mixedEndpointMPO
    (hL : ∀ a b, MPOTensor.actionLMatrix WF₀ (fun a (_ _ : Fin 1) ↦ VA₀ a)
        (fun a _ _ ↦ WA₀ a) a b 0 0 =
      MPOTensor.actionLMatrix WF₁ (fun a (_ _ : Fin 1) ↦ VA₁ a)
        (fun a _ _ ↦ WA₁ a) a b 0 0) :
    MPOTensor.IsMPOFusionAlgebra
      (fun a ↦ mixedEndpointMPO (O₀ a) (O₁ a) (VA₀ a) (VA₁ a) (WA₀ a) (WA₁ a)) N :=
  MPOTensor.isMPOFusionAlgebra_of_biorthogonalDecompositions
    (fun a b c μ ↦ mixedEndpointMPOFusionAnalysis (VF₀ a b c μ) (VF₁ a b c μ))
    (fun a b c μ ↦ mixedEndpointMPOFusionSynthesis (WF₀ a b c μ) (WF₁ a b c μ))
    (fun a b ↦ isBiorthogonalDecomposition_mixedEndpointMPO
      O₀ O₁ A₀ A₁ VF₀ WF₀ VA₀ WA₀ VF₁ WF₁ VA₁ WA₁
      hF₀ hA₀ hF₁ hA₁ hInj₀ hInj₁ hD₀ hD₁ a b (hL a b))

end Fusion

end MPSTensor.MPOSymmetry
