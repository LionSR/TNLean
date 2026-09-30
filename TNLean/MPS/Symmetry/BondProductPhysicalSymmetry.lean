/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.BondProductHamiltonianSymmetry
import TNLean.MPS.Symmetry.BondProductPhysicalParentHamiltonian
import TNLean.MPS.Symmetry.BondRegroupingSymmetry

/-!
# Symmetry of the physical bond-product Hamiltonian

The incoming-bond permutation carries the sitewise bond action to the
physical on-site action. Consequently, invariance of the normalized bond
vector implies invariance of every finite-chain parent Hamiltonian.
Source: Schuch--Pérez-García--Cirac, arXiv:1010.3732, Section II.F.2.
-/

open scoped Matrix BigOperators Kronecker

namespace MPSTensor

/-- Unitary regrouping carries bond-Hamiltonian symmetry to physical
coordinates. Source: arXiv:1010.3732, Section II.F.2,
`eq:1d-sym:jointsym`. -/
theorem physicalBondProductParentHamiltonian_commute_of_bond_action
    {D N : ℕ} (η : Fin (D * D) → ℂ)
    (S : Matrix (Fin (D * D)) (Fin (D * D)) ℂ)
    (T : MPOTensor.ChainOperator (D * D) N)
    (hS : S ∈ Matrix.unitaryGroup (Fin (D * D)) ℂ)
    (hη : S *ᵥ η = η) (hN : 1 ≤ N)
    (hT : (incomingBondPerm D N).permMatrix ℂ *
      MPOTensor.sitewiseMatrixFamily (fun _ : Fin N => S) *
      ((incomingBondPerm D N).permMatrix ℂ)ᴴ = T) :
    Commute T (physicalBondProductParentHamiltonian η hN) := by
  let P := (incomingBondPerm D N).permMatrix ℂ
  let A := MPOTensor.sitewiseMatrixFamily (fun _ : Fin N => S)
  let H := bondProductParentHamiltonian η hN
  have hP : Pᴴ * P = 1 :=
    (Matrix.mem_unitaryGroup_iff').mp (incomingBondPerm_mem_unitaryGroup D N)
  have hAH : A * H = H * A :=
    (commute_iff_eq A H).mp
      (bondProductParentHamiltonian_commute_sitewise_of_unitary_fixed
        η S hS hη hN)
  rw [← hT]
  change Commute (P * A * Pᴴ) (P * H * Pᴴ)
  apply (commute_iff_eq _ _).2
  calc
    (P * A * Pᴴ) * (P * H * Pᴴ) = P * (A * H) * Pᴴ := by
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Pᴴ P, hP,
        Matrix.one_mul]
    _ = P * (H * A) * Pᴴ := by rw [hAH]
    _ = (P * H * Pᴴ) * (P * A * Pᴴ) := by
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Pᴴ P, hP,
        Matrix.one_mul]

/-- The physical parent Hamiltonian of the normalized interpolation commutes
with the on-site symmetry at every chain length. Source: arXiv:1010.3732,
Section II.F.2, `eq:1d-sym:jointsym`. -/
theorem normalizedPhysicalBondInterpolation_parent_commute_onSite
    {G : Type*} [Group G] {D₀ D₁ N : ℕ}
    {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈
      Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈
      Matrix.unitaryGroup _ ℂ)
    (g : G) (γ : ℝ) (hN : 1 ≤ N) :
    Commute
      (Matrix.finKronecker (fun _ : Fin N =>
        (ρ₀.directSum ρ₁).onSiteMatrix g))
      (physicalBondProductParentHamiltonian
        (normalizedBondInterpolationVector D₀ D₁ γ) hN) := by
  let ρ := ρ₀.directSum ρ₁
  let X : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ := ρ.X g⁻¹
  let Y : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ :=
    ((ρ.X g⁻¹)⁻¹ : GL (Fin (D₀ + D₁)) ℂ)
  let S := Matrix.reindex finProdFinEquiv finProdFinEquiv (Y ⊗ₖ Xᵀ)
  have hX : X ∈ Matrix.unitaryGroup (Fin (D₀ + D₁)) ℂ :=
    ρ₀.directSum_mem_unitaryGroup ρ₁ g⁻¹ (h₀ g⁻¹) (h₁ g⁻¹)
  have hY : Y = Xᴴ := by
    let Q : Matrix.unitaryGroup (Fin (D₀ + D₁)) ℂ := ⟨X, hX⟩
    have hQ : Unitary.toUnits Q = ρ.X g⁻¹ := Units.ext rfl
    dsimp [Y, X]
    rw [← hQ]
    rfl
  have hS : S ∈ Matrix.unitaryGroup (Fin ((D₀ + D₁) * (D₀ + D₁))) ℂ := by
    dsimp [S]
    apply Matrix.reindex_mem_unitaryGroup
    apply Matrix.kronecker_mem_unitary
    · rw [hY]
      exact Unitary.star_mem hX
    · exact Matrix.transpose_mem_unitaryGroup_iff.mpr hX
  have hfix : S *ᵥ normalizedBondInterpolationVector D₀ D₁ γ =
      normalizedBondInterpolationVector D₀ D₁ γ := by
    rw [show S = Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Xᴴ ⊗ₖ Xᵀ) from by dsimp [S]; rw [hY]]
    exact normalizedBondInterpolationVector_fixed_directSum
      ρ₀ ρ₁ g⁻¹ γ (h₀ g⁻¹) (h₁ g⁻¹)
  apply physicalBondProductParentHamiltonian_commute_of_bond_action
    (normalizedBondInterpolationVector D₀ D₁ γ) S _ hS hfix hN
  change (incomingBondPerm (D₀ + D₁) N).permMatrix ℂ *
      Matrix.finKronecker (fun _ : Fin N => S) *
      ((incomingBondPerm (D₀ + D₁) N).permMatrix ℂ)ᴴ = _
  simpa only [S, X, Y, MPOTensor.sitewiseMatrixFamily,
    Matrix.finKronecker_apply] using
    incomingBondPerm_conj_onSiteAction ρ g N

end MPSTensor
