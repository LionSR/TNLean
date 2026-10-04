/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import TNLean.Algebra.UnitaryGeneralLinearInverse
import TNLean.MPS.ParentHamiltonian.PhysicalDeformation
import TNLean.MPS.Symmetry.BondProductPhysicalSymmetry
import TNLean.MPS.Symmetry.FixedPointGappedPath

/-!
# Local symmetry of the normalized bond interpolation

Every two-site term of the normalized direct-sum bond interpolation is
invariant under the physical on-site symmetry.
Source: arXiv:1010.3732, Section II.F.2, equation eq:1d-sym:jointsym.
-/

open scoped Matrix Kronecker

namespace MPOTensor

/-- Embedding an operator on the entire chain at the origin preserves it. -/
theorem embedLocalOperator_full_zero {d N : ℕ} [NeZero N]
    (B : ChainOperator d N) : embedLocalOperator N N le_rfl 0 B = B := by
  ext σ τ
  unfold embedLocalOperator AgreesOutsideWindow MPSTensor.replaceWindow MPSTensor.extractWindow
  simp (disch := exact Fin.isLt _) [Nat.mod_eq_of_lt]

end MPOTensor

namespace MPSTensor

/-- Each local normalized bond interaction commutes with the two-site
physical symmetry. Source: arXiv:1010.3732, Section II.F.2,
equation eq:1d-sym:jointsym. -/
theorem normalizedBondInteraction_commute_onSite
    {G : Type} [Group G] {D₀ D₁ : ℕ}
    {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈
      Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈
      Matrix.unitaryGroup _ ℂ)
    (g : G) (γ : ℝ) :
    Commute (normalizedBondInteraction D₀ D₁ γ)
      (onSiteTensorPow 2 (sptFixedPointAction (ρ₀.directSum ρ₁) 1 g)) := by
  let ρ := ρ₀.directSum ρ₁
  let X : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ := ρ.X g⁻¹
  let S := Matrix.reindex finProdFinEquiv finProdFinEquiv (Xᴴ ⊗ₖ Xᵀ)
  have hX : X ∈ Matrix.unitaryGroup (Fin (D₀ + D₁)) ℂ :=
    ρ₀.directSum_mem_unitaryGroup ρ₁ g⁻¹ (h₀ g⁻¹) (h₁ g⁻¹)
  have hS : S ∈ Matrix.unitaryGroup (Fin ((D₀ + D₁) * (D₀ + D₁))) ℂ :=
    Matrix.reindex_mem_unitaryGroup finProdFinEquiv (Xᴴ ⊗ₖ Xᵀ)
      (Matrix.kronecker_mem_unitary (Unitary.star_mem hX)
        (Matrix.transpose_mem_unitaryGroup_iff.mpr hX))
  have hfix : S *ᵥ normalizedBondInterpolationVector D₀ D₁ γ =
      normalizedBondInterpolationVector D₀ D₁ γ :=
    normalizedBondInterpolationVector_fixed_directSum
      ρ₀ ρ₁ g⁻¹ γ (h₀ g⁻¹) (h₁ g⁻¹)
  let P := (incomingBondPerm (D₀ + D₁) 2).permMatrix ℂ
  let U : Matrix.unitaryGroup (Cfg ((D₀ + D₁) * (D₀ + D₁)) 2) ℂ :=
    ⟨P, incomingBondPerm_mem_unitaryGroup (D₀ + D₁) 2⟩
  have hlocal :=
    (bondPenaltyAt_commute_sitewise_of_unitary_fixed (N := 2)
      (normalizedBondInterpolationVector D₀ D₁ γ) S hS hfix (by omega)
      (finRotate 2 0)).map (Unitary.conjStarAlgAut ℂ _ U)
  simp only [Unitary.conjStarAlgAut_apply, U, Matrix.star_eq_conjTranspose] at hlocal
  have haction : P * MPOTensor.sitewiseMatrixFamily (fun _ : Fin 2 => S) * Pᴴ =
      onSiteTensorPow 2 (sptFixedPointAction ρ 1 g) := by
    change P * Matrix.finKronecker (fun _ : Fin 2 => S) * Pᴴ = _
    simpa only [P, S, X, onSiteTensorPow_eq_finKronecker,
      MPOTensor.sitewiseMatrixFamily, Matrix.finKronecker_apply, sptGauge,
      Matrix.coe_gl_inv_eq_conjTranspose_of_mem_unitaryGroup (ρ.X g⁻¹) hX] using
        incomingBondPerm_conj_sptFixedPointAction ρ g 2
  have hBond : P * bondPenaltyAt (normalizedBondInterpolationVector D₀ D₁ γ)
      (by omega) (finRotate 2 0) * Pᴴ = normalizedBondInteraction D₀ D₁ γ := by
    have h := embed_twoSiteBondInteraction_eq_conj (N := 2) (by omega) 0
      (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
        (bondPenalty (normalizedBondInterpolationVector D₀ D₁ γ)))
    rw [MPOTensor.embedLocalOperator_full_zero] at h
    simpa only [normalizedBondInteraction, bondPenaltyAt, P,
      ← Matrix.reindex_symm, Equiv.apply_symm_apply] using h.symm
  rw [haction, hBond] at hlocal
  exact hlocal.symm

end MPSTensor
