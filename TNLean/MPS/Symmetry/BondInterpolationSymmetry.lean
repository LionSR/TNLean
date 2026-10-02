/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.BondInterpolation
import TNLean.MPS.Symmetry.ProjectiveDirectSum

/-!
# Symmetry of the interpolating bond

The coefficient matrix of the interpolating bond is scalar on each of the
two virtual summands. It therefore commutes with their direct-sum action.
For unitary virtual matrices this is precisely invariance of the bond under
the action on its two ends. Source: Schuch–Pérez-García–Cirac,
arXiv:1010.3732, Section II.F.2, equations `eq:sym:omega-gamma` and
`eq:1d-sym:jointsym`.

**Local fix (second-block range):** The second summand has dimension `D₁`
inside a space of dimension `D₀ + D₁`, as recorded in
`docs/paper-gaps/spc11_spt_interpolation_upper_range.tex`.
-/

open scoped Matrix
open TNLean.Algebra

namespace MPSTensor

/-- The bond interpolation is scalar on each direct summand. Source:
arXiv:1010.3732, Section II.F.2, equation `eq:sym:omega-gamma`, with the
second-block range corrected as in
`docs/paper-gaps/spc11_spt_interpolation_upper_range.tex`. -/
theorem bondInterpolationMatrix_eq_fromBlocks (D₀ D₁ : ℕ) (γ : ℝ) :
    bondInterpolationMatrix D₀ D₁ γ =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (((1 - γ : ℝ) : ℂ) • (1 : Matrix (Fin D₀) (Fin D₀) ℂ))
          0 0 ((γ : ℂ) • (1 : Matrix (Fin D₁) (Fin D₁) ℂ))) := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  cases i <;> cases j <;>
    simp [bondInterpolationMatrix, bondInterpolationWeight, Matrix.reindex_apply,
      Matrix.fromBlocks, Matrix.diagonal, Matrix.one_apply]
  all_goals simp only [Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd]
  all_goals omega

/-- The interpolating bond coefficient matrix commutes with the virtual
direct-sum action. Source: arXiv:1010.3732, Section II.F.2, equations
`eq:sym:omega-gamma` and `eq:1d-sym:jointsym`. -/
theorem bondInterpolationMatrix_commute_directSum
    {G : Type} [Group G] {D₀ D₁ : ℕ} {ω : ScalarCocycle G}
    (ρ₀ : ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : ProjectiveRepresentation (D := D₁) ω) (g : G) (γ : ℝ) :
    Commute (bondInterpolationMatrix D₀ D₁ γ)
      ((ρ₀.directSum ρ₁).X g : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ) := by
  change bondInterpolationMatrix D₀ D₁ γ * _ =
    _ * bondInterpolationMatrix D₀ D₁ γ
  rw [bondInterpolationMatrix_eq_fromBlocks]
  change (Matrix.reindexAlgEquiv ℂ ℂ finSumFinEquiv) _ *
    (Matrix.reindexAlgEquiv ℂ ℂ finSumFinEquiv)
      (Matrix.fromBlocks (ρ₀.X g).val 0 0 (ρ₁.X g).val) =
    (Matrix.reindexAlgEquiv ℂ ℂ finSumFinEquiv)
      (Matrix.fromBlocks (ρ₀.X g).val 0 0 (ρ₁.X g).val) *
    (Matrix.reindexAlgEquiv ℂ ℂ finSumFinEquiv) _
  rw [← map_mul, ← map_mul]
  simp [Matrix.fromBlocks_multiply]

/-- The interpolating bond is invariant under the action on its two ends
induced by the unitary virtual direct sum. In coefficient-matrix notation
this action is conjugation. Source: arXiv:1010.3732, Section II.F.2,
equations `eq:sym:omega-gamma` and `eq:1d-sym:jointsym`. -/
theorem bondInterpolationMatrix_conjugate_directSum
    {G : Type} [Group G] {D₀ D₁ : ℕ} {ω : ScalarCocycle G}
    (ρ₀ : ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : ProjectiveRepresentation (D := D₁) ω) (g : G) (γ : ℝ)
    (h₀ : (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ) :
    ((ρ₀.directSum ρ₁).X g : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ) *
      bondInterpolationMatrix D₀ D₁ γ *
      ((ρ₀.directSum ρ₁).X g : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ)ᴴ =
      bondInterpolationMatrix D₀ D₁ γ := by
  have hV := Matrix.mem_unitaryGroup_iff.mp (ρ₀.directSum_mem_unitaryGroup ρ₁ g h₀ h₁)
  rw [← (bondInterpolationMatrix_commute_directSum ρ₀ ρ₁ g γ).eq, Matrix.mul_assoc,
    ← Matrix.star_eq_conjTranspose, hV, Matrix.mul_one]

/-- Normalization preserves invariance of the interpolating bond. Source:
arXiv:1010.3732, Section II.F.2, equations `eq:sym:omega-gamma` and
`eq:1d-sym:jointsym`. -/
theorem normalizedBondInterpolationMatrix_conjugate_directSum
    {G : Type} [Group G] {D₀ D₁ : ℕ} {ω : ScalarCocycle G}
    (ρ₀ : ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : ProjectiveRepresentation (D := D₁) ω) (g : G) (γ : ℝ)
    (h₀ : (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ) :
    ((ρ₀.directSum ρ₁).X g : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ) *
      normalizedBondInterpolationMatrix D₀ D₁ γ *
      ((ρ₀.directSum ρ₁).X g : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ)ᴴ =
      normalizedBondInterpolationMatrix D₀ D₁ γ := by
  simp only [normalizedBondInterpolationMatrix, Matrix.mul_smul, Matrix.smul_mul,
    bondInterpolationMatrix_conjugate_directSum ρ₀ ρ₁ g γ h₀ h₁]

end MPSTensor
