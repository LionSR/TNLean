/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.BondProductParentHamiltonian
import TNLean.MPS.Symmetry.BondInterpolationSymmetry

/-!
# Symmetry of the independent-bond parent Hamiltonian

A linear action fixing the bond vector preserves each rank-one bond
projection. The tensor product action therefore preserves every parent
term separately. This is the independent-bond symmetry argument in
Schuch--Pérez-García--Cirac, arXiv:1010.3732, Section II.F.2.
-/

open scoped Matrix BigOperators Kronecker

namespace MPSTensor

variable {q N : ℕ}

/-- Matrix conjugation fixes the one-index bond vector under the corresponding
two-register action. The transpose reflects Mathlib's column-first `vec`
convention. Source: arXiv:1010.3732, Section II.F.2,
`eq:1d-sym:jointsym`. -/
theorem bondMatrixVector_fixed_of_conjugation {D : ℕ}
    (W X Y : Matrix (Fin D) (Fin D) ℂ) (hW : Y * W * X = W) :
    (Matrix.reindex finProdFinEquiv finProdFinEquiv (Y ⊗ₖ Xᵀ)) *ᵥ
      (fun x : Fin (D * D) => W (finProdFinEquiv.symm x).1
        (finProdFinEquiv.symm x).2) =
      (fun x : Fin (D * D) => W (finProdFinEquiv.symm x).1
        (finProdFinEquiv.symm x).2) := by
  classical
  let e := finProdFinEquiv (m := D) (n := D)
  have hvec : (fun x : Fin (D * D) => W (e.symm x).1 (e.symm x).2) =
      (Matrix.vec Wᵀ) ∘ e.symm := rfl
  have hK : (Y ⊗ₖ Xᵀ) *ᵥ Matrix.vec Wᵀ = Matrix.vec Wᵀ := by
    rw [Matrix.kronecker_mulVec_vec Xᵀ Wᵀ Y]
    congr 1
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] using
      congrArg Matrix.transpose hW
  rw [hvec, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
  dsimp [e]
  simpa only [Equiv.symm_symm, Function.comp_def,
    Equiv.symm_apply_apply] using
    congrArg (fun v : Fin D × Fin D → ℂ => v ∘ finProdFinEquiv.symm) hK

/-- The normalized interpolating bond is fixed by the unitary direct-sum
virtual action on its two ends. Source: arXiv:1010.3732, Section II.F.2,
equations `eq:sym:omega-gamma` and `eq:1d-sym:jointsym`. -/
theorem normalizedBondInterpolationVector_fixed_directSum
    {G : Type} [Group G] {D₀ D₁ : ℕ}
    {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω)
    (g : G) (γ : ℝ)
    (h₀ : (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ) :
    (Matrix.reindex finProdFinEquiv finProdFinEquiv
      (((ρ₀.directSum ρ₁).X g : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ)ᴴ
        ⊗ₖ ((ρ₀.directSum ρ₁).X g :
          Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ)ᵀ)) *ᵥ
      normalizedBondInterpolationVector D₀ D₁ γ =
      normalizedBondInterpolationVector D₀ D₁ γ := by
  let X : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ := (ρ₀.directSum ρ₁).X g
  let W := normalizedBondInterpolationMatrix D₀ D₁ γ
  have hunit : Xᴴ * X = 1 :=
    (Matrix.mem_unitaryGroup_iff').mp
      (ρ₀.directSum_mem_unitaryGroup ρ₁ g h₀ h₁)
  have hconj : X * W * Xᴴ = W :=
    normalizedBondInterpolationMatrix_conjugate_directSum ρ₀ ρ₁ g γ h₀ h₁
  have hreverse : Xᴴ * W * X = W := by
    calc
      Xᴴ * W * X = Xᴴ * (X * W * Xᴴ) * X := by rw [hconj]
      _ = Xᴴ * (X * W) := by
        simp only [Matrix.mul_assoc, hunit, Matrix.mul_one]
      _ = W := by rw [← Matrix.mul_assoc, hunit, Matrix.one_mul]
  exact bondMatrixVector_fixed_of_conjugation W X Xᴴ hreverse

/-- A matrix fixing a bond vector on both sides commutes with its
rank-one matrix. Source: arXiv:1010.3732, Section II.F.2. -/
theorem bondVectorProjection_commute_of_fixed
    (η : Fin q → ℂ) (S : Matrix (Fin q) (Fin q) ℂ)
    (hright : S *ᵥ η = η) (hleft : star η ᵥ* S = star η) :
    Commute S (bondVectorProjection η) := by
  classical
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_apply, bondVectorProjection,
    Matrix.vecMulVec_apply] at *
  calc
    (∑ k : Fin q, S i k * (η k * star (η j))) =
        (S *ᵥ η) i * star (η j) := by
          simp only [Matrix.mulVec, dotProduct, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ = η i * star (η j) := by rw [hright]
    _ = η i * (star η ᵥ* S) j := by rw [hleft]; rfl
    _ = ∑ k : Fin q, (η i * star (η k)) * S k j := by
      simp [Matrix.vecMul, dotProduct, Finset.mul_sum, mul_assoc]

/-- A unitary action fixing a bond vector also fixes its dual vector.
Source: arXiv:1010.3732, Section II.F.2. -/
theorem bondVector_dual_fixed_of_unitary
    (η : Fin q → ℂ) (S : Matrix (Fin q) (Fin q) ℂ)
    (hS : S ∈ Matrix.unitaryGroup (Fin q) ℂ)
    (hη : S *ᵥ η = η) : star η ᵥ* S = star η := by
  have hSS : Sᴴ * S = 1 := (Matrix.mem_unitaryGroup_iff').mp hS
  have hs := congrArg star hη
  rw [Matrix.star_mulVec] at hs
  calc
    star η ᵥ* S = (star η ᵥ* Sᴴ) ᵥ* S := by rw [hs]
    _ = star η ᵥ* (Sᴴ * S) := Matrix.vecMul_vecMul _ _ _
    _ = star η := by rw [hSS, Matrix.vecMul_one]

/-- A unitary bond action fixing the bond vector preserves the local
parent projection. Source: arXiv:1010.3732, Section II.F.2. -/
theorem bondPenalty_commute_of_unitary_fixed
    (η : Fin q → ℂ) (S : Matrix (Fin q) (Fin q) ℂ)
    (hS : S ∈ Matrix.unitaryGroup (Fin q) ℂ)
    (hη : S *ᵥ η = η) : Commute S (bondPenalty η) := by
  have hQ := bondVectorProjection_commute_of_fixed η S hη
    (bondVector_dual_fixed_of_unitary η S hS hη)
  apply (commute_iff_eq S (bondPenalty η)).2
  change S * (1 - bondVectorProjection η) =
    (1 - bondVectorProjection η) * S
  rw [mul_sub, sub_mul, mul_one, one_mul,
    (commute_iff_eq S (bondVectorProjection η)).1 hQ]

/-- The tensor product of a unitary bond action preserves every local
penalty separately. Source: arXiv:1010.3732, Section II.F.2. -/
theorem bondPenaltyAt_commute_sitewise_of_unitary_fixed
    (η : Fin q → ℂ) (S : Matrix (Fin q) (Fin q) ℂ)
    (hS : S ∈ Matrix.unitaryGroup (Fin q) ℂ)
    (hη : S *ᵥ η = η) (hN : 1 ≤ N) (i : Fin N) :
    Commute (MPOTensor.sitewiseMatrixFamily (fun _ : Fin N => S))
      (bondPenaltyAt η hN i) := by
  classical
  unfold bondPenaltyAt
  rw [← MPOTensor.sitewiseMatrixFamily_mulSingle hN i (bondPenalty η)]
  apply (commute_iff_eq _ _).2
  rw [MPOTensor.sitewiseMatrixFamily_mul, MPOTensor.sitewiseMatrixFamily_mul]
  congr 1
  funext j
  by_cases hji : j = i
  · subst j
    simpa using (commute_iff_eq S (bondPenalty η)).1
      (bondPenalty_commute_of_unitary_fixed η S hS hη)
  · simp [hji]

/-- The full commuting parent Hamiltonian is invariant under the
sitewise bond action. Source: arXiv:1010.3732, Section II.F.2. -/
theorem bondProductParentHamiltonian_commute_sitewise_of_unitary_fixed
    (η : Fin q → ℂ) (S : Matrix (Fin q) (Fin q) ℂ)
    (hS : S ∈ Matrix.unitaryGroup (Fin q) ℂ)
    (hη : S *ᵥ η = η) (hN : 1 ≤ N) :
    Commute (MPOTensor.sitewiseMatrixFamily (fun _ : Fin N => S))
      (bondProductParentHamiltonian η hN) := by
  classical
  unfold bondProductParentHamiltonian
  apply (commute_iff_eq _ _).2
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  exact (commute_iff_eq _ _).1
    (bondPenaltyAt_commute_sitewise_of_unitary_fixed η S hS hη hN i)

end MPSTensor
