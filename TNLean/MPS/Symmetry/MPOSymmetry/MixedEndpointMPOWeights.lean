/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointMPO

/-!
# Bond-weight transport through the mixed endpoint action maps

Right multiplication of a state tensor by a bond matrix lifts to right
multiplication on the acted bond. The mixed analysis map intertwines the
lifted interpolation weight with the original weight, since its nonzero
entries have matching endpoint sectors. These statements hold even when
one or both endpoint weights vanish.

Source: Garre-Rubio–Lootens–Molnár, arXiv:2203.12563v3,
`defAgamma` and `Agammasym`, lines 1584–1665.
-/

open scoped Matrix BigOperators Kronecker

namespace MPOTensor

variable {d χ D : ℕ}

/-- Right multiplication on the state bond lifts through the MPO action
as the tensor product with the identity on the MPO bond.
Source: GLM23, `fusiontensors2` and the weighted tensors in `defAgamma`. -/
theorem actTensor_right_mul (T : MPOTensor d χ) (A : MPSTensor d D)
    (H : Matrix (Fin D) (Fin D) ℂ) (i : Fin d) :
    actTensor T (fun j => A j * H) i =
      actTensor T A i * productBoundary (1 : Matrix (Fin χ) (Fin χ) ℂ) H := by
  simp only [actTensor, productBoundary, Matrix.submatrix_mul_equiv,
    Finset.sum_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one]

/-- A diagonal state-bond weight remains diagonal on the acted bond, with
its value determined by the state-bond register. -/
theorem productBoundary_one_diagonal (w : Fin D → ℂ) :
    productBoundary (1 : Matrix (Fin χ) (Fin χ) ℂ) (Matrix.diagonal w) =
      Matrix.diagonal (fun p : Fin (χ * D) => w (finProdFinEquiv.symm p).2) := by
  unfold productBoundary
  rw [← Matrix.diagonal_one, Matrix.diagonal_kronecker_diagonal,
    Matrix.submatrix_diagonal_equiv]
  simp only [one_mul, Function.comp_def]

end MPOTensor

namespace MPSTensor.MPOSymmetry

variable {D₀ D₁ χ₀ χ₁ : ℕ}

/-- The mixed analysis map intertwines the lifted bond weight with the
bond weight of the interpolated tensor. Only matching endpoint sectors
contribute, so no restriction on the interpolation parameter is needed.
Source: GLM23, `defAgamma` and `Agammasym`, lines 1584–1665. -/
theorem mixedEndpointMPOAnalysis_mul_weight
    (V₀ : Matrix (Fin D₀) (Fin (χ₀ * D₀)) ℂ)
    (V₁ : Matrix (Fin D₁) (Fin (χ₁ * D₁)) ℂ) (γ : ℝ) :
    mixedEndpointMPOAnalysis V₀ V₁ *
        MPOTensor.productBoundary (1 : Matrix (Fin (χ₀ + χ₁)) (Fin (χ₀ + χ₁)) ℂ)
          (bondInterpolationMatrix D₀ D₁ γ) =
      bondInterpolationMatrix D₀ D₁ γ * mixedEndpointMPOAnalysis V₀ V₁ := by
  classical
  ext i j
  simp only [bondInterpolationMatrix, MPOTensor.productBoundary_one_diagonal,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  obtain ⟨r, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨⟨α, k⟩, rfl⟩ := (mixedEndpointActedEquiv χ₀ χ₁ D₀ D₁).surjective j
  simp only [mixedEndpointMPOAnalysis, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  simp only [mixedEndpointActedEquiv, Equiv.trans_apply, Equiv.symm_apply_apply,
    Equiv.prodCongr_apply]
  cases r <;> cases α <;> cases k <;>
    simp [mixedEndpointAnalysis, bondInterpolationWeight, mul_comm]

end MPSTensor.MPOSymmetry
