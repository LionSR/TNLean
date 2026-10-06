/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointInterpolation
import TNLean.MPS.MPDO.BoundaryTransport

/-!
# The mixed endpoint MPO and its action maps

The diagonal physical sectors retain the endpoint MPOs. The two cross
sectors contract endpoint synthesis with endpoint analysis, summing over a
common multiplicity index. The enlarged action maps are supported on the
matching summands of the MPO and MPS bonds. In particular, the unmatched
summands of their tensor product are annihilated; no completeness identity
on the full acted bond is imposed.

Source: Garre-Rubio–Lootens–Molnár, arXiv:2203.12563v3,
`fusiontensors2`, `eq:orthoV`, and `Agammasym`, lines 458–490 and 1584–1665.
The exact action identity is proved in `MixedEndpointMPOAction`.
-/

open scoped Matrix BigOperators

namespace MPSTensor.MPOSymmetry

variable {D₀ D₁ χ₀ χ₁ m : ℕ}

/-- Flatten the two direct-sum registers of a physical letter. -/
def mixedEndpointPhysicalEquiv (D₀ D₁ : ℕ) :
    ((Fin D₀ ⊕ Fin D₁) × (Fin D₀ ⊕ Fin D₁)) ≃
      Fin ((D₀ + D₁) * (D₀ + D₁)) :=
  (Equiv.prodCongr finSumFinEquiv finSumFinEquiv).trans finProdFinEquiv

/-- Flatten the MPO register and the state register of the acted bond. -/
def mixedEndpointActedEquiv (χ₀ χ₁ D₀ D₁ : ℕ) :
    ((Fin χ₀ ⊕ Fin χ₁) × (Fin D₀ ⊕ Fin D₁)) ≃
      Fin ((χ₀ + χ₁) * (D₀ + D₁)) :=
  (Equiv.prodCongr finSumFinEquiv finSumFinEquiv).trans finProdFinEquiv

/-- Analysis in direct-sum coordinates, supported on matching bond sectors.
Source: GLM23, the direct sums in `Agammasym`. -/
def mixedEndpointAnalysis
    (V₀ : Matrix (Fin D₀) (Fin (χ₀ * D₀)) ℂ)
    (V₁ : Matrix (Fin D₁) (Fin (χ₁ * D₁)) ℂ) :
    Matrix (Fin D₀ ⊕ Fin D₁)
      ((Fin χ₀ ⊕ Fin χ₁) × (Fin D₀ ⊕ Fin D₁)) ℂ :=
  fun r (α, k) => match r, α, k with
  | .inl r, .inl α, .inl k => V₀ r (finProdFinEquiv (α, k))
  | .inr r, .inr α, .inr k => V₁ r (finProdFinEquiv (α, k))
  | _, _, _ => 0

/-- Synthesis in direct-sum coordinates. It vanishes on the unmatched acted
bond sectors, independently of the interpolation parameter.
Source: GLM23, the direct sums in `Agammasym`. -/
def mixedEndpointSynthesis
    (W₀ : Matrix (Fin (χ₀ * D₀)) (Fin D₀) ℂ)
    (W₁ : Matrix (Fin (χ₁ * D₁)) (Fin D₁) ℂ) :
    Matrix ((Fin χ₀ ⊕ Fin χ₁) × (Fin D₀ ⊕ Fin D₁))
      (Fin D₀ ⊕ Fin D₁) ℂ :=
  fun (α, k) r => match α, k, r with
  | .inl α, .inl k, .inl r => W₀ (finProdFinEquiv (α, k)) r
  | .inr α, .inr k, .inr r => W₁ (finProdFinEquiv (α, k)) r
  | _, _, _ => 0

/-- The mixed MPO in direct-sum coordinates. Each ordered physical sector
is preserved and uses only the corresponding ordered MPO-bond corner.
The cross sectors are the contractions of the endpoint action maps.
Source: GLM23, lines 1600–1631 immediately preceding `Agammasym`. -/
noncomputable def mixedEndpointMPOLetter
    (T₀ : MPOTensor (D₀ * D₀) χ₀) (T₁ : MPOTensor (D₁ * D₁) χ₁)
    (V₀ : Fin m → Matrix (Fin D₀) (Fin (χ₀ * D₀)) ℂ)
    (V₁ : Fin m → Matrix (Fin D₁) (Fin (χ₁ * D₁)) ℂ)
    (W₀ : Fin m → Matrix (Fin (χ₀ * D₀)) (Fin D₀) ℂ)
    (W₁ : Fin m → Matrix (Fin (χ₁ * D₁)) (Fin D₁) ℂ)
    (r s k l : Fin D₀ ⊕ Fin D₁) :
    Matrix (Fin χ₀ ⊕ Fin χ₁) (Fin χ₀ ⊕ Fin χ₁) ℂ :=
  fun α β => match r, s, k, l, α, β with
  | .inl r, .inl s, .inl k, .inl l, .inl α, .inl β =>
      T₀ (finProdFinEquiv (r, s)) (finProdFinEquiv (k, l)) α β
  | .inl r, .inr s, .inl k, .inr l, .inl α, .inr β =>
      ∑ μ, W₀ μ (finProdFinEquiv (α, k)) r * V₁ μ s (finProdFinEquiv (β, l))
  | .inr r, .inl s, .inr k, .inl l, .inr α, .inl β =>
      ∑ μ, W₁ μ (finProdFinEquiv (α, k)) r * V₀ μ s (finProdFinEquiv (β, l))
  | .inr r, .inr s, .inr k, .inr l, .inr α, .inr β =>
      T₁ (finProdFinEquiv (r, s)) (finProdFinEquiv (k, l)) α β
  | _, _, _, _, _, _ => 0

/-- The explicit mixed MPO in the physical and virtual coordinates used by
`mixedEndpointInterpolation` and `MPOTensor.actTensor`. It is independent
of the real path parameter. Source: GLM23, lines 1600–1631. -/
noncomputable def mixedEndpointMPO
    (T₀ : MPOTensor (D₀ * D₀) χ₀) (T₁ : MPOTensor (D₁ * D₁) χ₁)
    (V₀ : Fin m → Matrix (Fin D₀) (Fin (χ₀ * D₀)) ℂ)
    (V₁ : Fin m → Matrix (Fin D₁) (Fin (χ₁ * D₁)) ℂ)
    (W₀ : Fin m → Matrix (Fin (χ₀ * D₀)) (Fin D₀) ℂ)
    (W₁ : Fin m → Matrix (Fin (χ₁ * D₁)) (Fin D₁) ℂ) :
    MPOTensor ((D₀ + D₁) * (D₀ + D₁)) (χ₀ + χ₁) :=
  fun i j =>
    (mixedEndpointMPOLetter T₀ T₁ V₀ V₁ W₀ W₁
      ((mixedEndpointPhysicalEquiv D₀ D₁).symm i).1
      ((mixedEndpointPhysicalEquiv D₀ D₁).symm i).2
      ((mixedEndpointPhysicalEquiv D₀ D₁).symm j).1
      ((mixedEndpointPhysicalEquiv D₀ D₁).symm j).2).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm

/-- The enlarged analysis map in the standard finite coordinates. -/
def mixedEndpointMPOAnalysis
    (V₀ : Matrix (Fin D₀) (Fin (χ₀ * D₀)) ℂ)
    (V₁ : Matrix (Fin D₁) (Fin (χ₁ * D₁)) ℂ) :
    Matrix (Fin (D₀ + D₁)) (Fin ((χ₀ + χ₁) * (D₀ + D₁))) ℂ :=
  (mixedEndpointAnalysis V₀ V₁).submatrix finSumFinEquiv.symm
    (mixedEndpointActedEquiv χ₀ χ₁ D₀ D₁).symm

/-- The enlarged synthesis map in the standard finite coordinates. -/
def mixedEndpointMPOSynthesis
    (W₀ : Matrix (Fin (χ₀ * D₀)) (Fin D₀) ℂ)
    (W₁ : Matrix (Fin (χ₁ * D₁)) (Fin D₁) ℂ) :
    Matrix (Fin ((χ₀ + χ₁) * (D₀ + D₁))) (Fin (D₀ + D₁)) ℂ :=
  (mixedEndpointSynthesis W₀ W₁).submatrix
    (mixedEndpointActedEquiv χ₀ χ₁ D₀ D₁).symm finSumFinEquiv.symm

/-- The mixed analysis-synthesis product is the direct sum of the endpoint
products. The two unmatched acted sectors contribute zero. -/
theorem mixedEndpointAnalysis_mul_synthesis
    (V₀ : Matrix (Fin D₀) (Fin (χ₀ * D₀)) ℂ)
    (V₁ : Matrix (Fin D₁) (Fin (χ₁ * D₁)) ℂ)
    (W₀ : Matrix (Fin (χ₀ * D₀)) (Fin D₀) ℂ)
    (W₁ : Matrix (Fin (χ₁ * D₁)) (Fin D₁) ℂ) :
    mixedEndpointAnalysis V₀ V₁ * mixedEndpointSynthesis W₀ W₁ =
      Matrix.fromBlocks (V₀ * W₀) 0 0 (V₁ * W₁) := by
  classical
  ext i j
  cases i <;> cases j <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.mul_apply,
      Fintype.sum_prod_type, Fintype.sum_sum_type, mixedEndpointAnalysis,
      mixedEndpointSynthesis, Matrix.zero_apply, zero_mul, mul_zero,
      Finset.sum_const_zero, zero_add, add_zero]
  · rename_i i j
    simpa only [Fintype.sum_prod_type] using
      (finProdFinEquiv.sum_comp (fun k => V₀ i k * W₀ k j))
  · rename_i i j
    simpa only [Fintype.sum_prod_type] using
      (finProdFinEquiv.sum_comp (fun k => V₁ i k * W₁ k j))

/-- A physical direct-sum pair selects the corresponding unweighted
mixed letter in standard bond coordinates. -/
@[simp] theorem mixedEndpointBase_physicalEquiv
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (r s : Fin D₀ ⊕ Fin D₁) :
    mixedEndpointBase A₀ A₁ (mixedEndpointPhysicalEquiv D₀ D₁ (r, s)) =
      (mixedEndpointLetter A₀ A₁ r s).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := by
  simp [mixedEndpointBase, mixedEndpointPhysicalEquiv, Matrix.reindex_apply]

/-- Evaluation of the constructed MPO at direct-sum physical pairs. -/
@[simp] theorem mixedEndpointMPO_physicalEquiv
    (T₀ : MPOTensor (D₀ * D₀) χ₀) (T₁ : MPOTensor (D₁ * D₁) χ₁)
    (V₀ : Fin m → Matrix (Fin D₀) (Fin (χ₀ * D₀)) ℂ)
    (V₁ : Fin m → Matrix (Fin D₁) (Fin (χ₁ * D₁)) ℂ)
    (W₀ : Fin m → Matrix (Fin (χ₀ * D₀)) (Fin D₀) ℂ)
    (W₁ : Fin m → Matrix (Fin (χ₁ * D₁)) (Fin D₁) ℂ)
    (r s k l : Fin D₀ ⊕ Fin D₁) :
    mixedEndpointMPO T₀ T₁ V₀ V₁ W₀ W₁
      (mixedEndpointPhysicalEquiv D₀ D₁ (r, s))
      (mixedEndpointPhysicalEquiv D₀ D₁ (k, l)) =
      (mixedEndpointMPOLetter T₀ T₁ V₀ V₁ W₀ W₁ r s k l).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := by
  simp [mixedEndpointMPO]

/-- Standard-coordinate mixed maps inherit biorthogonality from the two
endpoint maps. No identity on the ambient acted space is used. -/
theorem mixedEndpointMPOAnalysis_mul_synthesis
    (V₀ : Matrix (Fin D₀) (Fin (χ₀ * D₀)) ℂ)
    (V₁ : Matrix (Fin D₁) (Fin (χ₁ * D₁)) ℂ)
    (W₀ : Matrix (Fin (χ₀ * D₀)) (Fin D₀) ℂ)
    (W₁ : Matrix (Fin (χ₁ * D₁)) (Fin D₁) ℂ) :
    mixedEndpointMPOAnalysis V₀ V₁ * mixedEndpointMPOSynthesis W₀ W₁ =
      (Matrix.fromBlocks (V₀ * W₀) 0 0 (V₁ * W₁)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := by
  rw [mixedEndpointMPOAnalysis, mixedEndpointMPOSynthesis,
    Matrix.submatrix_mul_equiv, mixedEndpointAnalysis_mul_synthesis]

end MPSTensor.MPOSymmetry
