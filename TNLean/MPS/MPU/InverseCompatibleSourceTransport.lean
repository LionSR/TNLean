/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.InverseCompatibleSourceFactors

/-!
# Unitary transport of the inverse-compatible source factors

Let $S_0$ be the chosen source factors and $S$ the inverse-compatible source
factors at the same canonical weight. Transport the columns of the proved
unitary comparison $K:r\times\ell$ along the explicit rank equivalence
$e:\operatorname{Fin}\ell\simeq\operatorname{Fin}r$ to obtain a square matrix
$C$. Then $C$ is unitary and $S.X_1=S_0.X_1C$, $S.Y_1=C^\dagger S_0.Y_1$.
Consequently $S.X_1S.X_1^\dagger=S_0.X_1S_0.X_1^\dagger$ and
$S.Y_1^\dagger S.Y_1=S_0.Y_1^\dagger S_0.Y_1$.

Source: arXiv:2502.20257, the comparison at lines 5432–5443, justified as
unitary at lines 5444–5487. This is coordinate transport after that unitarity
proof, not an assumption that the inverse comparison is an adjoint. No
transport formula is asserted for the chosen source right inverse $Z_1$.
-/

open scoped ComplexOrder Matrix

namespace MPOTensor

variable {d D : ℕ} (U : MPOTensor d D) (T : Matrix.unitaryGroup (Fin D) ℂ)
  (hU : IsMPUCanonicalFormII U) (hsimple : IsMPUSimple U)
  (hT : ∀ i j, physicalAdjointTensor U i j =
    (T : Matrix (Fin D) (Fin D) ℂ)ᴴ * U i j * T)
  (σ : ℂ) (hσ : (T : Matrix (Fin D) (Fin D) ℂ) *
    (T : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) = σ • 1)

/-- The source records are related by the actual comparison after its column
rank index is transported. Its unitarity is inherited from the proved
rectangular comparison, and the right-factor formula uses the proved
identity $J=K^\dagger$.
Source: arXiv:2502.20257, lines 5432–5443 and 5444–5487. -/
theorem inverseCompatibleSourceFactors_unitary_transport :
    let S₀ := sourceFactors U hU.ρ hU.ρ_posDef
    let S := inverseCompatibleSourceFactors U T hU hsimple hT σ hσ
    let e := inverseCompatibleRankEquiv U T hT
    let K := inverseCompatibleComparisonK U T hU.ρ hU.ρ_posDef
    let C := Matrix.reindex (Equiv.refl _) e K
    C.IsUnitaryBetween ∧ S.X₁ = S₀.X₁ * C ∧ S.Y₁ = Cᴴ * S₀.Y₁ := by
  let e := inverseCompatibleRankEquiv U T hT
  let K := inverseCompatibleComparisonK U T hU.ρ hU.ρ_posDef
  have hK := inverseCompatibleComparisonK_isUnitaryBetween U T hU hsimple hT σ hσ
  have hX := (inverseCompatibleComparison U T hT hU.ρ hU.ρ_posDef).2.1
  have hY := (inverseCompatibleComparison U T hT hU.ρ hU.ρ_posDef).2.2.2.2.2.1
  rw [inverseCompatibleComparisonJ_eq_conjTranspose U T hU hsimple hT σ hσ] at hY
  refine ⟨hK.reindex _ (Equiv.refl _) e, ?_, ?_⟩
  · rw [inverseCompatibleSourceFactors_X₁, hX]
    change Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) e
        (sourceX₁ U hU.ρ hU.ρ_posDef * K) =
      Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) (Equiv.refl _)
        (sourceX₁ U hU.ρ hU.ρ_posDef) *
      Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) e K
    rw [Matrix.reindexLinearEquiv_mul]
  · rw [inverseCompatibleSourceFactors_Y₁, hY, Matrix.conjTranspose_reindex]
    change Matrix.reindexLinearEquiv ℂ ℂ e (Equiv.refl _)
        (Kᴴ * sourceY₁ U hU.ρ hU.ρ_posDef) =
      Matrix.reindexLinearEquiv ℂ ℂ e (Equiv.refl _) Kᴴ *
      Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) (Equiv.refl _)
        (sourceY₁ U hU.ρ hU.ρ_posDef)
    rw [Matrix.reindexLinearEquiv_mul]

/-- The two first-factor Gram matrices on the external source-cut spaces
are unchanged under the proved unitary transport. This does not compare
chosen right inverses or assert further pleasant properties.
Source: arXiv:2502.20257, the normalization transport at lines 5486–5487. -/
theorem inverseCompatibleSourceFactors_gram_eq :
    let S₀ := sourceFactors U hU.ρ hU.ρ_posDef
    let S := inverseCompatibleSourceFactors U T hU hsimple hT σ hσ
    S.X₁ * S.X₁ᴴ = S₀.X₁ * S₀.X₁ᴴ ∧
      S.Y₁ᴴ * S.Y₁ = S₀.Y₁ᴴ * S₀.Y₁ := by
  obtain ⟨hC, hX, hY⟩ :=
    inverseCompatibleSourceFactors_unitary_transport U T hU hsimple hT σ hσ
  let C := Matrix.reindex (Equiv.refl _) (inverseCompatibleRankEquiv U T hT)
    (inverseCompatibleComparisonK U T hU.ρ hU.ρ_posDef)
  have hCC : C * Cᴴ = 1 := hC.2
  constructor
  · rw [hX, Matrix.conjTranspose_mul]
    calc
      _ = (sourceFactors U hU.ρ hU.ρ_posDef).X₁ * (C * Cᴴ) *
          (sourceFactors U hU.ρ hU.ρ_posDef).X₁ᴴ := by simp only [C, Matrix.mul_assoc]
      _ = _ := by rw [hCC, Matrix.mul_one]
  · rw [hY, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      _ = (sourceFactors U hU.ρ hU.ρ_posDef).Y₁ᴴ * (C * Cᴴ) *
          (sourceFactors U hU.ρ hU.ρ_posDef).Y₁ := by simp only [C, Matrix.mul_assoc]
      _ = _ := by rw [hCC, Matrix.mul_one]

end MPOTensor
