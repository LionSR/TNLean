/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointMPO

/-!
# Mixed endpoint fusion maps

Fusion analysis and synthesis have three independent bond dimensions at each
endpoint. They are supported on the two matching sectors of the product of
the incoming direct sums. Their analysis-synthesis product is the direct sum
of the endpoint products, including when the outgoing dimensions differ.

Source: Garre-Rubio–Lootens–Molnár, arXiv:2203.12563v3,
`fusiontensors`, `eq:orthoW`, and the mixed fusion tensors in
`REsubmission.tex`, lines 1667–1685.
-/

open scoped Matrix BigOperators

namespace MPSTensor.MPOSymmetry

variable {χa₀ χa₁ χb₀ χb₁ χc₀ χc₁ χd₀ χd₁ : ℕ}

/-- Fusion analysis in direct-sum coordinates, with independent incoming
and outgoing bonds. Source: GLM23, mixed fusion tensors, lines 1667–1685. -/
def mixedEndpointFusionAnalysis
    (V₀ : Matrix (Fin χc₀) (Fin (χa₀ * χb₀)) ℂ)
    (V₁ : Matrix (Fin χc₁) (Fin (χa₁ * χb₁)) ℂ) :
    Matrix (Fin χc₀ ⊕ Fin χc₁)
      ((Fin χa₀ ⊕ Fin χa₁) × (Fin χb₀ ⊕ Fin χb₁)) ℂ :=
  fun r (α, β) => match r, α, β with
  | .inl r, .inl α, .inl β => V₀ r (finProdFinEquiv (α, β))
  | .inr r, .inr α, .inr β => V₁ r (finProdFinEquiv (α, β))
  | _, _, _ => 0

/-- Fusion synthesis in direct-sum coordinates. The unmatched incoming
bond sectors vanish. Source: GLM23, mixed fusion tensors, lines 1667–1685. -/
def mixedEndpointFusionSynthesis
    (W₀ : Matrix (Fin (χa₀ * χb₀)) (Fin χc₀) ℂ)
    (W₁ : Matrix (Fin (χa₁ * χb₁)) (Fin χc₁) ℂ) :
    Matrix ((Fin χa₀ ⊕ Fin χa₁) × (Fin χb₀ ⊕ Fin χb₁))
      (Fin χc₀ ⊕ Fin χc₁) ℂ :=
  fun (α, β) r => match α, β, r with
  | .inl α, .inl β, .inl r => W₀ (finProdFinEquiv (α, β)) r
  | .inr α, .inr β, .inr r => W₁ (finProdFinEquiv (α, β)) r
  | _, _, _ => 0

/-- The mixed fusion analysis map in standard finite coordinates.
Source: GLM23, mixed fusion tensors, lines 1667–1685. -/
def mixedEndpointMPOFusionAnalysis
    (V₀ : Matrix (Fin χc₀) (Fin (χa₀ * χb₀)) ℂ)
    (V₁ : Matrix (Fin χc₁) (Fin (χa₁ * χb₁)) ℂ) :
    Matrix (Fin (χc₀ + χc₁)) (Fin ((χa₀ + χa₁) * (χb₀ + χb₁))) ℂ :=
  (mixedEndpointFusionAnalysis V₀ V₁).submatrix finSumFinEquiv.symm
    (mixedEndpointActedEquiv χa₀ χa₁ χb₀ χb₁).symm

/-- The mixed fusion synthesis map in standard finite coordinates.
Source: GLM23, mixed fusion tensors, lines 1667–1685. -/
def mixedEndpointMPOFusionSynthesis
    (W₀ : Matrix (Fin (χa₀ * χb₀)) (Fin χc₀) ℂ)
    (W₁ : Matrix (Fin (χa₁ * χb₁)) (Fin χc₁) ℂ) :
    Matrix (Fin ((χa₀ + χa₁) * (χb₀ + χb₁))) (Fin (χc₀ + χc₁)) ℂ :=
  (mixedEndpointFusionSynthesis W₀ W₁).submatrix
    (mixedEndpointActedEquiv χa₀ χa₁ χb₀ χb₁).symm finSumFinEquiv.symm

/-- The rectangular mixed fusion product is the direct sum of the endpoint
products. In particular, different outgoing fusion channels remain
orthogonal whenever the endpoint maps are orthogonal.
Source: GLM23, `eq:orthoW` and mixed fusion tensors, lines 1667–1685. -/
theorem mixedEndpointFusionAnalysis_mul_synthesis
    (V₀ : Matrix (Fin χc₀) (Fin (χa₀ * χb₀)) ℂ)
    (V₁ : Matrix (Fin χc₁) (Fin (χa₁ * χb₁)) ℂ)
    (W₀ : Matrix (Fin (χa₀ * χb₀)) (Fin χd₀) ℂ)
    (W₁ : Matrix (Fin (χa₁ * χb₁)) (Fin χd₁) ℂ) :
    mixedEndpointFusionAnalysis V₀ V₁ * mixedEndpointFusionSynthesis W₀ W₁ =
      Matrix.fromBlocks (V₀ * W₀) 0 0 (V₁ * W₁) := by
  classical
  ext i j
  cases i <;> cases j <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.mul_apply,
      Fintype.sum_prod_type, Fintype.sum_sum_type, mixedEndpointFusionAnalysis,
      mixedEndpointFusionSynthesis, Matrix.zero_apply, zero_mul, mul_zero,
      Finset.sum_const_zero, zero_add, add_zero]
  · rename_i i j
    simpa only [Fintype.sum_prod_type] using
      (finProdFinEquiv.sum_comp (fun k => V₀ i k * W₀ k j))
  · rename_i i j
    simpa only [Fintype.sum_prod_type] using
      (finProdFinEquiv.sum_comp (fun k => V₁ i k * W₁ k j))

/-- Standard-coordinate mixed fusion maps inherit every rectangular
analysis-synthesis identity of the two endpoint maps.
Source: GLM23, `eq:orthoW` and mixed fusion tensors, lines 1667–1685. -/
theorem mixedEndpointMPOFusionAnalysis_mul_synthesis
    (V₀ : Matrix (Fin χc₀) (Fin (χa₀ * χb₀)) ℂ)
    (V₁ : Matrix (Fin χc₁) (Fin (χa₁ * χb₁)) ℂ)
    (W₀ : Matrix (Fin (χa₀ * χb₀)) (Fin χd₀) ℂ)
    (W₁ : Matrix (Fin (χa₁ * χb₁)) (Fin χd₁) ℂ) :
    mixedEndpointMPOFusionAnalysis V₀ V₁ * mixedEndpointMPOFusionSynthesis W₀ W₁ =
      (Matrix.fromBlocks (V₀ * W₀) 0 0 (V₁ * W₁)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := by
  rw [mixedEndpointMPOFusionAnalysis, mixedEndpointMPOFusionSynthesis,
    Matrix.submatrix_mul_equiv, mixedEndpointFusionAnalysis_mul_synthesis]

/-- Conjugating a rectangular direct-sum matrix by mixed fusion maps retains
its four corners on the matching product sectors and annihilates every
unmatched sector. Applied to a mixed MPO letter, the off-diagonal corners
are its endpoint action contractions.
Source: GLM23, mixed fusion tensors, lines 1667–1685. -/
theorem mixedEndpointFusion_sandwich_apply
    (W₀ : Matrix (Fin (χa₀ * χb₀)) (Fin χc₀) ℂ)
    (W₁ : Matrix (Fin (χa₁ * χb₁)) (Fin χc₁) ℂ)
    (M : Matrix (Fin χc₀ ⊕ Fin χc₁) (Fin χd₀ ⊕ Fin χd₁) ℂ)
    (V₀ : Matrix (Fin χd₀) (Fin (χa₀ * χb₀)) ℂ)
    (V₁ : Matrix (Fin χd₁) (Fin (χa₁ * χb₁)) ℂ)
    (p q : (Fin χa₀ ⊕ Fin χa₁) × (Fin χb₀ ⊕ Fin χb₁)) :
    (mixedEndpointFusionSynthesis W₀ W₁ * M * mixedEndpointFusionAnalysis V₀ V₁)
        p q =
      match p.1, p.2, q.1, q.2 with
      | .inl α, .inl β, .inl γ, .inl δ =>
          (W₀ * M.submatrix Sum.inl Sum.inl * V₀)
            (finProdFinEquiv (α, β)) (finProdFinEquiv (γ, δ))
      | .inl α, .inl β, .inr γ, .inr δ =>
          (W₀ * M.submatrix Sum.inl Sum.inr * V₁)
            (finProdFinEquiv (α, β)) (finProdFinEquiv (γ, δ))
      | .inr α, .inr β, .inl γ, .inl δ =>
          (W₁ * M.submatrix Sum.inr Sum.inl * V₀)
            (finProdFinEquiv (α, β)) (finProdFinEquiv (γ, δ))
      | .inr α, .inr β, .inr γ, .inr δ =>
          (W₁ * M.submatrix Sum.inr Sum.inr * V₁)
            (finProdFinEquiv (α, β)) (finProdFinEquiv (γ, δ))
      | _, _, _, _ => 0 := by
  classical
  rcases p with ⟨α, β⟩
  rcases q with ⟨γ, δ⟩
  cases α <;> cases β <;> cases γ <;> cases δ <;>
    simp only [Matrix.mul_apply, Fintype.sum_sum_type,
      mixedEndpointFusionSynthesis, mixedEndpointFusionAnalysis,
      Matrix.submatrix_apply, zero_mul, mul_zero, Finset.sum_const_zero,
      zero_add, add_zero]

/-- Standard finite-coordinate fusion sandwiches are the relabelled
sandwiches on direct sums. Source: GLM23, mixed fusion tensors,
lines 1667–1685. -/
theorem mixedEndpointMPOFusion_sandwich
    (W₀ : Matrix (Fin (χa₀ * χb₀)) (Fin χc₀) ℂ)
    (W₁ : Matrix (Fin (χa₁ * χb₁)) (Fin χc₁) ℂ)
    (M : Matrix (Fin χc₀ ⊕ Fin χc₁) (Fin χd₀ ⊕ Fin χd₁) ℂ)
    (V₀ : Matrix (Fin χd₀) (Fin (χa₀ * χb₀)) ℂ)
    (V₁ : Matrix (Fin χd₁) (Fin (χa₁ * χb₁)) ℂ) :
    mixedEndpointMPOFusionSynthesis W₀ W₁ *
        M.submatrix finSumFinEquiv.symm finSumFinEquiv.symm *
          mixedEndpointMPOFusionAnalysis V₀ V₁ =
      (mixedEndpointFusionSynthesis W₀ W₁ * M * mixedEndpointFusionAnalysis V₀ V₁).submatrix
        (mixedEndpointActedEquiv χa₀ χa₁ χb₀ χb₁).symm
        (mixedEndpointActedEquiv χa₀ χa₁ χb₀ χb₁).symm := by
  rw [mixedEndpointMPOFusionSynthesis, mixedEndpointMPOFusionAnalysis,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]

end MPSTensor.MPOSymmetry
