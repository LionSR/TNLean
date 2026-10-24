/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Entropy.ConditionalSkewPhase

/-!
# Schmidt-diagonal operators act equally on both sides of a cut

Let `Ψ = ∑ α, a α ψ_L(α) ⊗ ψ_R(α)` be a Schmidt decomposition with orthonormal families
`ψ_L` and `ψ_R`. For any function `O`, the operators `B_L = ∑ α, O α |ψ_L(α)⟩⟨ψ_L(α)| ⊗ 1`
and `B_R = 1 ⊗ ∑ α, O α |ψ_R(α)⟩⟨ψ_R(α)|` satisfy `B_L Ψ = B_R Ψ`. Hastings uses this identity
in the proof of Lemma 3.

## Main results

* `TNLean.MPS.AreaLaw.Hastings.kronecker_one_mulVec_schmidt_eq_one_kronecker_mulVec`:
  `B_L Ψ = B_R Ψ`.

## References

* M. B. Hastings, *An area law for one-dimensional quantum systems*, arXiv:0705.2024v4,
  `References/0705.2024/law16.tex`, Lemma 3, lines 627–692; the identity is used at line 672.
-/

open Matrix
open scoped Kronecker

namespace TNLean.MPS.AreaLaw.Hastings

variable {l r κ : Type*} [Fintype l] [Fintype r] [Fintype κ]

/-- An operator diagonal in an orthonormal family `ψ`, with eigenvalue `O β` on `ψ β`,
maps `ψ α` to `O α • ψ α`. -/
theorem sum_smul_vecMulVec_mulVec_of_orthonormal [DecidableEq κ] {n : Type*} [Fintype n]
    (O : κ → ℂ) (ψ : κ → n → ℂ)
    (hψ : ∀ α β, star (ψ α) ⬝ᵥ ψ β = if α = β then 1 else 0) (α : κ) :
    (∑ β, O β • vecMulVec (ψ β) (star (ψ β))) *ᵥ ψ α = O α • ψ α := by
  simp [sum_mulVec, smul_mulVec, vecMulVec_mulVec, hψ]

/-- Hastings, arXiv:0705.2024v4, Lemma 3, `law16.tex` lines 627–692, the identity used at
line 672: for a Schmidt
decomposition `Ψ = ∑ α, a α ψL α ⊗ ψR α` with orthonormal families `ψL` and `ψR`,
the operator `∑ α, O α |ψL α⟩⟨ψL α| ⊗ 1` and the operator
`1 ⊗ ∑ α, O α |ψR α⟩⟨ψR α|` agree on `Ψ`, both giving `∑ α, a α O α ψL α ⊗ ψR α`. -/
theorem kronecker_one_mulVec_schmidt_eq_one_kronecker_mulVec
    [DecidableEq l] [DecidableEq r] [DecidableEq κ]
    (a O : κ → ℂ) (ψL : κ → l → ℂ) (ψR : κ → r → ℂ)
    (hL : ∀ α β, star (ψL α) ⬝ᵥ ψL β = if α = β then 1 else 0)
    (hR : ∀ α β, star (ψR α) ⬝ᵥ ψR β = if α = β then 1 else 0) :
    ((∑ α, O α • vecMulVec (ψL α) (star (ψL α))) ⊗ₖ (1 : Matrix r r ℂ)) *ᵥ
        (fun p => ∑ α, a α * (ψL α p.1 * ψR α p.2)) =
      ((1 : Matrix l l ℂ) ⊗ₖ (∑ α, O α • vecMulVec (ψR α) (star (ψR α)))) *ᵥ
        (fun p => ∑ α, a α * (ψL α p.1 * ψR α p.2)) := by
  ext ⟨i, k⟩
  rw [Entropy.ConditionalSkew.kronecker_one_mulVec_apply,
    Entropy.ConditionalSkew.one_kronecker_mulVec_apply]
  have hC : Entropy.ConditionalSkew.coeffMat (fun p => ∑ α, a α * (ψL α p.1 * ψR α p.2)) =
      ∑ α, a α • vecMulVec (ψL α) (ψR α) := by
    ext x y
    simp [Entropy.ConditionalSkew.coeffMat, vecMulVec_apply, Matrix.sum_apply]
  rw [hC, Matrix.mul_sum, Matrix.sum_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec, vecMulVec_mul, vecMul_transpose,
    sum_smul_vecMulVec_mulVec_of_orthonormal O ψL hL,
    sum_smul_vecMulVec_mulVec_of_orthonormal O ψR hR]
  simp only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun α _ => by ring

end TNLean.MPS.AreaLaw.Hastings
