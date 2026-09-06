/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinSumPermutation
import TNLean.MPS.MPU.InverseCompatibleCutComparison
import TNLean.MPS.MPU.SourceUV

/-!
# The literal inverse-compatible gate identity

For a tensor $U$, a positive-definite weight $\rho$, and a unitary virtual gauge $T$
relating $U$ to its physical adjoint, let $K$ be the weighted first-cut comparison.
If $T\overline T=\sigma I$, the actual source gates obey
$u=\sigma(K^\dagger\otimes K)v^\dagger$.

This follows the contraction in arXiv:2502.20257, `main.tex` lines 5444–5487:
adjoint the first comparison to express $Y_2$, substitute the comparison for
$\tilde Y_1$, and contract $\overline T T$. The diagram's $\tilde Y_1$ is used,
retaining the tilde omitted in the preceding printed equation. The weight remains
in the chosen source factors and $K$. No identification of the inverse comparison
with $K^\dagger$, gate unitarity, simplicity, or unit modulus of $\sigma$ is assumed.
The row orders of $u$ and $v^\dagger$ are respectively $(\ell,r)$ and $(r,\ell)$;
there is no additional swap.
-/

open scoped ComplexOrder Matrix Kronecker

namespace MPOTensor

variable {d D : ℕ} (U : MPOTensor d D) (T : Matrix.unitaryGroup (Fin D) ℂ)

/-- Adjointing the first comparison gives the second source factor in terms
of the weighted first source factor. This does not use $J=K^\dagger$.
Source: arXiv:2502.20257, lines 5440–5443, with the maintained product-index order. -/
theorem sourceY₂_eq_inverseCompatibleComparisonK_adjoint
    (hT : ∀ i j, physicalAdjointTensor U i j =
      (T : Matrix (Fin D) (Fin D) ℂ)ᴴ * U i j * T)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    sourceY₂ U = (inverseCompatibleComparisonK U T ρ hρ)ᴴ *
      (sourceX₁ U ρ hρ)ᴴ * inverseCompatibleLeftGauge (d := d) T := by
  have hX := (inverseCompatibleComparison U T hT ρ hρ).2.1
  have hA : (inverseCompatibleLeftGauge (d := d) T)ᴴ *
      inverseCompatibleLeftGauge (d := d) T = 1 :=
    (Matrix.kronecker_mem_unitary (show (1 : Matrix (Fin d) (Fin d) ℂ) ∈
      unitary (Matrix (Fin d) (Fin d) ℂ) from one_mem _)
      (Matrix.map_star_mem_unitaryGroup_iff.mpr T.property)).1
  have h := congrArg (fun M ↦ Mᴴ * inverseCompatibleLeftGauge (d := d) T) hX
  simpa only [inverseCompatibleX₁, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, hA, Matrix.mul_one] using h

/-- The literal $u=\sigma(K^\dagger\otimes K)v^\dagger$ contraction, with
$K$ the actual weighted comparison and no permutation of the gate indices.
Source: arXiv:2502.20257, lines 5444–5487. This is an algebraic gate identity,
not the subsequent unitarity conclusion. -/
theorem sourceU_eq_smul_inverseCompatibleComparisonK_kronecker_sourceV_adjoint
    (hT : ∀ i j, physicalAdjointTensor U i j =
      (T : Matrix (Fin D) (Fin D) ℂ)ᴴ * U i j * T)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) (σ : ℂ)
    (hσ : (T : Matrix (Fin D) (Fin D) ℂ) *
      (T : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) = σ • 1) :
    let K := inverseCompatibleComparisonK U T ρ hρ
    sourceU U ρ hρ = σ • ((Kᴴ ⊗ₖ K) * (sourceV U ρ hρ)ᴴ) := by
  let K := inverseCompatibleComparisonK U T ρ hρ
  let Tc := (T : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ)
  have hunit : (T : Matrix (Fin D) (Fin D) ℂ)ᴴ * T = 1 := T.property.1
  have hphase : Tc * (T : Matrix (Fin D) (Fin D) ℂ) = σ • 1 := by
    have h := congrArg (fun M ↦ (T : Matrix (Fin D) (Fin D) ℂ)ᴴ * M * T) hσ
    simpa only [← Matrix.mul_assoc, hunit, Matrix.one_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one] using h
  have hY₂ := sourceY₂_eq_inverseCompatibleComparisonK_adjoint U T hT ρ hρ
  have hY₁ := (inverseCompatibleComparison U T hT ρ hρ).2.2.1
  change sourceY₂ U = Kᴴ * (sourceX₁ U ρ hρ)ᴴ *
    inverseCompatibleLeftGauge (d := d) T at hY₂
  change sourceY₁ U ρ hρ = K * inverseCompatibleY₁ U T at hY₁
  ext ⟨l, s⟩ ⟨i, j⟩
  let C : Matrix (Fin r[U]) (Fin D) ℂ := fun r γ ↦ star (sourceX₁ U ρ hρ (i, γ) r)
  let E : Matrix (Fin D) (Fin ℓ[U]) ℂ := fun δ t ↦ star (sourceX₂ U (δ, j) t)
  have hleft (β : Fin D) : sourceY₂ U l (i, β) = (Kᴴ * C * Tc) l β := by
    rw [hY₂]
    simp only [inverseCompatibleLeftGauge, Matrix.mul_apply, Fintype.sum_prod_type,
      Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.conjTranspose_apply,
      ite_mul, one_mul, zero_mul, mul_ite, mul_zero,
      Finset.sum_ite_irrel, Finset.sum_const_zero, Fintype.sum_ite_eq']
    rfl
  have hright (β : Fin D) : sourceY₁ U ρ hρ s (β, j) =
      ((T : Matrix (Fin D) (Fin D) ℂ) * E * Kᵀ) β s := by
    rw [hY₁]
    simp only [inverseCompatibleY₁, inverseCompatibleRightGauge, Matrix.mul_apply,
      Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Matrix.conjTranspose_apply, Matrix.transpose_apply, Finset.mul_sum,
      Finset.sum_mul, mul_ite, mul_one, mul_zero, Fintype.sum_ite_eq']
    simp only [E]
    apply Finset.sum_congr₂
    intro t _ δ _
    ring
  have hcontract : (Kᴴ * C * Tc) * ((T : Matrix (Fin D) (Fin D) ℂ) * E * Kᵀ) =
      σ • (Kᴴ * C * E * Kᵀ) := by
    calc
      _ = Kᴴ * C * (Tc * (T : Matrix (Fin D) (Fin D) ℂ)) * E * Kᵀ := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hphase]; simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  rw [sourceU_apply]
  simp_rw [hleft, hright]
  rw [← Matrix.mul_apply, hcontract]
  simp only [Matrix.smul_apply, smul_eq_mul]
  congr 1
  change (Kᴴ * C * E * Kᵀ) l s = ((Kᴴ ⊗ₖ K) * (sourceV U ρ hρ)ᴴ) (l, s) (i, j)
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    Matrix.conjTranspose_apply, sourceV_apply, star_sum, star_mul, Matrix.transpose_apply,
    Finset.mul_sum, Finset.sum_mul]
  dsimp only [C, E]
  rw [Fintype.sum_reverse_three]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr₂
  intro t _ γ _
  ring

end MPOTensor
