/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixIsometryEntries
import TNLean.MPS.MPU.Simple
import TNLean.MPS.MPU.SourceFactors

/-!
# Source-factor and physical-adjoint contraction identities

This module records the algebraic identities used before the finite-sum contraction in
arXiv:1703.09188, Lemma `lemuisometry` (lines 545--557). It records how the physical adjoint
acts on MPU tensors and their periodic operators, gives the exact output-first double-layer
entry with its bond-pair order, and recovers the two right source factors from the source cuts.

The first source cut uses rows `(left virtual, down physical)`, so its weight is literally
`ρ ⊗ₖ 1` in product-index order. The output-first double layer uses `(α, γ)` for its
left bond
pair and `(β, δ)` for its right bond pair.

This module does not identify the resulting finite sum with
`sourceY₁X₂ᴴ * sourceY₁X₂` and proves no isometry or rank theorem. In
particular, it establishes no Gram formula for the paper gate $u$.

## Main results

* `physicalAdjointTensor_physicalAdjointTensor` -- physical adjoint is involutive.
* `IsMPU.physicalAdjointTensor` -- physical adjoint preserves the MPU property.
* `doubleLayerTensor_physicalAdjointTensor_apply` -- output-first double-layer entry formula.
* `sourceY₁_eq_sourceX₁_conjTranspose_mul_weight_mul_sourceCutM₁` -- weighted recovery
  of `Y₁`.
* `sourceY₂_eq_sourceX₂_conjTranspose_mul_sourceCutM₂` -- unweighted recovery of `Y₂`.
* `mpo_physicalAdjointTensor_eq_conjTranspose` -- periodic MPO conjugate-transpose identity.
-/

open scoped Matrix BigOperators ComplexOrder Kronecker
open Matrix

namespace MPOTensor

variable {d D : ℕ} (U : MPOTensor d D)

/-- Physical adjoint is an involution. This is the local algebraic involution underlying the
output-layer reflection used in arXiv:1703.09188, Lemma `lemuisometry` (lines 545--557). -/
@[simp] theorem physicalAdjointTensor_physicalAdjointTensor (U : MPOTensor d D) :
    physicalAdjointTensor (physicalAdjointTensor U) = U := by
  ext i j α β
  simp only [physicalAdjointTensor_apply, star_star]

/-- Passing to the physical adjoint preserves the MPU property. The proof transposes the
periodic unitarity equation from arXiv:1703.09188, equation `UisUnitary` (lines 327--335). -/
theorem IsMPU.physicalAdjointTensor {U : MPOTensor d D} (hU : IsMPU U) :
    IsMPU (physicalAdjointTensor U) := by
  intro N hN
  rw [Matrix.mem_unitaryGroup_iff']
  simp only [Matrix.star_eq_conjTranspose]
  ext σ τ
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    mpo_physicalAdjointTensor]
  simpa only [Matrix.one_apply, star_star] using
    Matrix.sum_mul_star_eq_ite_of_mul_conjTranspose_eq_one
      (mpo U N) (hU.mpo_mul_conjTranspose_mpo hN) σ τ

/-- Entrywise output-layer form of the physical-adjoint double layer.

The left doubled bond is ordered `(α, γ)` and the right doubled bond is ordered `(β, δ)`.
Thus the first factor is `U i j α β`, while the reflected output factor is
`star (U k j γ δ)`. This is the orientation used before the contraction in
arXiv:1703.09188, Lemma `lemuisometry` (lines 545--557). -/
theorem doubleLayerTensor_physicalAdjointTensor_apply
    (U : MPOTensor d D) (i k : Fin d) (α γ β δ : Fin D) :
    doubleLayerTensor (physicalAdjointTensor U) i k
        (finProdFinEquiv (α, γ)) (finProdFinEquiv (β, δ)) =
      ∑ j : Fin d, U i j α β * star (U k j γ δ) := by
  simp [doubleLayerTensor, mulTensor_apply, Matrix.sum_apply, kroneckerMap_apply]

/-- Recover the first right source factor by applying the weighted left inverse of `X₁` to
`M₁ = X₁Y₁`. The product-index weight is `ρ ⊗ₖ I_d`, corresponding to the graphically
written
`I_d ⊗ ρ` in arXiv:1703.09188, equations `Y1Y1X1X1`--`X1X2b` (lines 487--526). -/
theorem sourceY₁_eq_sourceX₁_conjTranspose_mul_weight_mul_sourceCutM₁
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    sourceY₁ U ρ hρ =
      (sourceX₁ U ρ hρ)ᴴ * sourceWeight (d := d) ρ * sourceCutM₁ U := by
  calc
    sourceY₁ U ρ hρ =
        (1 : Matrix (Fin r[U]) (Fin r[U]) ℂ) * sourceY₁ U ρ hρ := by
      rw [Matrix.one_mul]
    _ = ((sourceX₁ U ρ hρ)ᴴ * sourceWeight (d := d) ρ * sourceX₁ U ρ hρ) *
          sourceY₁ U ρ hρ := by rw [sourceX₁_weighted_isometry]
    _ = (sourceX₁ U ρ hρ)ᴴ * sourceWeight (d := d) ρ *
          (sourceX₁ U ρ hρ * sourceY₁ U ρ hρ) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [← sourceCutM₁_eq_sourceX₁_mul_sourceY₁]

/-- Recover the second right source factor by applying the ordinary left inverse of `X₂` to
`M₂ = X₂Y₂`. This is the unweighted normalization in arXiv:1703.09188, equations
`Y1Y1X1X1`--`X1X2b` (lines 487--526). -/
theorem sourceY₂_eq_sourceX₂_conjTranspose_mul_sourceCutM₂ :
    sourceY₂ U = (sourceX₂ U)ᴴ * sourceCutM₂ U := by
  calc
    sourceY₂ U = (1 : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ) * sourceY₂ U := by
      rw [Matrix.one_mul]
    _ = ((sourceX₂ U)ᴴ * sourceX₂ U) * sourceY₂ U := by
      rw [sourceX₂_isometry]
    _ = (sourceX₂ U)ᴴ * (sourceX₂ U * sourceY₂ U) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [← sourceCutM₂_eq_sourceX₂_mul_sourceY₂]

/-- The periodic MPO of the physical adjoint is the matrix conjugate transpose. This is the
matrix-level form of the output-layer identity used in arXiv:1703.09188, Lemma `lemuisometry`
(lines 545--557). -/
theorem mpo_physicalAdjointTensor_eq_conjTranspose (U : MPOTensor d D) (N : ℕ) :
    mpo (physicalAdjointTensor U) N = (mpo U N)ᴴ := by
  ext σ τ
  exact mpo_physicalAdjointTensor U N σ τ

end MPOTensor
