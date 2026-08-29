/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SourceUClosedNetwork

/-!
# The second-cut metric in the closed $Y_1$--$X_2$ mixed network

This file factors the second-cut range projector through the right inverse
$Z_2$ and exposes the resulting eight-index formula for the auxiliary
mixed-kernel Gram entry. The metric is $H_2=Z_2Z_2^\dagger$; no result
identifies $H_2$ with the identity or asserts an ambient coisometry.

The surrounding mixed network is not the paper gate $u$, so these declarations
are not attributed to CPSV17 equation `uUnitary`.
-/

open scoped Matrix BigOperators ComplexOrder
open Matrix

namespace MPOTensor

variable {d D : ℕ} (U : MPOTensor d D)

/-- Exact second-cut range-projector factorization through the right inverse.

Source: arXiv:1703.09188, equations `Z1Z2` and `YZ=1`, lines 495--506. -/
theorem sourceX₂_mul_conjTranspose_eq_sourceCutM₂_mul_secondCutMetric
    : sourceX₂ U * (sourceX₂ U)ᴴ =
      sourceCutM₂ U * (sourceZ₂ U * (sourceZ₂ U)ᴴ) * (sourceCutM₂ U)ᴴ := by
  have hXZ : sourceCutM₂ U * sourceZ₂ U = sourceX₂ U := by
    rw [sourceCutM₂_eq_sourceX₂_mul_sourceY₂, Matrix.mul_assoc,
      sourceY₂_mul_sourceZ₂, Matrix.mul_one]
  calc
    sourceX₂ U * (sourceX₂ U)ᴴ =
        (sourceCutM₂ U * sourceZ₂ U) * (sourceCutM₂ U * sourceZ₂ U)ᴴ := by
      rw [hXZ]
    _ = sourceCutM₂ U * (sourceZ₂ U * (sourceZ₂ U)ᴴ) * (sourceCutM₂ U)ᴴ := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]


/-- The auxiliary $Y_1$--$X_2$ Gram entry with the exact second-cut metric
$H_2=Z_2Z_2^\dagger$ and all eight virtual and physical indices explicit.

Algebraic mixed-cut identity; not CPSV17 equation `uUnitary`. -/
theorem sourceY₁X₂_gram_apply_eq_secondCutMetric
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (p q : Fin d × Fin d) :
    (∑ lr : Fin ℓ[U] × Fin r[U],
      sourceY₁X₂ U ρ hρ lr q * star (sourceY₁X₂ U ρ hρ lr p)) =
      ∑ β : Fin D, ∑ δ : Fin D, ∑ γ : Fin D, ∑ α : Fin D,
      ∑ j : Fin d, ∑ a : Fin D, ∑ k : Fin d, ∑ c : Fin D,
        ρ α γ *
          doubleLayerTensor (physicalAdjointTensor U) q.1 p.1
            (finProdFinEquiv (γ, α)) (finProdFinEquiv (β, δ)) *
          (U q.2 j β a *
            (sourceZ₂ U * (sourceZ₂ U)ᴴ) (j, a) (k, c) *
              star (U p.2 k δ c)) := by
  rw [sourceY₁X₂_gram_apply_eq_closed_output_letter]
  simp_rw [sourceX₂_mul_conjTranspose_eq_sourceCutM₂_mul_secondCutMetric U]
  let H := sourceZ₂ U * (sourceZ₂ U)ᴴ
  have hentry (β δ : Fin D) (i i' : Fin d) :
      (sourceCutM₂ U * H * (sourceCutM₂ U)ᴴ) (β, i) (δ, i') =
        ∑ j : Fin d, ∑ a : Fin D, ∑ k : Fin d, ∑ c : Fin D,
          U i j β a * H (j, a) (k, c) * star (U i' k δ c) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, sourceCutM₂_apply]
    simp_rw [Finset.sum_mul]
    let f := fun (j : Fin d) (a : Fin D) (k : Fin d) (c : Fin D) ↦
      U i j β a * H (j, a) (k, c) * star (U i' k δ c)
    change (∑ k, ∑ c, ∑ j, ∑ a, f j a k c) =
      ∑ j, ∑ a, ∑ k, ∑ c, f j a k c
    calc
      _ = ∑ k, ∑ j, ∑ c, ∑ a, f j a k c := by
        apply Finset.sum_congr rfl
        intro k _
        exact Finset.sum_comm
      _ = ∑ j, ∑ k, ∑ c, ∑ a, f j a k c := Finset.sum_comm
      _ = ∑ j, ∑ k, ∑ a, ∑ c, f j a k c := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        exact Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        exact Finset.sum_comm
  apply Finset.sum_congr rfl
  intro β _
  apply Finset.sum_congr rfl
  intro δ _
  apply Finset.sum_congr rfl
  intro γ _
  apply Finset.sum_congr rfl
  intro α _
  rw [hentry]
  dsimp only [H]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]


end MPOTensor
