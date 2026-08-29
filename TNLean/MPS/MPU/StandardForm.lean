/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalBlocking
import TNLean.MPS.MPU.SourceUOpenTail

/-!
# Auxiliary mixed-cut open-leg two-site equations

This file records two purely algebraic factorizations through the auxiliary
mixed kernels $Y_1$--$X_2$ and $X_1$--$Y_2$. These kernels are not the paper
gates $u$ and $v$ in CPSV17 equations `uu` and `vdagger`, and these identities
are not attributed to the paper's `StandardForm` figure.
-/

open scoped Matrix BigOperators ComplexOrder
open Matrix

namespace MPOTensor

variable {d D : ℕ} (U : MPOTensor d D)

namespace SourceFactors

/-- The concrete two-site block factors through $X_1$--$(Y_1$--$X_2)$--$Y_2$ for any supplied
source factorization. The decoded source row has order `(l, r)`.

Auxiliary consequence of $M_1=X_1Y_1$ and $M_2=X_2Y_2$; this is not a
CPSV17 standard-form gate identity. -/
theorem blockTwo_apply_eq_sum_X₁_mul_sourceY₁X₂_mul_Y₂
    {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ)
    (i j : Fin (d * d)) (α γ : Fin D) :
    blockTwo U i j α γ =
      ∑ r : Fin r[U], ∑ l : Fin ℓ[U],
        S.X₁ (α, (finProdFinEquiv.symm j).1) r *
          sourceY₁X₂ U S (l, r) (finProdFinEquiv.symm i) *
            S.Y₂ l ((finProdFinEquiv.symm j).2, γ) := by
  exact mul_apply_eq_sum_X₁_mul_sourceY₁X₂_mul_Y₂ U S
    (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1
    (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2 α γ

/-- The reflected open two-site product factors through $X_2$--$(X_1$--$Y_2)$--$Y_1$ for any
supplied source factorization. The physical row of the mixed kernel is `(j₂, j₁)`, and its
source column is `(r, l)`.

Auxiliary consequence of $M_1=X_1Y_1$ and $M_2=X_2Y_2$; this is not a
CPSV17 standard-form gate identity. -/
theorem mul_apply_eq_sum_X₂_mul_sourceX₁Y₂_reflected_mul_Y₁
    {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ)
    (i₁ j₁ i₂ j₂ : Fin d) (α γ : Fin D) :
    (U i₁ j₁ * U i₂ j₂) α γ =
      ∑ l : Fin ℓ[U], ∑ r : Fin r[U],
        S.X₂ (α, i₁) l * sourceX₁Y₂ U S (j₂, j₁) (r, l) * S.Y₁ r (i₂, γ) := by
  classical
  simp only [Matrix.mul_apply]
  have h₁ (β : Fin D) : U i₁ j₁ α β =
      ∑ l : Fin ℓ[U], S.X₂ (α, i₁) l * S.Y₂ l (j₁, β) := by
    simpa only [Matrix.mul_apply] using (X₂_mul_Y₂_apply U S α i₁ j₁ β).symm
  have h₂ (β : Fin D) : U i₂ j₂ β γ =
      ∑ r : Fin r[U], S.X₁ (β, j₂) r * S.Y₁ r (i₂, γ) := by
    simpa only [Matrix.mul_apply] using (X₁_mul_Y₁_apply U S β j₂ i₂ γ).symm
  simp_rw [h₁, h₂, Finset.sum_mul_sum]
  simp_rw [sourceX₁Y₂_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro β _
  ring

/-- The concrete two-site block has the reflected $X_2$--$(X_1$--$Y_2)$--$Y_1$ form for any
supplied source factorization. Its physical row and source column retain the
orders `(j₂, j₁)` and `(r, l)`.

Auxiliary consequence of $M_1=X_1Y_1$ and $M_2=X_2Y_2$; this is not a
CPSV17 standard-form gate identity. -/
theorem blockTwo_apply_eq_sum_X₂_mul_sourceX₁Y₂_reflected_mul_Y₁
    {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ)
    (i j : Fin (d * d)) (α γ : Fin D) :
    blockTwo U i j α γ =
      ∑ l : Fin ℓ[U], ∑ r : Fin r[U],
        S.X₂ (α, (finProdFinEquiv.symm i).1) l *
          sourceX₁Y₂ U S
            ((finProdFinEquiv.symm j).2, (finProdFinEquiv.symm j).1) (r, l) *
            S.Y₁ r ((finProdFinEquiv.symm i).2, γ) := by
  exact mul_apply_eq_sum_X₂_mul_sourceX₁Y₂_reflected_mul_Y₁ U S
    (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1
    (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2 α γ

end SourceFactors

/-- The concrete two-site block factors through the auxiliary $X_1$--$(Y_1$--$X_2)$--$Y_2$ form.
The decoded ket and bra pairs retain the source tensor's row order `(l, r)`.

Auxiliary consequence of $M_1=X_1Y_1$ and $M_2=X_2Y_2$; this is not a
CPSV17 standard-form gate identity. -/
theorem blockTwo_apply_eq_sum_sourceX₁_mul_sourceY₁X₂_mul_sourceY₂
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (i j : Fin (d * d)) (α γ : Fin D) :
    blockTwo U i j α γ =
      ∑ r : Fin r[U], ∑ l : Fin ℓ[U],
        sourceX₁ U ρ hρ (α, (finProdFinEquiv.symm j).1) r *
          sourceY₁X₂ U ρ hρ (l, r) (finProdFinEquiv.symm i) *
            sourceY₂ U l ((finProdFinEquiv.symm j).2, γ) := by
  simpa [sourceFactors, sourceFactors_sourceY₁X₂] using
    SourceFactors.blockTwo_apply_eq_sum_X₁_mul_sourceY₁X₂_mul_Y₂ U
      (sourceFactors U ρ hρ) i j α γ

/-- The reflected open two-site product factors through the auxiliary
$X_2$--$(X_1$--$Y_2)$--$Y_1$ form. The physical row of the mixed kernel is
explicitly `(j₂, j₁)`, and its source column is explicitly `(r, l)`.

Auxiliary consequence of $M_1=X_1Y_1$ and $M_2=X_2Y_2$; this is not a
CPSV17 standard-form gate identity. -/
theorem mul_apply_eq_sum_sourceX₂_mul_sourceX₁Y₂_reflected_mul_sourceY₁
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (i₁ j₁ i₂ j₂ : Fin d) (α γ : Fin D) :
    (U i₁ j₁ * U i₂ j₂) α γ =
      ∑ l : Fin ℓ[U], ∑ r : Fin r[U],
        sourceX₂ U (α, i₁) l * sourceX₁Y₂ U ρ hρ (j₂, j₁) (r, l) *
          sourceY₁ U ρ hρ r (i₂, γ) := by
  simpa [sourceFactors, sourceFactors_sourceX₁Y₂] using
    SourceFactors.mul_apply_eq_sum_X₂_mul_sourceX₁Y₂_reflected_mul_Y₁ U
      (sourceFactors U ρ hρ) i₁ j₁ i₂ j₂ α γ

/-- The concrete two-site block in the reflected paper form $X_2$--$(X_1$--$Y_2)$--$Y_1$.
The standard product-index decoding exposes `(j₂, j₁)` and `(r, l)` without an
implicit identification of either order.

Auxiliary consequence of $M_1=X_1Y_1$ and $M_2=X_2Y_2$; this is not a
CPSV17 standard-form gate identity. -/
theorem blockTwo_apply_eq_sum_sourceX₂_mul_sourceX₁Y₂_reflected_mul_sourceY₁
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (i j : Fin (d * d)) (α γ : Fin D) :
    blockTwo U i j α γ =
      ∑ l : Fin ℓ[U], ∑ r : Fin r[U],
        sourceX₂ U (α, (finProdFinEquiv.symm i).1) l *
          sourceX₁Y₂ U ρ hρ
            ((finProdFinEquiv.symm j).2, (finProdFinEquiv.symm j).1) (r, l) *
            sourceY₁ U ρ hρ r ((finProdFinEquiv.symm i).2, γ) := by
  exact mul_apply_eq_sum_sourceX₂_mul_sourceX₁Y₂_reflected_mul_sourceY₁ U ρ hρ
    (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1
    (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2 α γ

end MPOTensor
