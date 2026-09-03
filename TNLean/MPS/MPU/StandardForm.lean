/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalBlocking
import TNLean.MPS.MPU.SourceUV

/-!
# Two-site source-gate equations

This file records the two source-faithful factorizations of a two-site MPO
letter through the paper gates $u=Y_2\mathbin{-}Y_1$ and
$v=X_1\mathbin{-}X_2$, together with the open one-sided contraction of the
gate $v$ against the first right source factor.

Source: arXiv:1703.09188, equations `uuvv`, `uu`, and `vdagger`
(lines 532--543), used by the standard form of Definition `SF`
(lines 603--622).
-/

open scoped Matrix BigOperators ComplexOrder
open Matrix

namespace MPOTensor

variable {d D : ℕ} (U : MPOTensor d D)

namespace SourceFactors

/-- Contracting the right source leg of $v=X_1\mathbin{-}X_2$ with $Y_1$
leaves the open $X_2$ leg for supplied source factors.

Source: CPSV17 equations `uuvv` and `vdagger`, lines 532--543. -/
theorem sum_sourceV_mul_Y₁
    {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ)
    (i₁ j₁ i₂ : Fin d) (α : Fin D) (l : Fin ℓ[U]) :
    (∑ r : Fin r[U], sourceV U S (i₁, i₂) (r, l) * S.Y₁ r (α, j₁)) =
      ∑ β : Fin D, U i₁ j₁ α β * S.X₂ (β, i₂) l := by
  classical
  simp only [sourceV_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro β _
  calc
    _ = (∑ r : Fin r[U], S.X₁ (i₁, β) r * S.Y₁ r (α, j₁)) *
        S.X₂ (β, i₂) l := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = _ := by rw [← Matrix.mul_apply, X₁_mul_Y₁_apply]

/-- The open two-site product factors through the paper gate $v=X_1\mathbin{-}X_2$
and the two right source factors.

Source: CPSV17 equations `uuvv` and `vdagger`, lines 532--543. -/
theorem mul_apply_eq_sum_sourceV_mul_Y₁_mul_Y₂
    {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ)
    (i₁ j₁ i₂ j₂ : Fin d) (α γ : Fin D) :
    (U i₁ j₁ * U i₂ j₂) α γ =
      ∑ r : Fin r[U], ∑ l : Fin ℓ[U],
        sourceV U S (i₁, i₂) (r, l) * S.Y₁ r (α, j₁) * S.Y₂ l (j₂, γ) := by
  classical
  symm
  calc
    _ = ∑ l : Fin ℓ[U],
        (∑ r : Fin r[U], sourceV U S (i₁, i₂) (r, l) * S.Y₁ r (α, j₁)) *
          S.Y₂ l (j₂, γ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.sum_mul]
    _ = ∑ l : Fin ℓ[U], (∑ β : Fin D, U i₁ j₁ α β * S.X₂ (β, i₂) l) *
          S.Y₂ l (j₂, γ) := by
      apply Finset.sum_congr rfl
      intro l _
      rw [sum_sourceV_mul_Y₁ U S]
    _ = ∑ β : Fin D, U i₁ j₁ α β *
        (∑ l : Fin ℓ[U], S.X₂ (β, i₂) l * S.Y₂ l (j₂, γ)) := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro β _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = ∑ β : Fin D, U i₁ j₁ α β * U i₂ j₂ β γ := by
      apply Finset.sum_congr rfl
      intro β _
      rw [← Matrix.mul_apply, X₂_mul_Y₂_apply]
    _ = _ := by rw [Matrix.mul_apply]

/-- The two-site product factors through the two left source factors, the paper
gate $u=Y_2\mathbin{-}Y_1$, and the remaining $X_1$ factor:
$$
  (U^{i_1j_1}U^{i_2j_2})_{\alpha\gamma}
  =\sum_{\ell,r}(X_2)_{(\alpha,i_1),\ell}
    u_{(\ell,r),(j_1,j_2)}(X_1)_{(i_2,\gamma),r}.
$$

Source: CPSV17 equations `uuvv` and `uu`, lines 532--543. -/
theorem mul_apply_eq_sum_X₂_mul_sourceU_mul_X₁
    {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ)
    (i₁ j₁ i₂ j₂ : Fin d) (α γ : Fin D) :
    (U i₁ j₁ * U i₂ j₂) α γ =
      ∑ l : Fin ℓ[U], ∑ r : Fin r[U],
        S.X₂ (α, i₁) l * sourceU U S (l, r) (j₁, j₂) * S.X₁ (i₂, γ) r := by
  classical
  simp only [Matrix.mul_apply]
  have h₁ (β : Fin D) : U i₁ j₁ α β =
      ∑ l : Fin ℓ[U], S.X₂ (α, i₁) l * S.Y₂ l (j₁, β) := by
    simpa only [Matrix.mul_apply] using (X₂_mul_Y₂_apply U S α i₁ j₁ β).symm
  have h₂ (β : Fin D) : U i₂ j₂ β γ =
      ∑ r : Fin r[U], S.X₁ (i₂, γ) r * S.Y₁ r (β, j₂) := by
    simpa only [Matrix.mul_apply] using (X₁_mul_Y₁_apply U S i₂ γ β j₂).symm
  simp_rw [h₁, h₂, Finset.sum_mul_sum]
  simp_rw [sourceU_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro β _
  ring

/-- The concrete two-site block has the $X_2$--$u$--$X_1$ source form.

Source: CPSV17 equations `uuvv` and `uu`, lines 532--543. -/
theorem blockTwo_apply_eq_sum_X₂_mul_sourceU_mul_X₁
    {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ)
    (i j : Fin (d * d)) (α γ : Fin D) :
    blockTwo U i j α γ =
      ∑ l : Fin ℓ[U], ∑ r : Fin r[U],
        S.X₂ (α, (finProdFinEquiv.symm i).1) l *
          sourceU U S (l, r) (finProdFinEquiv.symm j) *
            S.X₁ ((finProdFinEquiv.symm i).2, γ) r := by
  exact mul_apply_eq_sum_X₂_mul_sourceU_mul_X₁ U S
    (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1
    (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2 α γ

/-- The concrete two-site block has the $v$--$Y_1$--$Y_2$ source form.

Source: CPSV17 equations `uuvv` and `vdagger`, lines 532--543. -/
theorem blockTwo_apply_eq_sum_sourceV_mul_Y₁_mul_Y₂
    {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ)
    (i j : Fin (d * d)) (α γ : Fin D) :
    blockTwo U i j α γ =
      ∑ r : Fin r[U], ∑ l : Fin ℓ[U],
        sourceV U S (finProdFinEquiv.symm i) (r, l) *
          S.Y₁ r (α, (finProdFinEquiv.symm j).1) *
            S.Y₂ l ((finProdFinEquiv.symm j).2, γ) := by
  exact mul_apply_eq_sum_sourceV_mul_Y₁_mul_Y₂ U S
    (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1
    (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2 α γ

end SourceFactors

/-- Contracting the right source leg of the paper gate $v=X_1\mathbin{-}X_2$
with $Y_1$ leaves the open $X_2$ leg of the first tensor letter.

Source: CPSV17 equations `uuvv` and `vdagger`, lines 532--543. -/
theorem sum_sourceV_mul_sourceY₁
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (i₁ j₁ i₂ : Fin d) (α : Fin D) (l : Fin ℓ[U]) :
    (∑ r : Fin r[U],
      sourceV U ρ hρ (i₁, i₂) (r, l) * sourceY₁ U ρ hρ r (α, j₁)) =
      ∑ β : Fin D, U i₁ j₁ α β * sourceX₂ U (β, i₂) l := by
  classical
  simp only [sourceV_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro β _
  calc
    _ = (∑ r : Fin r[U], sourceX₁ U ρ hρ (i₁, β) r *
          sourceY₁ U ρ hρ r (α, j₁)) * sourceX₂ U (β, i₂) l := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = _ := by
      rw [← Matrix.mul_apply, sourceX₁_mul_sourceY₁_apply]

/-- The open two-site matrix product factors through the paper gate $v$ and
the two right source factors.

Source: CPSV17 equations `uuvv` and `vdagger`, lines 532--543. -/
theorem mul_apply_eq_sum_sourceV_mul_sourceY₁_mul_sourceY₂
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (i₁ j₁ i₂ j₂ : Fin d) (α γ : Fin D) :
    (U i₁ j₁ * U i₂ j₂) α γ =
      ∑ r : Fin r[U], ∑ l : Fin ℓ[U],
        sourceV U ρ hρ (i₁, i₂) (r, l) * sourceY₁ U ρ hρ r (α, j₁) *
          sourceY₂ U l (j₂, γ) := by
  simpa [sourceFactors, sourceFactors_sourceV] using
    SourceFactors.mul_apply_eq_sum_sourceV_mul_Y₁_mul_Y₂ U
      (sourceFactors U ρ hρ) i₁ j₁ i₂ j₂ α γ

/-- Pair-index reformulation of the open two-site factorization. The output
pair is \(q\), while \(j\) is the input pair. The name \(p\) remains reserved for the
retained output pair in the conjugated factor of a later Gram contraction.

Source: CPSV17 equations `uuvv` and `vdagger`, lines 532--543. This source-$v$
identity does not prove equation `uUnitary` or Lemma `lemuisometry`, which concern
source gate $u$. -/
theorem mul_apply_eq_sum_sourceV_mul_sourceY₁_mul_sourceY₂_pair
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (q j : Fin d × Fin d) (α γ : Fin D) :
    (U q.1 j.1 * U q.2 j.2) α γ =
      ∑ r : Fin r[U], ∑ l : Fin ℓ[U],
        sourceV U ρ hρ q (r, l) * sourceY₁ U ρ hρ r (α, j.1) *
          sourceY₂ U l (j.2, γ) := by
  exact mul_apply_eq_sum_sourceV_mul_sourceY₁_mul_sourceY₂ U ρ hρ
    q.1 j.1 q.2 j.2 α γ

/-- The concrete two-site block has the compact-SVD $X_2$--$u$--$X_1$ source
form.

Source: CPSV17 equations `uuvv` and `uu`, lines 532--543. -/
theorem blockTwo_apply_eq_sum_sourceX₂_mul_sourceU_mul_sourceX₁
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (i j : Fin (d * d)) (α γ : Fin D) :
    blockTwo U i j α γ =
      ∑ l : Fin ℓ[U], ∑ r : Fin r[U],
        sourceX₂ U (α, (finProdFinEquiv.symm i).1) l *
          sourceU U ρ hρ (l, r) (finProdFinEquiv.symm j) *
            sourceX₁ U ρ hρ ((finProdFinEquiv.symm i).2, γ) r := by
  simpa [sourceFactors, sourceFactors_sourceU] using
    SourceFactors.blockTwo_apply_eq_sum_X₂_mul_sourceU_mul_X₁ U
      (sourceFactors U ρ hρ) i j α γ

/-- The concrete two-site block has the compact-SVD $v$--$Y_1$--$Y_2$ source
form.

Source: CPSV17 equations `uuvv` and `vdagger`, lines 532--543. -/
theorem blockTwo_apply_eq_sum_sourceV_mul_sourceY₁_mul_sourceY₂
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (i j : Fin (d * d)) (α γ : Fin D) :
    blockTwo U i j α γ =
      ∑ r : Fin r[U], ∑ l : Fin ℓ[U],
        sourceV U ρ hρ (finProdFinEquiv.symm i) (r, l) *
          sourceY₁ U ρ hρ r (α, (finProdFinEquiv.symm j).1) *
            sourceY₂ U l ((finProdFinEquiv.symm j).2, γ) := by
  simpa [sourceFactors, sourceFactors_sourceV] using
    SourceFactors.blockTwo_apply_eq_sum_sourceV_mul_Y₁_mul_Y₂ U
      (sourceFactors U ρ hρ) i j α γ

end MPOTensor
