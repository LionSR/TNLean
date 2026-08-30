/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SourceFactors

/-!
# Paper source gates and auxiliary mixed source-factor kernels

This file defines the paper gates $u=Y_2\mathbin{-}Y_1$ and
$v=X_1\mathbin{-}X_2$ from arXiv:1703.09188, equations `uuvv`, `uu`, and
`vdagger` (lines 532--543), with the triangle assignment made explicit in
arXiv:2502.20257, equation `eq:uv` (lines 704--760).

It also retains the algebraically useful mixed contractions $Y_1\mathbin{-}X_2$
and $X_1\mathbin{-}Y_2$ under explicit factor-pair names. Those auxiliary
kernels give an ordinary two-letter MPO factorization, but they are not the
paper gates and carry no `uuvv`, `lemuisometry`, or standard-form claim.
-/

open scoped Matrix BigOperators ComplexOrder
open Matrix

namespace MPOTensor

variable {d D : ℕ} (U : MPOTensor d D)

namespace SourceFactors

/-- The auxiliary $Y_1$--$X_2$ contraction for supplied source factors.

This is a mixed-cut kernel used by exact algebraic factorizations below. It is
not the tensor $u$ in CPSV17 equation `uu` or FBC25 equation `eq:uv`. -/
def sourceY₁X₂ {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ) :
    Matrix (Fin ℓ[U] × Fin r[U]) (Fin d × Fin d) ℂ :=
  fun (l, r) (i₁, i₂) ↦ ∑ β : Fin D, S.Y₁ r (i₁, β) * S.X₂ (β, i₂) l

/-- The auxiliary $X_1$--$Y_2$ contraction for supplied source factors.

This is a mixed-cut kernel used by exact algebraic factorizations below. It is
not the tensor $v$ in CPSV17 equation `vdagger` or FBC25 equation `eq:uv`. -/
def sourceX₁Y₂ {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ) :
    Matrix (Fin d × Fin d) (Fin r[U] × Fin ℓ[U]) ℂ :=
  fun (j₁, j₂) (r, l) ↦ ∑ α : Fin D, S.X₁ (α, j₁) r * S.Y₂ l (j₂, α)

/-- The paper gate $u : d^2 \to \ell\times r$ for supplied source factors.
Its two triangles are $Y_2$ and $Y_1$, in that order.

Source: CPSV17 equations `uuvv` and `uu` (lines 532--543), and FBC25 equation
`eq:uv` (lines 704--760). -/
def sourceU {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ) :
    Matrix (Fin ℓ[U] × Fin r[U]) (Fin d × Fin d) ℂ :=
  fun (l, r) (i₁, i₂) ↦ ∑ β : Fin D, S.Y₂ l (i₁, β) * S.Y₁ r (i₂, β)

/-- The paper gate $v : r\times\ell \to d^2$ for supplied source factors.
Its two triangles are $X_1$ and $X_2$, in that order.

Source: CPSV17 equations `uuvv` and `vdagger` (lines 532--543), and FBC25
equation `eq:uv` (lines 704--760). -/
def sourceV {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ) :
    Matrix (Fin d × Fin d) (Fin r[U] × Fin ℓ[U]) ℂ :=
  fun (j₁, j₂) (r, l) ↦ ∑ α : Fin D, S.X₁ (α, j₁) r * S.X₂ (α, j₂) l

/-- Entry formula for the auxiliary $Y_1$--$X_2$ kernel with supplied factors.

Auxiliary mixed-cut identity; not CPSV17 equation `uu`. -/
@[simp] theorem sourceY₁X₂_apply {ρ : Matrix (Fin D) (Fin D) ℂ}
    (S : SourceFactors U ρ) (l : Fin ℓ[U]) (r : Fin r[U]) (i₁ i₂ : Fin d) :
    sourceY₁X₂ U S (l, r) (i₁, i₂) =
      ∑ β : Fin D, S.Y₁ r (i₁, β) * S.X₂ (β, i₂) l := rfl

/-- Entry formula for the auxiliary $X_1$--$Y_2$ kernel with supplied factors.

Auxiliary mixed-cut identity; not CPSV17 equation `vdagger`. -/
@[simp] theorem sourceX₁Y₂_apply {ρ : Matrix (Fin D) (Fin D) ℂ}
    (S : SourceFactors U ρ) (j₁ j₂ : Fin d) (r : Fin r[U]) (l : Fin ℓ[U]) :
    sourceX₁Y₂ U S (j₁, j₂) (r, l) =
      ∑ α : Fin D, S.X₁ (α, j₁) r * S.Y₂ l (j₂, α) := rfl

/-- Literal entry formula for the paper gate $u=Y_2\mathbin{-}Y_1$.

Source: CPSV17 equation `uu` (lines 532--543) and FBC25 equation `eq:uv`
(lines 704--760). -/
@[simp] theorem sourceU_apply {ρ : Matrix (Fin D) (Fin D) ℂ}
    (S : SourceFactors U ρ) (l : Fin ℓ[U]) (r : Fin r[U]) (i₁ i₂ : Fin d) :
    sourceU U S (l, r) (i₁, i₂) =
      ∑ β : Fin D, S.Y₂ l (i₁, β) * S.Y₁ r (i₂, β) := rfl

/-- Literal entry formula for the paper gate $v=X_1\mathbin{-}X_2$.

Source: CPSV17 equation `vdagger` (lines 532--543) and FBC25 equation `eq:uv`
(lines 704--760). -/
@[simp] theorem sourceV_apply {ρ : Matrix (Fin D) (Fin D) ℂ}
    (S : SourceFactors U ρ) (j₁ j₂ : Fin d) (r : Fin r[U]) (l : Fin ℓ[U]) :
    sourceV U S (j₁, j₂) (r, l) =
      ∑ α : Fin D, S.X₁ (α, j₁) r * S.X₂ (α, j₂) l := rfl

/-- Entry form of the first source-cut factorization for supplied factors.

Source: arXiv:1703.09188, equations `X1Y1` and `SVDforms2`, lines 508--528. -/
@[simp] theorem X₁_mul_Y₁_apply {ρ : Matrix (Fin D) (Fin D) ℂ}
    (S : SourceFactors U ρ) (α : Fin D) (j i : Fin d) (β : Fin D) :
    (S.X₁ * S.Y₁) (α, j) (i, β) = U i j α β := by
  rw [← S.sourceCutM₁_eq]
  rfl

/-- Entry form of the second source-cut factorization for supplied factors.

Source: arXiv:1703.09188, equations `X2Y2` and `SVDforms2`, lines 508--528. -/
@[simp] theorem X₂_mul_Y₂_apply {ρ : Matrix (Fin D) (Fin D) ℂ}
    (S : SourceFactors U ρ) (α : Fin D) (i j : Fin d) (β : Fin D) :
    (S.X₂ * S.Y₂) (α, i) (j, β) = U i j α β := by
  rw [← S.sourceCutM₂_eq]
  rfl

end SourceFactors

/-- The compact-SVD auxiliary $Y_1$--$X_2$ mixed-cut kernel.

This kernel is not the tensor $u$ in CPSV17 equation `uu` or FBC25 equation
`eq:uv`. -/
noncomputable def sourceY₁X₂ (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    Matrix (Fin ℓ[U] × Fin r[U]) (Fin d × Fin d) ℂ :=
  fun (l, r) (i₁, i₂) ↦ ∑ β : Fin D,
    sourceY₁ U ρ hρ r (i₁, β) * sourceX₂ U (β, i₂) l

/-- The compact-SVD auxiliary $X_1$--$Y_2$ mixed-cut kernel.

This kernel is not the tensor $v$ in CPSV17 equation `vdagger` or FBC25
equation `eq:uv`. -/
noncomputable def sourceX₁Y₂ (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    Matrix (Fin d × Fin d) (Fin r[U] × Fin ℓ[U]) ℂ :=
  fun (j₁, j₂) (r, l) ↦ ∑ α : Fin D,
    sourceX₁ U ρ hρ (α, j₁) r * sourceY₂ U l (j₂, α)

/-- The compact-SVD paper gate $u=Y_2\mathbin{-}Y_1$.

Source: CPSV17 equations `uuvv` and `uu` (lines 532--543), and FBC25 equation
`eq:uv` (lines 704--760). -/
noncomputable def sourceU (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    Matrix (Fin ℓ[U] × Fin r[U]) (Fin d × Fin d) ℂ :=
  SourceFactors.sourceU U (sourceFactors U ρ hρ)

/-- The compact-SVD paper gate $v=X_1\mathbin{-}X_2$.

Source: CPSV17 equations `uuvv` and `vdagger` (lines 532--543), and FBC25
equation `eq:uv` (lines 704--760). -/
noncomputable def sourceV (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    Matrix (Fin d × Fin d) (Fin r[U] × Fin ℓ[U]) ℂ :=
  SourceFactors.sourceV U (sourceFactors U ρ hρ)

/-- The compact-SVD source factors recover the paper gate $u$.

Source: CPSV17 equation `uu` (lines 532--543) and FBC25 equation `eq:uv`
(lines 704--760). -/
@[simp] theorem sourceFactors_sourceU
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    SourceFactors.sourceU U (sourceFactors U ρ hρ) = sourceU U ρ hρ := rfl

/-- The compact-SVD source factors recover the paper gate $v$.

Source: CPSV17 equation `vdagger` (lines 532--543) and FBC25 equation `eq:uv`
(lines 704--760). -/
@[simp] theorem sourceFactors_sourceV
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    SourceFactors.sourceV U (sourceFactors U ρ hρ) = sourceV U ρ hρ := rfl

/-- Literal compact-SVD entry formula for the paper gate $u=Y_2\mathbin{-}Y_1$.

Source: CPSV17 equation `uu` (lines 532--543) and FBC25 equation `eq:uv`
(lines 704--760). -/
@[simp] theorem sourceU_apply (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (l : Fin ℓ[U]) (r : Fin r[U]) (i₁ i₂ : Fin d) :
    sourceU U ρ hρ (l, r) (i₁, i₂) = ∑ β : Fin D,
      sourceY₂ U l (i₁, β) * sourceY₁ U ρ hρ r (i₂, β) := rfl

/-- Conjugate-transpose entry formula for the paper gate $u=Y_2\mathbin{-}Y_1$.

Source: CPSV17 equation `uu` (lines 532--543) and FBC25 equation `eq:uv`
(lines 704--760). -/
@[simp] theorem sourceU_conjTranspose_apply
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (i₁ i₂ : Fin d) (l : Fin ℓ[U]) (r : Fin r[U]) :
    (sourceU U ρ hρ)ᴴ (i₁, i₂) (l, r) = star (∑ β : Fin D,
      sourceY₂ U l (i₁, β) * sourceY₁ U ρ hρ r (i₂, β)) := rfl

/-- Literal compact-SVD entry formula for the paper gate $v=X_1\mathbin{-}X_2$.

Source: CPSV17 equation `vdagger` (lines 532--543) and FBC25 equation `eq:uv`
(lines 704--760). -/
@[simp] theorem sourceV_apply (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (j₁ j₂ : Fin d) (r : Fin r[U]) (l : Fin ℓ[U]) :
    sourceV U ρ hρ (j₁, j₂) (r, l) = ∑ α : Fin D,
      sourceX₁ U ρ hρ (α, j₁) r * sourceX₂ U (α, j₂) l := rfl

/-- Conjugate-transpose entry formula for the paper gate $v=X_1\mathbin{-}X_2$.

Source: CPSV17 equation `vdagger` (lines 532--543) and FBC25 equation `eq:uv`
(lines 704--760). -/
@[simp] theorem sourceV_conjTranspose_apply
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (r : Fin r[U]) (l : Fin ℓ[U]) (j₁ j₂ : Fin d) :
    (sourceV U ρ hρ)ᴴ (r, l) (j₁, j₂) = star (∑ α : Fin D,
      sourceX₁ U ρ hρ (α, j₁) r * sourceX₂ U (α, j₂) l) := rfl

/-- The compact-SVD factors recover the auxiliary $Y_1$--$X_2$ kernel.

Algebraic consequence of the compact-SVD source factors; this is not CPSV17 $u$. -/
@[simp] theorem sourceFactors_sourceY₁X₂
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    SourceFactors.sourceY₁X₂ U (sourceFactors U ρ hρ) = sourceY₁X₂ U ρ hρ := by
  rfl

/-- The compact-SVD factors recover the auxiliary $X_1$--$Y_2$ kernel.

Algebraic consequence of the compact-SVD source factors; this is not CPSV17 $v$. -/
@[simp] theorem sourceFactors_sourceX₁Y₂
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    SourceFactors.sourceX₁Y₂ U (sourceFactors U ρ hρ) = sourceX₁Y₂ U ρ hρ := by
  rfl

/-- Stable entry formula for the auxiliary $Y_1$--$X_2$ kernel.

Auxiliary mixed-cut identity; not CPSV17 equation `uu`. -/
@[simp] theorem sourceY₁X₂_apply (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (l : Fin ℓ[U]) (r : Fin r[U]) (i₁ i₂ : Fin d) :
    sourceY₁X₂ U ρ hρ (l, r) (i₁, i₂) = ∑ β : Fin D,
      sourceY₁ U ρ hρ r (i₁, β) * sourceX₂ U (β, i₂) l := rfl

/-- Stable entry formula for the auxiliary $X_1$--$Y_2$ kernel.

Auxiliary mixed-cut identity; not CPSV17 equation `vdagger`. -/
@[simp] theorem sourceX₁Y₂_apply (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (j₁ j₂ : Fin d) (r : Fin r[U]) (l : Fin ℓ[U]) :
    sourceX₁Y₂ U ρ hρ (j₁, j₂) (r, l) = ∑ α : Fin D,
      sourceX₁ U ρ hρ (α, j₁) r * sourceY₂ U l (j₂, α) := rfl

/-- Conjugate-transpose entry formula for the auxiliary $Y_1$--$X_2$ kernel.

Auxiliary mixed-cut identity; not CPSV17 equations `uuvv` or `uu`. -/
@[simp] theorem sourceY₁X₂_conjTranspose_apply
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (i₁ i₂ : Fin d) (l : Fin ℓ[U]) (r : Fin r[U]) :
    (sourceY₁X₂ U ρ hρ)ᴴ (i₁, i₂) (l, r) = star (∑ β : Fin D,
      sourceY₁ U ρ hρ r (i₁, β) * sourceX₂ U (β, i₂) l) := rfl

/-- Conjugate-transpose entry formula for the auxiliary $X_1$--$Y_2$ kernel.

Auxiliary mixed-cut identity; not CPSV17 equation `vdagger`. -/
@[simp] theorem sourceX₁Y₂_conjTranspose_apply
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (r : Fin r[U]) (l : Fin ℓ[U]) (j₁ j₂ : Fin d) :
    (sourceX₁Y₂ U ρ hρ)ᴴ (r, l) (j₁, j₂) = star (∑ α : Fin D,
      sourceX₁ U ρ hρ (α, j₁) r * sourceY₂ U l (j₂, α)) := rfl

/-- The traced product of two local letters factors through the two mixed kernels.

Algebraic mixed-cut factorization; not the CPSV17/FBC25 source gates. -/
theorem trace_mul_eq_sourceY₁X₂_mul_sourceX₁Y₂_swap
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (i₁ i₂ j₁ j₂ : Fin d) :
    Matrix.trace (U i₁ j₁ * U i₂ j₂) =
      ∑ lr : Fin ℓ[U] × Fin r[U],
        sourceY₁X₂ U ρ hρ lr (i₁, i₂) *
          sourceX₁Y₂ U ρ hρ (j₁, j₂) (lr.2, lr.1) := by
  classical
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, sourceY₁X₂, sourceX₁Y₂,
    Finset.mul_sum, Finset.sum_mul]
  have h₁ (α β : Fin D) :
      U i₁ j₁ α β = ∑ r, sourceX₁ U ρ hρ (α, j₁) r *
        sourceY₁ U ρ hρ r (i₁, β) := by
    simpa only [Matrix.mul_apply] using
      (sourceX₁_mul_sourceY₁_apply U ρ hρ α j₁ i₁ β).symm
  have h₂ (β α : Fin D) :
      U i₂ j₂ β α = ∑ l, sourceX₂ U (β, i₂) l * sourceY₂ U l (j₂, α) := by
    simpa only [Matrix.mul_apply] using
      (sourceX₂_mul_sourceY₂_apply U β i₂ j₂ α).symm
  simp_rw [h₁, h₂]
  simp only [Finset.mul_sum, Finset.sum_mul]
  let f := fun (α β : Fin D) (l : Fin ℓ[U]) (r : Fin r[U]) ↦
    sourceX₁ U ρ hρ (α, j₁) r * sourceY₁ U ρ hρ r (i₁, β) *
      (sourceX₂ U (β, i₂) l * sourceY₂ U l (j₂, α))
  change (∑ α, ∑ β, ∑ l, ∑ r, f α β l r) = _
  calc
    _ = ∑ α, ∑ l, ∑ β, ∑ r, f α β l r := by
      apply Finset.sum_congr rfl
      intro α _
      exact Finset.sum_comm
    _ = ∑ l, ∑ α, ∑ β, ∑ r, f α β l r := Finset.sum_comm
    _ = ∑ l, ∑ α, ∑ r, ∑ β, f α β l r := by
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro α _
      exact Finset.sum_comm
    _ = ∑ l, ∑ r, ∑ α, ∑ β, f α β l r := by
      apply Finset.sum_congr rfl
      intro l _
      exact Finset.sum_comm
    _ = ∑ lr : Fin ℓ[U] × Fin r[U], ∑ α, ∑ β, f α β lr.1 lr.2 := by
      rw [Fintype.sum_prod_type]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro lr _
      apply Finset.sum_congr rfl
      intro α _
      apply Finset.sum_congr rfl
      intro β _
      simp only [f]
      ring

/-- Entrywise two-site factorization through the two auxiliary mixed kernels.

Algebraic mixed-cut factorization; not the CPSV17/FBC25 source gates. -/
theorem mpo_two_pair_entry_eq_sourceY₁X₂_mul_sourceX₁Y₂_swap
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (i₁ i₂ j₁ j₂ : Fin d) :
    mpo U 2 ![i₁, i₂] ![j₁, j₂] =
      ∑ lr : Fin ℓ[U] × Fin r[U],
        sourceY₁X₂ U ρ hρ lr (i₁, i₂) *
          sourceX₁Y₂ U ρ hρ (j₁, j₂) (lr.2, lr.1) := by
  rw [mpo_apply, mpoMatrixEntry, evalWord_ofFn]
  simpa only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
    Matrix.mul_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
    Matrix.cons_val_fin_one] using
    trace_mul_eq_sourceY₁X₂_mul_sourceX₁Y₂_swap U ρ hρ i₁ i₂ j₁ j₂

/-- The exact two-site periodic MPO factorization through the auxiliary mixed kernels.

The two-site physical configurations are reindexed by `finTwoArrowEquiv`. The
columns of the auxiliary $X_1$--$Y_2$ kernel have order $r\times\ell$, so
`Equiv.prodComm` explicitly swaps them to the $\ell\times r$ order used by
the rows of the auxiliary $Y_1$--$X_2$ kernel.

Algebraic mixed-cut factorization; not the CPSV17/FBC25 source gates. -/
theorem mpo_two_reindex_eq_sourceY₁X₂_transpose_mul_sourceX₁Y₂_swap_transpose
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    Matrix.reindex (finTwoArrowEquiv (Fin d)) (finTwoArrowEquiv (Fin d))
        (mpo U 2) =
      (sourceY₁X₂ U ρ hρ)ᵀ *
        (Matrix.reindex (Equiv.refl (Fin d × Fin d))
          (Equiv.prodComm (Fin r[U]) (Fin ℓ[U]))
          (sourceX₁Y₂ U ρ hρ))ᵀ := by
  classical
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Equiv.refl_symm, Equiv.refl_apply, Equiv.prodComm_symm,
    Equiv.prodComm_apply, finTwoArrowEquiv_symm_apply]
  rw [mpo_two_pair_entry_eq_sourceY₁X₂_mul_sourceX₁Y₂_swap U ρ hρ i₁ i₂ j₁ j₂]
  apply Finset.sum_congr rfl
  rintro ⟨l, r⟩ _
  rfl

end MPOTensor
