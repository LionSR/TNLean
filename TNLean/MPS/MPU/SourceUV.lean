/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SourceFactors

/-!
# Paper source gates

This file defines the paper gates $u=Y_2\mathbin{-}Y_1$ and
$v=X_1\mathbin{-}X_2$ from arXiv:1703.09188, equations `uuvv`, `uu`, and
`vdagger` (lines 532--543), with the triangle assignment made explicit in
arXiv:2502.20257, equation `eq:uv` (lines 704--760).

Both gates contract two factors taken from the same side of the source cuts,
as the source prints them; no other pairing of the four source factors is
defined here.
-/

open scoped Matrix BigOperators ComplexOrder
open Matrix

namespace MPOTensor

variable {d D : ℕ} (U : MPOTensor d D)

namespace SourceFactors

/-- The paper gate $u : d^2 \to \ell\times r$ for supplied source factors.
Its two triangles are $Y_2$ and $Y_1$, in that order.

Source: CPSV17 equations `uuvv` and `uu` (lines 532--543), and FBC25 equation
`eq:uv` (lines 704--760). -/
def sourceU {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ) :
    Matrix (Fin ℓ[U] × Fin r[U]) (Fin d × Fin d) ℂ :=
  fun (l, r) (i₁, i₂) ↦ ∑ β : Fin D, S.Y₂ l (i₁, β) * S.Y₁ r (β, i₂)

/-- The paper gate $v : r\times\ell \to d^2$ for supplied source factors.
Its two triangles are $X_1$ and $X_2$, in that order.

Source: CPSV17 equations `uuvv` and `vdagger` (lines 532--543), and FBC25
equation `eq:uv` (lines 704--760). -/
def sourceV {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ) :
    Matrix (Fin d × Fin d) (Fin r[U] × Fin ℓ[U]) ℂ :=
  fun (j₁, j₂) (r, l) ↦ ∑ α : Fin D, S.X₁ (j₁, α) r * S.X₂ (α, j₂) l

/-- Literal entry formula for the paper gate $u=Y_2\mathbin{-}Y_1$.

Source: CPSV17 equation `uu` (lines 532--543) and FBC25 equation `eq:uv`
(lines 704--760). -/
@[simp] theorem sourceU_apply {ρ : Matrix (Fin D) (Fin D) ℂ}
    (S : SourceFactors U ρ) (l : Fin ℓ[U]) (r : Fin r[U]) (i₁ i₂ : Fin d) :
    sourceU U S (l, r) (i₁, i₂) =
      ∑ β : Fin D, S.Y₂ l (i₁, β) * S.Y₁ r (β, i₂) := rfl

/-- Literal entry formula for the paper gate $v=X_1\mathbin{-}X_2$.

Source: CPSV17 equation `vdagger` (lines 532--543) and FBC25 equation `eq:uv`
(lines 704--760). -/
@[simp] theorem sourceV_apply {ρ : Matrix (Fin D) (Fin D) ℂ}
    (S : SourceFactors U ρ) (j₁ j₂ : Fin d) (r : Fin r[U]) (l : Fin ℓ[U]) :
    sourceV U S (j₁, j₂) (r, l) =
      ∑ α : Fin D, S.X₁ (j₁, α) r * S.X₂ (α, j₂) l := rfl

/-- Entry form of the first source-cut factorization for supplied factors.

Source: arXiv:1703.09188, equations `X1Y1` and `SVDforms2`, lines 508--528. -/
@[simp] theorem X₁_mul_Y₁_apply {ρ : Matrix (Fin D) (Fin D) ℂ}
    (S : SourceFactors U ρ) (i : Fin d) (β α : Fin D) (j : Fin d) :
    (S.X₁ * S.Y₁) (i, β) (α, j) = U i j α β := by
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
      sourceY₂ U l (i₁, β) * sourceY₁ U ρ hρ r (β, i₂) := rfl

/-- Conjugate-transpose entry formula for the paper gate $u=Y_2\mathbin{-}Y_1$.

Source: CPSV17 equation `uu` (lines 532--543) and FBC25 equation `eq:uv`
(lines 704--760). -/
@[simp] theorem sourceU_conjTranspose_apply
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (i₁ i₂ : Fin d) (l : Fin ℓ[U]) (r : Fin r[U]) :
    (sourceU U ρ hρ)ᴴ (i₁, i₂) (l, r) = star (∑ β : Fin D,
      sourceY₂ U l (i₁, β) * sourceY₁ U ρ hρ r (β, i₂)) := rfl

/-- Literal compact-SVD entry formula for the paper gate $v=X_1\mathbin{-}X_2$.

Source: CPSV17 equation `vdagger` (lines 532--543) and FBC25 equation `eq:uv`
(lines 704--760). -/
@[simp] theorem sourceV_apply (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (j₁ j₂ : Fin d) (r : Fin r[U]) (l : Fin ℓ[U]) :
    sourceV U ρ hρ (j₁, j₂) (r, l) = ∑ α : Fin D,
      sourceX₁ U ρ hρ (j₁, α) r * sourceX₂ U (α, j₂) l := rfl

/-- Conjugate-transpose entry formula for the paper gate $v=X_1\mathbin{-}X_2$.

Source: CPSV17 equation `vdagger` (lines 532--543) and FBC25 equation `eq:uv`
(lines 704--760). -/
@[simp] theorem sourceV_conjTranspose_apply
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (r : Fin r[U]) (l : Fin ℓ[U]) (j₁ j₂ : Fin d) :
    (sourceV U ρ hρ)ᴴ (r, l) (j₁, j₂) = star (∑ α : Fin D,
      sourceX₁ U ρ hρ (j₁, α) r * sourceX₂ U (α, j₂) l) := rfl

/-- The traced product of two local letters factors through the paper gates $v$ and $u$.

This is the coordinate contraction obtained from the two graphical
factorizations in CPSV17 `SVDforms2` and the gate definitions `uuvv`
(lines 525--543). The reversed pair `(j₂,j₁)` records the spatial order of
the $Y_2$--$Y_1$ contraction around the periodic trace. -/
theorem trace_mul_eq_sourceV_mul_sourceU_swap
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (i₁ i₂ j₁ j₂ : Fin d) :
    Matrix.trace (U i₁ j₁ * U i₂ j₂) =
      ∑ lr : Fin ℓ[U] × Fin r[U],
        sourceV U ρ hρ (i₁, i₂) (lr.2, lr.1) *
          sourceU U ρ hρ lr (j₂, j₁) := by
  classical
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  have h₁ (α β : Fin D) :
      U i₁ j₁ α β = ∑ r, sourceX₁ U ρ hρ (i₁, β) r *
        sourceY₁ U ρ hρ r (α, j₁) := by
    simpa only [Matrix.mul_apply] using
      (sourceX₁_mul_sourceY₁_apply U ρ hρ i₁ β α j₁).symm
  have h₂ (β α : Fin D) :
      U i₂ j₂ β α = ∑ l, sourceX₂ U (β, i₂) l * sourceY₂ U l (j₂, α) := by
    simpa only [Matrix.mul_apply] using
      (sourceX₂_mul_sourceY₂_apply U β i₂ j₂ α).symm
  simp_rw [h₁, h₂]
  simp only [Finset.mul_sum, Finset.sum_mul]
  let f := fun (α β : Fin D) (l : Fin ℓ[U]) (r : Fin r[U]) ↦
    sourceX₁ U ρ hρ (i₁, β) r * sourceY₁ U ρ hρ r (α, j₁) *
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
      refine Finset.sum_congr rfl fun lr _ => ?_
      obtain ⟨l, r⟩ := lr
      rw [sourceV_apply, sourceU_apply, Finset.sum_mul_sum, Finset.sum_comm]
      refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
      simp only [f]
      ring

/-- Entrywise two-site factorization through the paper gates $v$ and $u$.

Source: CPSV17 `SVDforms2` and `uuvv` (lines 525--543). -/
theorem mpo_two_pair_entry_eq_sourceV_mul_sourceU_swap
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (i₁ i₂ j₁ j₂ : Fin d) :
    mpo U 2 ![i₁, i₂] ![j₁, j₂] =
      ∑ lr : Fin ℓ[U] × Fin r[U],
        sourceV U ρ hρ (i₁, i₂) (lr.2, lr.1) *
          sourceU U ρ hρ lr (j₂, j₁) := by
  rw [mpo_apply, mpoMatrixEntry, evalWord_ofFn]
  simpa only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
    Matrix.mul_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
    Matrix.cons_val_fin_one] using
    trace_mul_eq_sourceV_mul_sourceU_swap U ρ hρ i₁ i₂ j₁ j₂

/-- The exact two-site periodic MPO factorization through the paper gates $v$ and $u$.

The two-site physical configurations are reindexed by `finTwoArrowEquiv`.
The first `Equiv.prodComm` changes the rows of $u$ from $\ell\times r$ to
$r\times\ell$, as required by the columns of $v$; the second reverses the
two physical input coordinates.

Source: CPSV17 `SVDforms2` and `uuvv` (lines 525--543). -/
theorem mpo_two_reindex_eq_sourceV_mul_sourceU_swap
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    Matrix.reindex (finTwoArrowEquiv (Fin d)) (finTwoArrowEquiv (Fin d))
        (mpo U 2) =
      sourceV U ρ hρ *
        Matrix.reindex (Equiv.prodComm (Fin ℓ[U]) (Fin r[U]))
          (Equiv.prodComm (Fin d) (Fin d)) (sourceU U ρ hρ) := by
  classical
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.mul_apply,
    Equiv.prodComm_symm, Equiv.prodComm_apply, finTwoArrowEquiv_symm_apply]
  rw [mpo_two_pair_entry_eq_sourceV_mul_sourceU_swap U ρ hρ i₁ i₂ j₁ j₂]
  exact Fintype.sum_equiv (Equiv.prodComm (Fin ℓ[U]) (Fin r[U])) _ _ fun lr => rfl

end MPOTensor
