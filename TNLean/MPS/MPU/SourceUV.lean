/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SimpleBlocking
import TNLean.MPS.MPU.SourceFactors

/-!
# Source-factor tensors for matrix product unitaries

This file defines the tensors $u$ and $v$ from arXiv:1703.09188, equations
`uuvv`--`uUnitary` (lines 521--554). The product-index orders are kept
explicit: $u : d^2 \to \ell \times r$ and $v : r \times \ell \to d^2$.
The two-site factorization therefore includes the paper's swap of the dotted
and solid source bonds rather than identifying the two product orders.
-/

open scoped Matrix BigOperators ComplexOrder
open Matrix

namespace MPOTensor

variable {d D : ℕ} (U : MPOTensor d D)

/-- The paper's source tensor $u : d^2 \to \ell\times r$.

The row order is `(left source, right source)` and the physical column order is
`(first ket site, second ket site)`. Its two triangles are $Y_1$ and $X_2$.

Source: arXiv:1703.09188, equation `uu` and Figure `II_umatrix.png`, lines
521--534. -/
noncomputable def sourceU (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    Matrix (Fin ℓ[U] × Fin r[U]) (Fin d × Fin d) ℂ :=
  fun (l, r) (i₁, i₂) ↦ ∑ β : Fin D,
    sourceY₁ U ρ hρ r (i₁, β) * sourceX₂ U (β, i₂) l

/-- The paper's source tensor $v : r\times\ell \to d^2$.

The physical row order is `(first bra site, second bra site)` and the column
order is `(right source, left source)`. Its two triangles are $X_1$ and $Y_2$.

Source: arXiv:1703.09188, equation `vdagger` and Figure `II_vmatrix.png`, lines
521--534. -/
noncomputable def sourceV (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    Matrix (Fin d × Fin d) (Fin r[U] × Fin ℓ[U]) ℂ :=
  fun (j₁, j₂) (r, l) ↦ ∑ α : Fin D,
    sourceX₁ U ρ hρ (α, j₁) r * sourceY₂ U l (j₂, α)

/-- Stable entry formula for $u$ in the exact solid/dotted leg order.

Source: arXiv:1703.09188, equation `uu`, lines 521--534. -/
@[simp] theorem sourceU_apply (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (l : Fin ℓ[U]) (r : Fin r[U]) (i₁ i₂ : Fin d) :
    sourceU U ρ hρ (l, r) (i₁, i₂) = ∑ β : Fin D,
      sourceY₁ U ρ hρ r (i₁, β) * sourceX₂ U (β, i₂) l := rfl

/-- Stable entry formula for $v$ in the exact dotted/solid leg order.

Source: arXiv:1703.09188, equation `vdagger`, lines 521--534. -/
@[simp] theorem sourceV_apply (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (j₁ j₂ : Fin d) (r : Fin r[U]) (l : Fin ℓ[U]) :
    sourceV U ρ hρ (j₁, j₂) (r, l) = ∑ α : Fin D,
      sourceX₁ U ρ hρ (α, j₁) r * sourceY₂ U l (j₂, α) := rfl

/-- Entry formula for the conjugate transpose of $u$.

Source: arXiv:1703.09188, equation `uUnitary`, lines 536--554. -/
@[simp] theorem sourceU_conjTranspose_apply
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (i₁ i₂ : Fin d) (l : Fin ℓ[U]) (r : Fin r[U]) :
    (sourceU U ρ hρ)ᴴ (i₁, i₂) (l, r) = star (∑ β : Fin D,
      sourceY₁ U ρ hρ r (i₁, β) * sourceX₂ U (β, i₂) l) := rfl

/-- Entry formula for the conjugate transpose of $v$.

Source: arXiv:1703.09188, equation `vdagger`, lines 521--534. -/
@[simp] theorem sourceV_conjTranspose_apply
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (r : Fin r[U]) (l : Fin ℓ[U]) (j₁ j₂ : Fin d) :
    (sourceV U ρ hρ)ᴴ (r, l) (j₁, j₂) = star (∑ α : Fin D,
      sourceX₁ U ρ hρ (α, j₁) r * sourceY₂ U l (j₂, α)) := rfl

/-- The traced product of two local letters factors through the source tensors.

Source: arXiv:1703.09188, equations `SVDforms2` and `uuvv`, lines 515--534. -/
theorem trace_mul_eq_sourceU_mul_sourceV_swap
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (i₁ i₂ j₁ j₂ : Fin d) :
    Matrix.trace (U i₁ j₁ * U i₂ j₂) =
      ∑ lr : Fin ℓ[U] × Fin r[U],
        sourceU U ρ hρ lr (i₁, i₂) * sourceV U ρ hρ (j₁, j₂) (lr.2, lr.1) := by
  classical
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, sourceU, sourceV,
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

/-- Entrywise two-site factorization in the paper's site and bond order.

Source: arXiv:1703.09188, equations `SVDforms2` and `uuvv`, lines 515--534. -/
theorem mpo_two_pair_entry_eq_sourceU_mul_sourceV_swap
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (i₁ i₂ j₁ j₂ : Fin d) :
    mpo U 2 ![i₁, i₂] ![j₁, j₂] =
      ∑ lr : Fin ℓ[U] × Fin r[U],
        sourceU U ρ hρ lr (i₁, i₂) * sourceV U ρ hρ (j₁, j₂) (lr.2, lr.1) := by
  rw [mpo_apply, mpoMatrixEntry, evalWord_ofFn]
  simpa only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
    Matrix.mul_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
    Matrix.cons_val_fin_one] using
    trace_mul_eq_sourceU_mul_sourceV_swap U ρ hρ i₁ i₂ j₁ j₂

/-- The exact two-site periodic MPO factorization through $u$ and $v$.

The two-site physical configurations are reindexed by `finTwoArrowEquiv`. The
columns of $v$ have order $r\times\ell$, so `Equiv.prodComm` explicitly swaps
them to the $\ell\times r$ order used by the rows of $u$. This is the one-site
translation/bond swap visible in the paper figures.

Source: arXiv:1703.09188, equations `SVDforms2` and `uuvv`, lines 515--534. -/
theorem mpo_two_reindex_eq_sourceU_transpose_mul_sourceV_swap_transpose
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    Matrix.reindex (finTwoArrowEquiv (Fin d)) (finTwoArrowEquiv (Fin d)) (mpo U 2) =
      (sourceU U ρ hρ)ᵀ *
        (Matrix.reindex (Equiv.refl (Fin d × Fin d))
          (Equiv.prodComm (Fin r[U]) (Fin ℓ[U])) (sourceV U ρ hρ))ᵀ := by
  classical
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Equiv.refl_symm, Equiv.refl_apply, Equiv.prodComm_symm,
    Equiv.prodComm_apply, finTwoArrowEquiv_symm_apply]
  rw [mpo_two_pair_entry_eq_sourceU_mul_sourceV_swap U ρ hρ i₁ i₂ j₁ j₂]
  apply Finset.sum_congr rfl
  rintro ⟨l, r⟩ _
  rfl

end MPOTensor
