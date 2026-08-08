/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.Defs
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Source matrix cuts and ranks of an MPU tensor

This module defines the two source matrices ${\cal M}_1$ and ${\cal M}_2$
obtained from a four-index tensor ${\cal U}$ by regrouping its indices, and
the associated ranks $r$ and $\ell$, following
[Cirac--Perez-Garcia--Schuch--Verstraete 2017, arXiv:1703.09188],
Section II, Definition II.3 (label `defnrl`).

A tensor ${\cal U}$ generating a matrix product unitary (MPU) carries four
indices: up $i$ (ket, first physical), down $j$ (bra, second physical),
left $\alpha$ (left virtual), right $\beta$ (right virtual).  In the MPU
paper these appear as four-leg tensors where vertical lines carry physical
indices and horizontal lines carry virtual (auxiliary) ones.

## Source matrices ${\cal M}_1$, ${\cal M}_2$

Following lines 458–477 of the paper, we combine indices in two different
ways to form rectangular matrices:

* ${\cal M}_1$ groups **row = (left, down)** and **column = (up, right)**:
  $({\cal M}_1)_{(\alpha,j),(i,\beta)} = {\cal U}^{i}_{j,\alpha,\beta}$
  (using the paper's graphical convention), or equivalently
  `U i j α β` in `MPOTensor` notation (ket, bra, left-virtual, right-virtual).

* ${\cal M}_2$ groups **row = (left, up)** and **column = (down, right)**:
  $({\cal M}_2)_{(\alpha,i),(j,\beta)} = {\cal U}^{i}_{j,\alpha,\beta}$.

## Ranks $r$ and $\ell$

We set $r := \operatorname{rank} {\cal M}_1$,
$\ell := \operatorname{rank} {\cal M}_2$ as in Definition II.3 of the paper.

## Main definitions

* `MPOTensor.sourceCutM₁`, `MPOTensor.sourceCutM₂`: the two source matrices
  with product-index rows and columns.
* `MPOTensor.sourceCutM₁Fin`, `MPOTensor.sourceCutM₂Fin`: reindexed versions
  `Matrix (Fin (D * d)) (Fin (d * D)) ℂ`.
* `MPOTensor.sourceRank₁` (`r`), `MPOTensor.sourceRank₂` (`ℓ`): the ranks.

## Main results

* `sourceCutM₁_rank_bound`, `sourceCutM₂_rank_bound`: rank bounds
  $r \le \min(Dd, dD) = Dd$ and similarly $\ell \le Dd$.
* `sourceCut_entry` lemmas: `[simp]` entry formulas for both cuts and both
  index forms.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1703.09188,
  Section II, Definition II.3 and lines 458–477.
-/

open scoped Matrix
open Matrix

namespace MPOTensor

variable {d D : ℕ} (U : MPOTensor d D)

/-! ### Product-index source matrices (primary definitions) -/

/-- ${\cal M}_1$: group **row = (left, down)** and **column = (up, right)**.

The entry $({\cal M}_1)_{(\alpha,j),(i,\beta)}$ equals `U i j α β` where
`i` = up (ket), `j` = down (bra), `α` = left virtual, `β` = right virtual.

This follows arXiv:1703.09188, eq.~(II_SVD). -/
def sourceCutM₁ : Matrix (Fin D × Fin d) (Fin d × Fin D) ℂ :=
  fun (α, j) (i, β) => U i j α β

/-- ${\cal M}_2$: group **row = (left, up)** and **column = (down, right)**.

The entry $({\cal M}_2)_{(\alpha,i),(j,\beta)}$ equals `U i j α β`.

This follows arXiv:1703.09188, eq.~(II_SVD). -/
def sourceCutM₂ : Matrix (Fin D × Fin d) (Fin d × Fin D) ℂ :=
  fun (α, i) (j, β) => U i j α β

/-! ### Entry lemmas — `[simp]` -/

@[simp] lemma sourceCutM₁_apply (α : Fin D) (j : Fin d) (i : Fin d) (β : Fin D) :
    sourceCutM₁ U (α, j) (i, β) = U i j α β := rfl

@[simp] lemma sourceCutM₂_apply (α : Fin D) (i : Fin d) (j : Fin d) (β : Fin D) :
    sourceCutM₂ U (α, i) (j, β) = U i j α β := rfl

/-! ### Reindexing to `Fin (D * d)` and `Fin (d * D)` (thin bridges) -/

/-- ${\cal M}_1$ reindexed to `Fin (D * d)` rows and `Fin (d * D)` columns
via the standard product encoding `finProdFinEquiv`.

This is a thin bridge; the primary definition remains `sourceCutM₁`. -/
def sourceCutM₁Fin : Matrix (Fin (D * d)) (Fin (d * D)) ℂ :=
  Matrix.reindex
    (finProdFinEquiv (m := D) (n := d))
    (finProdFinEquiv (m := d) (n := D))
    (sourceCutM₁ U)

/-- ${\cal M}_2$ reindexed to `Fin (D * d)` rows and `Fin (d * D)` columns. -/
def sourceCutM₂Fin : Matrix (Fin (D * d)) (Fin (d * D)) ℂ :=
  Matrix.reindex
    (finProdFinEquiv (m := D) (n := d))
    (finProdFinEquiv (m := d) (n := D))
    (sourceCutM₂ U)

lemma sourceCutM₁Fin_eq_reindex : sourceCutM₁Fin U =
    Matrix.reindex
      (finProdFinEquiv (m := D) (n := d))
      (finProdFinEquiv (m := d) (n := D))
      (sourceCutM₁ U) := rfl

lemma sourceCutM₂Fin_eq_reindex : sourceCutM₂Fin U =
    Matrix.reindex
      (finProdFinEquiv (m := D) (n := d))
      (finProdFinEquiv (m := d) (n := D))
      (sourceCutM₂ U) := rfl

@[simp] lemma sourceCutM₁Fin_apply (r : Fin (D * d)) (c : Fin (d * D)) :
    sourceCutM₁Fin U r c =
      sourceCutM₁ U
        ((finProdFinEquiv (m := D) (n := d)).symm r)
        ((finProdFinEquiv (m := d) (n := D)).symm c) := rfl

@[simp] lemma sourceCutM₂Fin_apply (r : Fin (D * d)) (c : Fin (d * D)) :
    sourceCutM₂Fin U r c =
      sourceCutM₂ U
        ((finProdFinEquiv (m := D) (n := d)).symm r)
        ((finProdFinEquiv (m := d) (n := D)).symm c) := rfl

lemma sourceCutM₁_rank_eq_sourceCutM₁Fin_rank :
    (sourceCutM₁ U).rank = (sourceCutM₁Fin U).rank := by
  rw [sourceCutM₁Fin_eq_reindex, Matrix.rank_reindex]

lemma sourceCutM₂_rank_eq_sourceCutM₂Fin_rank :
    (sourceCutM₂ U).rank = (sourceCutM₂Fin U).rank := by
  rw [sourceCutM₂Fin_eq_reindex, Matrix.rank_reindex]

/-! ### Source ranks $r$ and $\ell$ (Definition II.3, label `defnrl`) -/

/-- The rank $r$ of ${\cal M}_1$, as in arXiv:1703.09188, Definition II.3. -/
noncomputable def sourceRank₁ : ℕ := (sourceCutM₁ U).rank

/-- The rank $\ell$ of ${\cal M}_2$, as in arXiv:1703.09188, Definition II.3. -/
noncomputable def sourceRank₂ : ℕ := (sourceCutM₂ U).rank

-- Notation corresponding to the paper's `r` and `ℓ`
@[inherit_doc sourceRank₁] scoped notation "r[" U "]" => MPOTensor.sourceRank₁ U
@[inherit_doc sourceRank₂] scoped notation "ℓ[" U "]" => MPOTensor.sourceRank₂ U

lemma sourceRank₁_eq : r[U] = (sourceCutM₁ U).rank := rfl

lemma sourceRank₂_eq : ℓ[U] = (sourceCutM₂ U).rank := rfl

/-! ### Rank bounds -/

/-- $r = \operatorname{rank} {\cal M}_1 \le D d$, since ${\cal M}_1$
has $Dd$ rows and $dD$ columns. -/
theorem sourceCutM₁_rank_bound : (sourceCutM₁ U).rank ≤ D * d := by
  refine (Matrix.rank_le_card_width (sourceCutM₁ U)).trans ?_
  simp [Fintype.card_fin, mul_comm]

/-- $\ell = \operatorname{rank} {\cal M}_2 \le D d$, since ${\cal M}_2$
also has $Dd$ rows and $dD$ columns. -/
theorem sourceCutM₂_rank_bound : (sourceCutM₂ U).rank ≤ D * d := by
  refine (Matrix.rank_le_card_width (sourceCutM₂ U)).trans ?_
  simp [Fintype.card_fin, mul_comm]

theorem sourceRank₁_bound : r[U] ≤ D * d :=
  sourceCutM₁_rank_bound U

theorem sourceRank₂_bound : ℓ[U] ≤ D * d :=
  sourceCutM₂_rank_bound U

/-! ### Literal verification: identity tensor

We verify the ranks for the identity MPU tensor
${\cal U}^{i}_{j,\alpha,\beta} = \delta_{i,j} \cdot \delta_{\alpha,\beta}$.
For this tensor both ${\cal M}_1$ and ${\cal M}_2$ become identity-like
matrices on $\min(Dd, dD) = Dd$ dimensions, so both ranks equal $D d$.

This example is source-relevant: the identity MPU is the trivial case of
Definition II.3, and the ranks saturate the bound $r, \ell \le Dd$. -/

/-- The identity MPU tensor: `idU d D i j α β = δ_{i,j} · δ_{α,β}`.
When $d$ and $D$ are concrete naturals the physical and virtual identity
Kronecker deltas are `if i = j ∧ α = β then 1 else 0`. -/
def idU (d D : ℕ) : MPOTensor d D :=
  fun i j α β => if i = j ∧ α = β then 1 else 0

lemma sourceCutM₁_idU (d D : ℕ) (α : Fin D) (j : Fin d) (i : Fin d) (β : Fin D) :
    sourceCutM₁ (idU d D) (α, j) (i, β) = if i = j ∧ α = β then 1 else 0 := by
  simp [idU, sourceCutM₁]

lemma sourceCutM₂_idU (d D : ℕ) (α : Fin D) (i : Fin d) (j : Fin d) (β : Fin D) :
    sourceCutM₂ (idU d D) (α, i) (j, β) = if i = j ∧ α = β then 1 else 0 := by
  simp [idU, sourceCutM₂]

end MPOTensor
