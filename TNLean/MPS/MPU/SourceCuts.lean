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
Section III, definition `defnrl`, lines 450–477.

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

We set $r := \operatorname{rank} {\cal M}_1$ (the **right rank**) and
$\ell := \operatorname{rank} {\cal M}_2$ (the **left rank**), as in
definition `defnrl` and lines 697–704 of the paper.

## Main definitions

* `MPOTensor.sourceCutM₁`, `MPOTensor.sourceCutM₂`: the two source matrices
  with product-index rows and columns.
* `MPOTensor.sourceCutM₁Fin`, `MPOTensor.sourceCutM₂Fin`: reindexed versions
  `Matrix (Fin (D * d)) (Fin (d * D)) ℂ`.
* `MPOTensor.rightRank` (`r`), `MPOTensor.leftRank` (`ℓ`): the ranks.

## Main results

* `rightRank_bound`, `leftRank_bound`: rank bounds
  $r \le \min(Dd, dD) = Dd$ and similarly $\ell \le Dd$.
* `sourceCut_entry` lemmas: `[simp]` entry formulas for both cuts and both
  index forms.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1703.09188,
  Section III, definition `defnrl`, lines 450–477 and 697–704.
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

/-! ### Right and left ranks $r$ and $\ell$ (definition `defnrl`, lines 697–704) -/

/-- The **right rank** $r = \operatorname{rank} {\cal M}_1$, as in
arXiv:1703.09188, definition `defnrl` (lines 450–477) and lines 697–704. -/
noncomputable def rightRank : ℕ := (sourceCutM₁ U).rank

/-- The **left rank** $\ell = \operatorname{rank} {\cal M}_2$, as in
arXiv:1703.09188, definition `defnrl` (lines 450–477) and lines 697–704. -/
noncomputable def leftRank : ℕ := (sourceCutM₂ U).rank

-- Notation corresponding to the paper's `r` and `ℓ`
@[inherit_doc rightRank] scoped notation "r[" U "]" => MPOTensor.rightRank U
@[inherit_doc leftRank] scoped notation "ℓ[" U "]" => MPOTensor.leftRank U

lemma rightRank_eq : r[U] = (sourceCutM₁ U).rank := rfl

lemma leftRank_eq : ℓ[U] = (sourceCutM₂ U).rank := rfl

/-! ### Rank bounds -/

/-- The right rank $r = \operatorname{rank} {\cal M}_1 \le D d$,
since ${\cal M}_1$ has $Dd$ rows and $dD$ columns. -/
theorem rightRank_bound : (sourceCutM₁ U).rank ≤ D * d := by
  refine (Matrix.rank_le_card_width (sourceCutM₁ U)).trans ?_
  simp [Fintype.card_fin, mul_comm]

/-- The left rank $\ell = \operatorname{rank} {\cal M}_2 \le D d$,
since ${\cal M}_2$ also has $Dd$ rows and $dD$ columns. -/
theorem leftRank_bound : (sourceCutM₂ U).rank ≤ D * d := by
  refine (Matrix.rank_le_card_width (sourceCutM₂ U)).trans ?_
  simp [Fintype.card_fin, mul_comm]

end MPOTensor
