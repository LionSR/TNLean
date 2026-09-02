/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalAdjoint
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

* ${\cal M}_1$ groups **row = (up, right)** and **column = (left, down)**:
  $({\cal M}_1)_{(i,\beta),(\alpha,j)} = {\cal U}^{i}_{j,\alpha,\beta}$.
  This orientation is fixed by the paper's factorization
  ${\cal M}_1=X_1Y_1$: in Figures `II_X1Y1.png` and `II_SVDforms2.png`,
  $X_1$ carries the up and right legs, whereas $Y_1$ carries the left and
  down legs.

* ${\cal M}_2$ groups **row = (left, up)** and **column = (down, right)**:
  $({\cal M}_2)_{(\alpha,i),(j,\beta)} = {\cal U}^{i}_{j,\alpha,\beta}$.

**Local fix (first source-cut orientation):** An earlier TNLean definition
transposed ${\cal M}_1$, placing $(\alpha,j)$ on rows and $(i,\beta)$ on
columns. The corrected definition follows CPSV17 `II_SVD` and the factors in
`II_X1Y1.png` and `II_SVDforms2.png`, with $(i,\beta)$ on rows and
$(\alpha,j)$ on columns. This correction is documented in
`docs/paper-gaps/mpu_source_cut_orientation.tex`.

## Ranks $r$ and $\ell$

We set $r := \operatorname{rank} {\cal M}_1$ (the **right rank**) and
$\ell := \operatorname{rank} {\cal M}_2$ (the **left rank**), as in
definition `defnrl` and lines 697–704 of the paper.

## Main definitions

* `MPOTensor.sourceCutM₁`, `MPOTensor.sourceCutM₂`: the two source matrices
  with product-index rows and columns.
* `MPOTensor.sourceCutM₁Fin`, `MPOTensor.sourceCutM₂Fin`: reindexed versions
  of the product-index source matrices.
* `MPOTensor.rightRank` (`r`), `MPOTensor.leftRank` (`ℓ`): the ranks.

## Main results

* `rightRank_bound`, `leftRank_bound`: rank bounds
  $r \le \min(Dd, dD) = Dd$ and similarly $\ell \le Dd$.
* `sourceCutM₁_reindexPhysical`, `sourceCutM₂_reindexPhysical`: physical reindexing
  formulas for the two cuts.
* `sourceCutM₁_physicalAdjointTensor`, `sourceCutM₂_physicalAdjointTensor`:
  physical adjunction exchanges the two cuts by conjugate transpose.
* `rightRank_physicalAdjointTensor`, `leftRank_physicalAdjointTensor`:
  physical adjunction exchanges the two source ranks.
* `rightRank_reindexPhysical`, `leftRank_reindexPhysical`: invariance of both ranks
  under bijective physical reindexing.
* `sourceCutM₁_apply`, `sourceCutM₂_apply`, `sourceCutM₁Fin_apply`,
  `sourceCutM₂Fin_apply`: `[simp]` entry formulas for both cuts and both index forms.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1703.09188,
  Section III, definition `defnrl`, lines 450–477 and 697–704.
-/

open scoped ComplexOrder Matrix

namespace MPOTensor

variable {d D : ℕ} (U : MPOTensor d D)

/-! ### Product-index source matrices (primary definitions) -/

/-- ${\cal M}_1$: group **row = (up, right)** and **column = (left, down)**.

The entry $({\cal M}_1)_{(i,\beta),(\alpha,j)}$ equals `U i j α β`.  The
row/column orientation is determined by arXiv:1703.09188, Figures
`II_X1Y1.png` and `II_SVDforms2.png`: the row factor $X_1$ carries the up
and right legs, and the column factor $Y_1$ carries the left and down legs. -/
def sourceCutM₁ : Matrix (Fin d × Fin D) (Fin D × Fin d) ℂ :=
  fun (i, β) (α, j) => U i j α β

/-- ${\cal M}_2$: group **row = (left, up)** and **column = (down, right)**.

The entry $({\cal M}_2)_{(\alpha,i),(j,\beta)}$ equals `U i j α β`.

This follows arXiv:1703.09188, eq.~(II_SVD). -/
def sourceCutM₂ : Matrix (Fin D × Fin d) (Fin d × Fin D) ℂ :=
  fun (α, i) (j, β) => U i j α β

/-! ### Entry lemmas — `[simp]` -/

/-- Entry formula for the first source cut in its physical--virtual row orientation.

Source: CPSV17 source cut `II_SVD`, lines 458--477, and the factor diagrams
`X1Y1` and `SVDforms2`, lines 508--530. -/
@[simp] lemma sourceCutM₁_apply (i : Fin d) (β : Fin D) (α : Fin D) (j : Fin d) :
    sourceCutM₁ U (i, β) (α, j) = U i j α β := rfl

@[simp] lemma sourceCutM₂_apply (α : Fin D) (i : Fin d) (j : Fin d) (β : Fin D) :
    sourceCutM₂ U (α, i) (j, β) = U i j α β := rfl

/-- Physical adjunction exchanges the first source cut with the adjoint of the second cut:
$$M_1(U^\sharp)=M_2(U)^*.$$

The source cuts follow arXiv:1703.09188, lines 450–506. The local physical-adjoint
operation follows arXiv:1606.00608, Appendix C.2, lines 1634–1689; arXiv:1703.09188,
lines 1201–1207 use the resulting adjoint family to reverse the index. -/
theorem sourceCutM₁_physicalAdjointTensor :
    sourceCutM₁ (physicalAdjointTensor U) = (sourceCutM₂ U)ᴴ := by
  ext row col
  rcases row with ⟨i, β⟩
  rcases col with ⟨α, j⟩
  rfl

/-- Physical adjunction exchanges the second source cut with the adjoint of the first cut:
$$M_2(U^\sharp)=M_1(U)^*.$$

The source cuts follow arXiv:1703.09188, lines 450–506. The local physical-adjoint
operation follows arXiv:1606.00608, Appendix C.2, lines 1634–1689; arXiv:1703.09188,
lines 1201–1207 use the resulting adjoint family to reverse the index. -/
theorem sourceCutM₂_physicalAdjointTensor :
    sourceCutM₂ (physicalAdjointTensor U) = (sourceCutM₁ U)ᴴ := by
  ext row col
  rcases row with ⟨α, i⟩
  rcases col with ⟨j, β⟩
  rfl

/-- Physical reindexing acts on the up leg of each row and the down leg of
each column of the first source cut.

Source: arXiv:1703.09188, proof of Theorem `IndexTh` (ii), lines 824--847. -/
theorem sourceCutM₁_reindexPhysical {d' : ℕ} (e : Fin d' ≃ Fin d) :
    sourceCutM₁ (reindexPhysical e U) =
      Matrix.reindex (Equiv.prodCongr e.symm (Equiv.refl (Fin D)))
        (Equiv.prodCongr (Equiv.refl (Fin D)) e.symm) (sourceCutM₁ U) := by
  ext row col
  rcases row with ⟨i, β⟩
  rcases col with ⟨α, j⟩
  simp [sourceCutM₁, reindexPhysical, Matrix.reindex_apply]

/-- Physical reindexing acts on the up leg of each row and the down leg of
each column of the second source cut.

Source: arXiv:1703.09188, proof of Theorem `IndexTh` (ii), lines 824--847. -/
theorem sourceCutM₂_reindexPhysical {d' : ℕ} (e : Fin d' ≃ Fin d) :
    sourceCutM₂ (reindexPhysical e U) =
      Matrix.reindex (Equiv.prodCongr (Equiv.refl (Fin D)) e.symm)
        (Equiv.prodCongr e.symm (Equiv.refl (Fin D))) (sourceCutM₂ U) := by
  ext row col
  rcases row with ⟨α, i⟩
  rcases col with ⟨j, β⟩
  simp [sourceCutM₂, reindexPhysical, Matrix.reindex_apply]

/-! ### Reindexing to finite intervals -/

/-- ${\cal M}_1$ reindexed to `Fin (d * D)` rows and `Fin (D * d)` columns
via the standard product encoding `finProdFinEquiv`.

This is a reindexed formulation; the primary definition remains `sourceCutM₁`. -/
def sourceCutM₁Fin : Matrix (Fin (d * D)) (Fin (D * d)) ℂ :=
  Matrix.reindex
    (finProdFinEquiv (m := d) (n := D))
    (finProdFinEquiv (m := D) (n := d))
    (sourceCutM₁ U)

/-- ${\cal M}_2$ reindexed to `Fin (D * d)` rows and `Fin (d * D)` columns. -/
def sourceCutM₂Fin : Matrix (Fin (D * d)) (Fin (d * D)) ℂ :=
  Matrix.reindex
    (finProdFinEquiv (m := D) (n := d))
    (finProdFinEquiv (m := d) (n := D))
    (sourceCutM₂ U)

lemma sourceCutM₁Fin_eq_reindex : sourceCutM₁Fin U =
    Matrix.reindex
      (finProdFinEquiv (m := d) (n := D))
      (finProdFinEquiv (m := D) (n := d))
      (sourceCutM₁ U) := rfl

lemma sourceCutM₂Fin_eq_reindex : sourceCutM₂Fin U =
    Matrix.reindex
      (finProdFinEquiv (m := D) (n := d))
      (finProdFinEquiv (m := d) (n := D))
      (sourceCutM₂ U) := rfl

@[simp] lemma sourceCutM₁Fin_apply (r : Fin (d * D)) (c : Fin (D * d)) :
    sourceCutM₁Fin U r c =
      sourceCutM₁ U
        ((finProdFinEquiv (m := d) (n := D)).symm r)
        ((finProdFinEquiv (m := D) (n := d)).symm c) := rfl

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

/-- Physical adjunction exchanges the right source rank with the left source rank:
$$r[U^\sharp]=\ell[U].$$

This is the raw source-rank identity underlying the sign reversal of the MPU index under
adjunction; it does not choose or compare standard-form factors.

Source: arXiv:1703.09188, definition `defnrl` and lines 1196–1207. -/
theorem rightRank_physicalAdjointTensor : r[physicalAdjointTensor U] = ℓ[U] := by
  rw [rightRank, sourceCutM₁_physicalAdjointTensor]
  rw [Matrix.rank_conjTranspose]
  rfl

/-- Physical adjunction exchanges the left source rank with the right source rank:
$$\ell[U^\sharp]=r[U].$$

Source: arXiv:1703.09188, definition `defnrl` and lines 1196–1207. -/
theorem leftRank_physicalAdjointTensor : ℓ[physicalAdjointTensor U] = r[U] := by
  rw [leftRank, sourceCutM₂_physicalAdjointTensor]
  rw [Matrix.rank_conjTranspose]
  rfl

/-- Bijective physical reindexing preserves the right source rank.

Source: arXiv:1703.09188, proof of Theorem `IndexTh` (ii), lines 824--847. -/
theorem rightRank_reindexPhysical {d' : ℕ} (e : Fin d' ≃ Fin d) :
    r[reindexPhysical e U] = r[U] := by
  rw [rightRank, sourceCutM₁_reindexPhysical, Matrix.rank_reindex]
  rfl

/-- Bijective physical reindexing preserves the left source rank.

Source: arXiv:1703.09188, proof of Theorem `IndexTh` (ii), lines 824--847. -/
theorem leftRank_reindexPhysical {d' : ℕ} (e : Fin d' ≃ Fin d) :
    ℓ[reindexPhysical e U] = ℓ[U] := by
  rw [leftRank, sourceCutM₂_reindexPhysical, Matrix.rank_reindex]
  rfl

/-! ### Rank bounds -/

/-- The right rank $r = \operatorname{rank} {\cal M}_1 \le D d$,
since ${\cal M}_1$ has $dD$ columns. -/
theorem rightRank_bound : r[U] ≤ D * d := by
  rw [rightRank]
  refine (Matrix.rank_le_card_width (sourceCutM₁ U)).trans ?_
  simp [Fintype.card_fin, mul_comm]

/-- The left rank $\ell = \operatorname{rank} {\cal M}_2 \le D d$,
since ${\cal M}_2$ also has $dD$ columns. -/
theorem leftRank_bound : ℓ[U] ≤ D * d := by
  rw [leftRank]
  refine (Matrix.rank_le_card_width (sourceCutM₂ U)).trans ?_
  simp [Fintype.card_fin, mul_comm]

end MPOTensor
