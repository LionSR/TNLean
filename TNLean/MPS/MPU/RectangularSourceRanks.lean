/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Kronecker
import TNLean.MPS.Core.ReductionBlocking
import TNLean.MPS.MPDO.PhysicalBlocking
import TNLean.MPS.MPU.SourceCuts

/-!
# Source ranks under rectangular reduction

Let $U$ have bond dimension $D$, and let $A$ and $B$ be rectangular matrices
of sizes $E\times D$ and $D\times E$. The tensor $V^{ij}=AU^{ij}B$
satisfies $r[V]\le r[U]$ and $\ell[V]\le\ell[U]$. Each source cut of $V$
is obtained from the corresponding cut of $U$ by multiplication on both sides
by rectangular Kronecker products.

In particular, rectangular reduction cannot increase either source rank.
No equality of ranks is asserted. These inequalities allow the composition
bounds of CPSV17 to pass to a reduced representative before using its exact
rank product.

## Main statements

* `sourceCutM₁_rectangularSandwich`, `sourceCutM₂_rectangularSandwich`:
  the two rectangular multiplication formulas.
* `rightRank_rectangularSandwich_le`, `leftRank_rectangularSandwich_le`:
  monotonicity of the two source ranks.
* `sourceRanks_le_of_isReduction`: the consequence for a rectangular reduction.
* `sourceRanks_blockTensor_le_of_isReduction`: the inequalities after common blocking.

## References

The source cuts are CPSV17, arXiv:1703.09188, `defnrl`, lines 450--477;
their composition bounds occur in `IndexTh` (ii), lines 837--845.
Rectangular reduction is MGSC18, arXiv:1706.07329v2, Definition following
Proposition 20, `cornerproblem.tex` lines 3137--3139.
-/

open scoped Matrix Kronecker

namespace MPOTensor

variable {d D E : ℕ}

/-- The second source cut of a rectangular virtual multiplication is
$(A\otimes I_d)M_2(U)(I_d\otimes B)$.
Source: CPSV17, arXiv:1703.09188, `defnrl`, lines 450--477. -/
theorem sourceCutM₂_rectangularSandwich
    (A : Matrix (Fin E) (Fin D) ℂ) (U : MPOTensor d D)
    (B : Matrix (Fin D) (Fin E) ℂ) :
    sourceCutM₂ (fun i j => A * U i j * B) =
      (A ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) * sourceCutM₂ U *
        ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ B) := by
  ext ⟨α, i⟩ ⟨j, β⟩
  simp [sourceCutM₂, Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type]

/-- Rectangular multiplication on the virtual legs cannot increase the left
source rank. No inverse or one-sided inverse is required.
Source: CPSV17, arXiv:1703.09188, `defnrl`, lines 450--477. -/
theorem leftRank_rectangularSandwich_le
    (A : Matrix (Fin E) (Fin D) ℂ) (U : MPOTensor d D)
    (B : Matrix (Fin D) (Fin E) ℂ) :
    ℓ[fun i j => A * U i j * B] ≤ ℓ[U] := by
  rw [leftRank, sourceCutM₂_rectangularSandwich]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

/-- The first source cut of a rectangular virtual multiplication is
$(I_d\otimes B^{\mathsf T})M_1(U)(A^{\mathsf T}\otimes I_d)$.
Source: CPSV17, arXiv:1703.09188, `defnrl`, lines 450--477. -/
theorem sourceCutM₁_rectangularSandwich
    (A : Matrix (Fin E) (Fin D) ℂ) (U : MPOTensor d D)
    (B : Matrix (Fin D) (Fin E) ℂ) :
    sourceCutM₁ (fun i j => A * U i j * B) =
      ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ B.transpose) * sourceCutM₁ U *
        (A.transpose ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) := by
  ext ⟨i, β⟩ ⟨α, j⟩
  simp only [sourceCutM₁, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Matrix.transpose_apply, Fintype.sum_prod_type,
    ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [mul_comm, mul_left_comm]

/-- Rectangular multiplication on the virtual legs cannot increase the right
source rank. No inverse or one-sided inverse is required.
Source: CPSV17, arXiv:1703.09188, `defnrl`, lines 450--477. -/
theorem rightRank_rectangularSandwich_le
    (A : Matrix (Fin E) (Fin D) ℂ) (U : MPOTensor d D)
    (B : Matrix (Fin D) (Fin E) ℂ) :
    r[fun i j => A * U i j * B] ≤ r[U] := by
  rw [rightRank, sourceCutM₁_rectangularSandwich]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

/-- A rectangular reduction cannot increase either source rank. The
single-letter reduction identities suffice for these inequalities.
Sources: MGSC18, arXiv:1706.07329v2, Definition following Proposition 20;
CPSV17, arXiv:1703.09188, `defnrl`, lines 450--477. -/
theorem sourceRanks_le_of_isReduction
    {U : MPOTensor d D} {V : MPOTensor d E}
    {A : Matrix (Fin E) (Fin D) ℂ} {B : Matrix (Fin D) (Fin E) ℂ}
    (h : MPSTensor.IsReduction U.toMPSTensor V.toMPSTensor A B) :
    r[V] ≤ r[U] ∧ ℓ[V] ≤ ℓ[U] := by
  have hletter (i j : Fin d) : A * U i j * B = V i j := by
    simpa [Kraus.evalWord, toMPSTensor] using h.evalWord [finProdFinEquiv (i, j)]
  have hV : V = fun i j => A * U i j * B :=
    funext fun i => funext fun j => (hletter i j).symm
  exact hV.symm ▸ ⟨rightRank_rectangularSandwich_le A U B,
    leftRank_rectangularSandwich_le A U B⟩

/-- A rectangular reduction cannot increase either source rank after any
common physical blocking. The same reduction matrices act on every blocked word.
Sources: MGSC18, arXiv:1706.07329v2, Definition following Proposition 20;
CPSV17, arXiv:1703.09188, `IndexTh` (ii), lines 837--845. -/
theorem sourceRanks_blockTensor_le_of_isReduction
    {U : MPOTensor d D} {V : MPOTensor d E}
    {A : Matrix (Fin E) (Fin D) ℂ} {B : Matrix (Fin D) (Fin E) ℂ}
    (h : MPSTensor.IsReduction U.toMPSTensor V.toMPSTensor A B) (L : ℕ) :
    r[blockTensor V L] ≤ r[blockTensor U L] ∧
      ℓ[blockTensor V L] ≤ ℓ[blockTensor U L] := by
  apply sourceRanks_le_of_isReduction (A := A) (B := B)
  simpa only [toMPSTensor_blockTensor] using
    (h.blockTensor L).reindexPhysical (blockedDoubledIndexEquiv d L)

end MPOTensor
