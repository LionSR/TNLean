/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinTupleEquiv
import TNLean.MPS.MPU.SourceUContraction
import TNLean.MPS.MPU.SourceUV

/-!
# Open-tail expansions through the source tensor u

This file develops the open-tail source-factor algebra used in the proof of
`lemuisometry` from arXiv:1703.09188, lines 536--557. It factors an open
periodic MPO through $X_1$, the source tensor $u$, and $X_2$, without closing
the remaining virtual tail.

The retained output pair is consistently denoted by \(q\); the corresponding
pair in a conjugated expression is denoted by \(p\). Thus later contractions
have the paper's order: the \(q\) term is unstarred and the \(p\) term is starred.

**Scope boundary:** no result here collapses the sandwiched open tail, proves
that `sourceU` is an isometry, or derives its rank bound. In particular, the
proofs use only the valid identity $X_2^\dagger X_2=1$ and never assert the
false ambient identity $X_2X_2^\dagger=1$.
-/

open scoped Matrix BigOperators ComplexOrder
open Matrix

namespace MPOTensor

variable {d D : ℕ} (U : MPOTensor d D)

/-- Entrywise weighted normalization of the first source-cut factor $X_1$.

Source: arXiv:1703.09188, equation `Y1Y1X1X1`, lines 479--494. -/
theorem sourceX₁_weighted_isometry_apply
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) (r r' : Fin r[U]) :
    (∑ y : Fin D × Fin d, ∑ x : Fin D × Fin d,
      star (sourceX₁ U ρ hρ x r) * sourceWeight (d := d) ρ x y *
        sourceX₁ U ρ hρ y r') = if r = r' then 1 else 0 := by
  have h := congrArg (fun M ↦ M r r') (sourceX₁_weighted_isometry U ρ hρ)
  simpa only [Matrix.mul_apply, Matrix.one_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul] using h

/-- Contracting the right source leg of $X_1$ with $u$ leaves the open $X_2$
leg of the first raw tensor letter.

Source: arXiv:1703.09188, equations `SVDforms2` and `uu`, lines 515--537. -/
theorem sum_sourceX₁_mul_sourceU
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (i₁ j₁ i₂ : Fin d) (α : Fin D) (l : Fin ℓ[U]) :
    (∑ r : Fin r[U],
      sourceX₁ U ρ hρ (α, j₁) r * sourceU U ρ hρ (l, r) (i₁, i₂)) =
      ∑ β : Fin D, U i₁ j₁ α β * sourceX₂ U (β, i₂) l := by
  classical
  simp only [sourceU_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro β _
  calc
    _ = (∑ r : Fin r[U], sourceX₁ U ρ hρ (α, j₁) r *
          sourceY₁ U ρ hρ r (i₁, β)) * sourceX₂ U (β, i₂) l := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = _ := by
      rw [← Matrix.mul_apply, sourceX₁_mul_sourceY₁_apply]

/-- The open two-site matrix product factors through $X_1$, $u$, and $Y_2$.

Source: arXiv:1703.09188, equation `SVDforms2`, lines 526--530, and equation
`uu`, lines 536--537. -/
theorem mul_apply_eq_sum_sourceX₁_mul_sourceU_mul_sourceY₂
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (i₁ j₁ i₂ j₂ : Fin d) (α γ : Fin D) :
    (U i₁ j₁ * U i₂ j₂) α γ =
      ∑ r : Fin r[U], ∑ l : Fin ℓ[U],
        sourceX₁ U ρ hρ (α, j₁) r * sourceU U ρ hρ (l, r) (i₁, i₂) *
          sourceY₂ U l (j₂, γ) := by
  classical
  simp only [Matrix.mul_apply]
  have h₁ (β : Fin D) : U i₁ j₁ α β =
      ∑ r : Fin r[U], sourceX₁ U ρ hρ (α, j₁) r *
        sourceY₁ U ρ hρ r (i₁, β) := by
    simpa only [Matrix.mul_apply] using
      (sourceX₁_mul_sourceY₁_apply U ρ hρ α j₁ i₁ β).symm
  have h₂ (β : Fin D) : U i₂ j₂ β γ =
      ∑ l : Fin ℓ[U], sourceX₂ U (β, i₂) l * sourceY₂ U l (j₂, γ) := by
    simpa only [Matrix.mul_apply] using
      (sourceX₂_mul_sourceY₂_apply U β i₂ j₂ γ).symm
  simp_rw [h₁, h₂, Finset.sum_mul_sum]
  simp_rw [sourceU_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro β _
  ring

/-- Pair-index reformulation of the open two-site factorization. The output
pair is \(q\), while \(j\) is the input pair. The name \(p\) remains reserved for the
retained output pair in the conjugated factor of a later Gram contraction.

Source: arXiv:1703.09188, equations `SVDforms2` and `uu`, lines 526--537. -/
theorem mul_apply_eq_sum_sourceX₁_mul_sourceU_mul_sourceY₂_pair
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (q j : Fin d × Fin d) (α γ : Fin D) :
    (U q.1 j.1 * U q.2 j.2) α γ =
      ∑ r : Fin r[U], ∑ l : Fin ℓ[U],
        sourceX₁ U ρ hρ (α, j.1) r * sourceU U ρ hρ (l, r) q *
          sourceY₂ U l (j.2, γ) := by
  exact mul_apply_eq_sum_sourceX₁_mul_sourceU_mul_sourceY₂ U ρ hρ
    q.1 j.1 q.2 j.2 α γ

/-- An open periodic MPO, reindexed into its first two sites and tail, factors
through $X_1$, $u$, $Y_2$, and the unevaluated virtual tail.

The retained output pair is \(q\); the pair \(j\) belongs to the input word.
Source: arXiv:1703.09188, equations `SVDforms2` and `uu`, lines 515--537. -/
theorem mpo_finAddTwo_eq_sum_sourceX₁_sourceU_sourceY₂_evalWord
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) (K : ℕ)
    (q j : Fin d × Fin d) (τ ζ : Fin K → Fin d) :
    mpo U (K + 2) ((finAddTwoArrowEquiv (Fin d) K).symm (q, τ))
        ((finAddTwoArrowEquiv (Fin d) K).symm (j, ζ)) =
      ∑ α : Fin D, ∑ γ : Fin D, ∑ r : Fin r[U], ∑ l : Fin ℓ[U],
        sourceX₁ U ρ hρ (α, j.1) r * sourceU U ρ hρ (l, r) q *
          sourceY₂ U l (j.2, γ) * evalWord U (List.ofFn τ) (List.ofFn ζ) γ α := by
  classical
  simp only [finAddTwoArrowEquiv_symm_apply]
  calc
    _ = Matrix.trace ((U q.1 j.1 * U q.2 j.2) *
        evalWord U (List.ofFn τ) (List.ofFn ζ)) := by
      rw [mpo_apply, mpoMatrixEntry]
      simp only [List.ofFn_succ, evalWord_cons, Fin.cons_zero, Fin.cons_succ]
      rw [← Matrix.mul_assoc]
    _ = ∑ α : Fin D, ∑ γ : Fin D,
        (U q.1 j.1 * U q.2 j.2) α γ *
          evalWord U (List.ofFn τ) (List.ofFn ζ) γ α := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    _ = _ := by
      simp_rw [mul_apply_eq_sum_sourceX₁_mul_sourceU_mul_sourceY₂_pair U ρ hρ]
      simp only [Finset.sum_mul, mul_assoc]

/-- The fully reconstructed open periodic MPO expansion through $X_1$, $u$,
$X_2$, and the open $K$-site virtual tail.

There is no normalization factor in this algebraic expansion. The unique
factor $d^{-K}$ enters only when the future normalized output-tail contraction
is formed.

Source: arXiv:1703.09188, equations `SVDforms2` and `uUnitary`, lines
515--554. -/
theorem mpo_finAddTwo_eq_sum_sourceX₁_sourceU_sourceX₂_openTail
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) (K : ℕ)
    (q j : Fin d × Fin d) (τ ζ : Fin K → Fin d) :
    mpo U (K + 2) ((finAddTwoArrowEquiv (Fin d) K).symm (q, τ))
        ((finAddTwoArrowEquiv (Fin d) K).symm (j, ζ)) =
      ∑ α : Fin D, ∑ r : Fin r[U], ∑ l : Fin ℓ[U],
        ∑ β : Fin D, ∑ i : Fin d,
          sourceX₁ U ρ hρ (α, j.1) r * sourceU U ρ hρ (l, r) q *
            star (sourceX₂ U (β, i) l) *
              (U i j.2 * evalWord U (List.ofFn τ) (List.ofFn ζ)) β α := by
  classical
  have sourceY₂_apply (l : Fin ℓ[U]) (j : Fin d) (γ : Fin D) :
      sourceY₂ U l (j, γ) =
        ∑ β : Fin D, ∑ i : Fin d, star (sourceX₂ U (β, i) l) * U i j β γ := by
    have h := congrArg (fun M ↦ M l (j, γ))
      (sourceY₂_eq_sourceX₂_conjTranspose_mul_sourceCutM₂ U)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply] at h
    rw [Fintype.sum_prod_type] at h
    exact h
  rw [mpo_finAddTwo_eq_sum_sourceX₁_sourceU_sourceY₂_evalWord U ρ hρ K q j τ ζ]
  simp_rw [sourceY₂_apply]
  simp only [Finset.mul_sum, Finset.sum_mul, Matrix.mul_apply, mul_assoc]
  apply Finset.sum_congr rfl
  intro α _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro β _
  rw [Finset.sum_comm]

end MPOTensor
