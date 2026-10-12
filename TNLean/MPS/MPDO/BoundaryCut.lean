/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.Boundary
import TNLean.MPS.MPDO.AreaLaw
import TNLean.MPS.MPDO.CommutingForm
import TNLean.MPS.ParentHamiltonian.Basic

/-!
# Finite cuts of boundary-weighted matrix product operators

Cutting the virtual trace expresses a finite MPO as a sum of tensor products
of arbitrary-boundary operators on a window and its complement. For a cyclic
window the global boundary must commute with the tensor letters; the local
boundaries produced by the cut need not commute with them.

This gives a local-to-periodic commutation theorem used in the parent-Hamiltonian
argument of Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, Section 5,
lines 1276--1320. No physical-unit or normality assumption is needed.
-/

open scoped Matrix Kronecker BigOperators

namespace MPOTensor

variable {d D : ℕ}

private theorem trace_mul_mul_eq_sum_matrixUnits
    (X A B : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.trace (X * (A * B)) =
      ∑ a : Fin D, ∑ b : Fin D,
        Matrix.trace ((Matrix.single b a 1 * X) * A) *
          Matrix.trace (Matrix.single a b 1 * B) := by
  simp only [Matrix.mul_assoc, Matrix.trace_single_mul, one_smul]
  rw [← Matrix.mul_assoc]
  rfl

/-- Cutting a boundary-weighted trace between a prefix and suffix gives a finite
sum of arbitrary-boundary MPO tensor products. The identity holds also when one
side of the cut is empty. Source: the finite-chain contraction underlying GLM23,
arXiv:2203.12563v3, Section 5, lines 1276--1320. -/
theorem mpoWithBoundary_reindex_blockSplit (T : MPOTensor d D)
    (X : Matrix (Fin D) (Fin D) ℂ) (L K : ℕ) :
    Matrix.reindex (blockSplitEquiv d L K) (blockSplitEquiv d L K)
        (mpoWithBoundary T X (L + K)) =
      ∑ a : Fin D, ∑ b : Fin D,
        mpoWithBoundary T (Matrix.single b a 1 * X) L ⊗ₖ
          mpoWithBoundary T (Matrix.single a b 1) K := by
  classical
  ext ⟨σ, τ⟩ ⟨σ', τ'⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, blockSplitEquiv_symm_apply,
    Matrix.sum_apply, Matrix.kroneckerMap_apply, mpoWithBoundary, List.ofFn_fin_append]
  rw [evalWord_append T _ _ _ _ (by simp)]
  exact trace_mul_mul_eq_sum_matrixUnits X _ _

private theorem trace_mul_evalWord_rotate_one (T : MPOTensor d D)
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : X ∈ commutingBoundaryAlgebra T)
    (w w' : List (Fin d)) (hlen : w.length = w'.length) :
    Matrix.trace (X * evalWord T (w.rotate 1) (w'.rotate 1)) =
      Matrix.trace (X * evalWord T w w') := by
  cases w with
  | nil =>
      have hw' : w' = [] := List.length_eq_zero_iff.mp hlen.symm
      subst w'
      rfl
  | cons a l =>
      cases w' with
      | nil => simp at hlen
      | cons b k =>
          rw [List.rotate_cons_succ, List.rotate_zero, List.rotate_cons_succ,
            List.rotate_zero, evalWord_append T l k [a] [b] (by simpa using hlen)]
          simp only [evalWord_cons, evalWord_nil, Matrix.mul_one]
          rw [Matrix.trace_mul_cycle', ← Matrix.mul_assoc,
            ((mem_commutingBoundaryAlgebra_iff T X).mp hX a b).eq.symm,
            Matrix.mul_assoc]

/-- A commuting boundary can be slid around a closed virtual word, so simultaneous
cyclic rotations leave the boundary-weighted trace unchanged. Source: the cyclic
symmetry contraction in GLM23, Section 5, lines 1276--1320. -/
theorem trace_mul_evalWord_rotate (T : MPOTensor d D)
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : X ∈ commutingBoundaryAlgebra T)
    (w w' : List (Fin d)) (hlen : w.length = w'.length) (p : ℕ) :
    Matrix.trace (X * evalWord T (w.rotate p) (w'.rotate p)) =
      Matrix.trace (X * evalWord T w w') := by
  induction p with
  | zero => simp
  | succ p ih =>
      rw [← List.rotate_rotate, ← List.rotate_rotate,
        trace_mul_evalWord_rotate_one T hX _ _ (by simpa using hlen)]
      exact ih

private theorem rotate_ofFn_eq_windowComplement {N : ℕ}
    (L : ℕ) (hLN : L ≤ N) (i : Fin N) (σ : Fin N → Fin d) :
    (List.ofFn σ).rotate i.val =
      List.ofFn ((windowComplementEquiv L N hLN i σ).1) ++
        List.ofFn ((windowComplementEquiv L N hLN i σ).2) := by
  simp only [windowComplementEquiv, Equiv.coe_fn_mk]
  simpa only [MPSTensor.replaceWindow_extractWindow] using
    MPSTensor.rotate_ofFn_replaceWindow L N hLN i σ
      (MPSTensor.extractWindow L i σ) (Fin.pos i)

/-- The finite MPO cut formula at an arbitrary, possibly wrapping, periodic
window. The global boundary commutes with every tensor letter. No such condition
is imposed on the local matrix-unit boundaries created by the cut. Source:
GLM23, arXiv:2203.12563v3, Section 5, lines 1276--1320. -/
theorem mpoWithBoundary_reindex_windowComplement (T : MPOTensor d D)
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : X ∈ commutingBoundaryAlgebra T)
    {N : ℕ} (L : ℕ) (hLN : L ≤ N) (i : Fin N) :
    Matrix.reindex (windowComplementEquiv L N hLN i)
        (windowComplementEquiv L N hLN i) (mpoWithBoundary T X N) =
      ∑ a : Fin D, ∑ b : Fin D,
        mpoWithBoundary T (Matrix.single b a 1 * X) L ⊗ₖ
          mpoWithBoundary T (Matrix.single a b 1) (N - L) := by
  classical
  ext ⟨σ, τ⟩ ⟨σ', τ'⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sum_apply,
    Matrix.kroneckerMap_apply, mpoWithBoundary]
  rw [← trace_mul_evalWord_rotate T hX _ _ (by simp) i.val]
  rw [rotate_ofFn_eq_windowComplement L hLN i,
    rotate_ofFn_eq_windowComplement L hLN i,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rw [evalWord_append T _ _ _ _ (by simp)]
  exact trace_mul_mul_eq_sum_matrixUnits X _ _

/-- A local operator commuting with the entire arbitrary-boundary range commutes,
when placed at any periodic window, with every globally commuting-boundary MPO.
This is the finite-cut implication needed by the canonical-parent argument in
GLM23, arXiv:2203.12563v3, Section 5, lines 1276--1320. -/
theorem embedLocalOperator_commute_mpoWithBoundary (T : MPOTensor d D)
    {L N : ℕ} (hLN : L ≤ N) (i : Fin N)
    (K : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ)
    (hcomm : ∀ Y : Matrix (Fin D) (Fin D) ℂ, Commute K (mpoWithBoundary T Y L))
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : X ∈ commutingBoundaryAlgebra T) :
    Commute (embedLocalOperator L N hLN i K) (mpoWithBoundary T X N) := by
  classical
  let e := windowComplementEquiv (d := d) L N hLN i
  apply (commute_iff_eq _ _).2
  apply (Matrix.reindex e e).injective
  change (Matrix.reindexLinearEquiv ℂ ℂ e e)
      (embedLocalOperator L N hLN i K * mpoWithBoundary T X N) =
    (Matrix.reindexLinearEquiv ℂ ℂ e e)
      (mpoWithBoundary T X N * embedLocalOperator L N hLN i K)
  rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ e e e,
    ← Matrix.reindexLinearEquiv_mul ℂ ℂ e e e]
  simp only [Matrix.coe_reindexLinearEquiv, e]
  rw [reindex_embedLocalOperator_windowComplement,
    mpoWithBoundary_reindex_windowComplement T hX]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one, (hcomm (Matrix.single b a 1 * X)).eq]

end MPOTensor
