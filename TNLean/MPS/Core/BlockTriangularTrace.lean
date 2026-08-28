/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.ProjectionTriangularTrace
import TNLean.MPS.Core.MultiBlock

import Mathlib.Data.Matrix.Block
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Block-triangular trace invariance for MPS tensors

This file specializes the coordinate-free projection-triangular API to the decomposition
`Fin n ⊕ Fin m`, transported to `Fin (n + m)` by `finSumFinEquiv`. The public coordinate
constructions and statements are retained as a compatibility interface, while their proofs
are obtained from the projection formulation.
-/

open scoped Matrix BigOperators

namespace MPSTensor

section BlockTriangular

variable {d n m : ℕ}

/-- A `2×2` block upper-triangular tensor on `Fin n ⊕ Fin m` indices. -/
noncomputable def upperSum
    (A11 : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (A12 : Fin d → Matrix (Fin n) (Fin m) ℂ)
    (A22 : Fin d → Matrix (Fin m) (Fin m) ℂ) :
    Fin d → Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℂ :=
  fun i => Matrix.fromBlocks (A11 i) (A12 i) 0 (A22 i)

/-- The block-diagonal part of a `2×2` block tensor on `Fin n ⊕ Fin m` indices. -/
noncomputable def diagSum
    (A11 : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (A22 : Fin d → Matrix (Fin m) (Fin m) ℂ) :
    Fin d → Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℂ :=
  fun i => Matrix.fromBlocks (A11 i) 0 0 (A22 i)

/-- Reindex `upperSum` from `Fin n ⊕ Fin m` to `Fin (n+m)`, producing an `MPSTensor d (n+m)`. -/
noncomputable def upperFin
    (A11 : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (A12 : Fin d → Matrix (Fin n) (Fin m) ℂ)
    (A22 : Fin d → Matrix (Fin m) (Fin m) ℂ) :
    MPSTensor d (n + m) :=
  fun i =>
    Matrix.reindex (finSumFinEquiv (m := n) (n := m)) (finSumFinEquiv (m := n) (n := m))
      (upperSum (d := d) (n := n) (m := m) A11 A12 A22 i)

/-- Reindex `diagSum` from `Fin n ⊕ Fin m` to `Fin (n+m)`, producing an `MPSTensor d (n+m)`. -/
noncomputable def diagFin
    (A11 : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (A22 : Fin d → Matrix (Fin m) (Fin m) ℂ) :
    MPSTensor d (n + m) :=
  fun i =>
    Matrix.reindex (finSumFinEquiv (m := n) (n := m)) (finSumFinEquiv (m := n) (n := m))
      (diagSum (d := d) (n := n) (m := m) A11 A22 i)


private noncomputable def sumProj (n m : ℕ) :
    Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℂ :=
  Matrix.fromBlocks 1 0 0 0

private noncomputable def coordProj (n m : ℕ) :
    Matrix (Fin (n + m)) (Fin (n + m)) ℂ :=
  Matrix.reindex (finSumFinEquiv (m := n) (n := m)) (finSumFinEquiv (m := n) (n := m))
    (sumProj n m)

private lemma sumProj_isHermitian : (sumProj n m).IsHermitian := by
  exact Matrix.IsHermitian.fromBlocks (by simp) (by simp) (by simp)

private lemma sumProj_isIdempotent : sumProj n m * sumProj n m = sumProj n m := by
  simp [sumProj, Matrix.fromBlocks_multiply]

private lemma coordProj_isOrthogonalProjection :
    IsOrthogonalProjection (coordProj n m) := by
  let e : (Fin n ⊕ Fin m) ≃ Fin (n + m) := finSumFinEquiv
  constructor
  · exact sumProj_isHermitian.reindex e
  · change (Matrix.reindexRingEquiv ℂ e) (sumProj n m) *
        (Matrix.reindexRingEquiv ℂ e) (sumProj n m) =
      (Matrix.reindexRingEquiv ℂ e) (sumProj n m)
    rw [← map_mul, sumProj_isIdempotent]

private lemma one_sub_sumProj :
    1 - sumProj n m =
      Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) 0 0 (1 : Matrix (Fin m) (Fin m) ℂ) := by
  classical
  rw [← Matrix.fromBlocks_one]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [sumProj, Matrix.one_apply]

private lemma lowerZero_upperBlocks
    (X : Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin n) (Fin m) ℂ)
    (Z : Matrix (Fin m) (Fin m) ℂ) :
    (1 - sumProj n m) * Matrix.fromBlocks X Y 0 Z * sumProj n m = 0 := by
  rw [one_sub_sumProj]
  simp [sumProj, Matrix.fromBlocks_multiply]

private lemma diagPart_upperBlocks
    (X : Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin n) (Fin m) ℂ)
    (Z : Matrix (Fin m) (Fin m) ℂ) :
    sumProj n m * Matrix.fromBlocks X Y 0 Z * sumProj n m +
      (1 - sumProj n m) * Matrix.fromBlocks X Y 0 Z * (1 - sumProj n m) =
      Matrix.fromBlocks X 0 0 Z := by
  rw [one_sub_sumProj]
  simp only [sumProj, Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp

private lemma lowerZero_upperFin
    (A11 : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (A12 : Fin d → Matrix (Fin n) (Fin m) ℂ)
    (A22 : Fin d → Matrix (Fin m) (Fin m) ℂ) :
    ∀ i, (1 - coordProj n m) * upperFin A11 A12 A22 i * coordProj n m = 0 := by
  intro i
  let e : (Fin n ⊕ Fin m) ≃ Fin (n + m) := finSumFinEquiv
  change (1 - (Matrix.reindexRingEquiv ℂ e) (sumProj n m)) *
      (Matrix.reindexRingEquiv ℂ e) (Matrix.fromBlocks (A11 i) (A12 i) 0 (A22 i)) *
      (Matrix.reindexRingEquiv ℂ e) (sumProj n m) = 0
  simpa only [map_sub, map_one, map_mul, map_zero] using
    congrArg (Matrix.reindexRingEquiv ℂ e)
      (lowerZero_upperBlocks (A11 i) (A12 i) (A22 i))

private lemma diagPart_upperFin
    (A11 : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (A12 : Fin d → Matrix (Fin n) (Fin m) ℂ)
    (A22 : Fin d → Matrix (Fin m) (Fin m) ℂ) :
    Kraus.diagPart (upperFin A11 A12 A22) (coordProj n m) = diagFin A11 A22 := by
  funext i
  let e : (Fin n ⊕ Fin m) ≃ Fin (n + m) := finSumFinEquiv
  change (Matrix.reindexRingEquiv ℂ e) (sumProj n m) *
        (Matrix.reindexRingEquiv ℂ e) (Matrix.fromBlocks (A11 i) (A12 i) 0 (A22 i)) *
        (Matrix.reindexRingEquiv ℂ e) (sumProj n m) +
      (1 - (Matrix.reindexRingEquiv ℂ e) (sumProj n m)) *
        (Matrix.reindexRingEquiv ℂ e) (Matrix.fromBlocks (A11 i) (A12 i) 0 (A22 i)) *
        (1 - (Matrix.reindexRingEquiv ℂ e) (sumProj n m)) =
      (Matrix.reindexRingEquiv ℂ e) (Matrix.fromBlocks (A11 i) 0 0 (A22 i))
  simpa only [map_sub, map_one, map_mul, map_add] using
    congrArg (Matrix.reindexRingEquiv ℂ e)
      (diagPart_upperBlocks (A11 i) (A12 i) (A22 i))

private def inlMatrix (n m : ℕ) : Matrix (Fin n ⊕ Fin m) (Fin n) ℂ
  | Sum.inl i, j => (1 : Matrix (Fin n) (Fin n) ℂ) i j
  | Sum.inr _, _ => 0

private def inrMatrix (n m : ℕ) : Matrix (Fin n ⊕ Fin m) (Fin m) ℂ
  | Sum.inl _, _ => 0
  | Sum.inr i, j => (1 : Matrix (Fin m) (Fin m) ℂ) i j

private lemma evalWord_intertwine_reindex
    {ι : Type*} [Fintype ι] [DecidableEq ι] {D r : ℕ} (e : ι ≃ Fin D)
    (K : Fin d → Matrix ι ι ℂ) (L : Fin d → Matrix (Fin r) (Fin r) ℂ)
    (V : Matrix ι (Fin r) ℂ) (hInt : ∀ i, K i * V = V * L i) (w : List (Fin d)) :
    _root_.evalWord K w * V = V * _root_.evalWord L w := by
  let K' : MPSTensor d D := fun i => Matrix.reindex e e (K i)
  let V' := Matrix.reindex e (Equiv.refl _) V
  have hInt' : ∀ i, K' i * V' = V' * L i := by
    intro i
    change Matrix.reindex e e (K i) * Matrix.reindex e (Equiv.refl _) V =
      Matrix.reindex e (Equiv.refl _) V * L i
    rw [show Matrix.reindex e e (K i) * Matrix.reindex e (Equiv.refl _) V =
      Matrix.reindex e (Equiv.refl _) (K i * V) from
        Matrix.reindexLinearEquiv_mul ℂ ℂ e e (Equiv.refl _) _ _]
    rw [show Matrix.reindex e (Equiv.refl _) V * L i =
      Matrix.reindex e (Equiv.refl _) (V * L i) from
        Matrix.reindexLinearEquiv_mul ℂ ℂ e (Equiv.refl _) (Equiv.refl _) _ _]
    exact congrArg (Matrix.reindexLinearEquiv ℂ ℂ e (Equiv.refl _)) (hInt i)
  have h := Kraus.evalWord_intertwine K' L V' hInt' w
  have hReindex : Kraus.evalWord K' w = Matrix.reindex e e (_root_.evalWord K w) :=
    MPSTensor.evalWord_reindex e K w
  apply (Matrix.reindexLinearEquiv ℂ ℂ e (Equiv.refl _)).injective
  rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ e e (Equiv.refl _)]
  rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ e (Equiv.refl _) (Equiv.refl _)]
  change Matrix.reindex e e (_root_.evalWord K w) * V' = V' * _root_.evalWord L w
  rw [← hReindex]
  simpa only [MPSTensor.evalWord_aux_eq] using h

private lemma diagSum_mul_inl
    (A11 : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (A22 : Fin d → Matrix (Fin m) (Fin m) ℂ) (i : Fin d) :
    diagSum A11 A22 i * inlMatrix n m = inlMatrix n m * A11 i := by
  classical
  ext x j
  rcases x with x | x <;> simp [diagSum, Matrix.mul_apply, inlMatrix, Matrix.one_apply]

private lemma diagSum_mul_inr
    (A11 : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (A22 : Fin d → Matrix (Fin m) (Fin m) ℂ) (i : Fin d) :
    diagSum A11 A22 i * inrMatrix n m = inrMatrix n m * A22 i := by
  classical
  ext x j
  rcases x with x | x <;> simp [diagSum, Matrix.mul_apply, inrMatrix, Matrix.one_apply]

private lemma evalWord_diagSumAux
    (A11 : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (A22 : Fin d → Matrix (Fin m) (Fin m) ℂ) (w : List (Fin d)) :
    _root_.evalWord (diagSum A11 A22) w =
      Matrix.fromBlocks (_root_.evalWord A11 w) 0 0 (_root_.evalWord A22 w) := by
  classical
  have h₁ := evalWord_intertwine_reindex finSumFinEquiv (diagSum A11 A22) A11
    (inlMatrix n m) (diagSum_mul_inl A11 A22) w
  have h₂ := evalWord_intertwine_reindex finSumFinEquiv (diagSum A11 A22) A22
    (inrMatrix n m) (diagSum_mul_inr A11 A22) w
  ext x y
  rcases y with y | y
  · have h := congrArg (fun M => M x y) h₁
    rcases x with x | x <;>
      simpa [Matrix.mul_apply, Fintype.sum_sum_type, inlMatrix, Matrix.one_apply] using h
  · have h := congrArg (fun M => M x y) h₂
    rcases x with x | x <;>
      simpa [Matrix.mul_apply, Fintype.sum_sum_type, inrMatrix, Matrix.one_apply] using h

private lemma sumProj_compressions (M : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℂ) :
    sumProj n m * M * sumProj n m + (1 - sumProj n m) * M * (1 - sumProj n m) =
      Matrix.fromBlocks (Matrix.toBlocks₁₁ M) 0 0 (Matrix.toBlocks₂₂ M) := by
  rw [← Matrix.fromBlocks_toBlocks M, one_sub_sumProj]
  simp only [sumProj, Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp

private lemma sumProj_lowerCompression (M : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℂ) :
    (1 - sumProj n m) * M * sumProj n m =
      Matrix.fromBlocks 0 0 (Matrix.toBlocks₂₁ M) 0 := by
  rw [← Matrix.fromBlocks_toBlocks M, one_sub_sumProj]
  simp only [sumProj, Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp

private lemma lowerZero_evalWord_upperSum
    (A11 : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (A12 : Fin d → Matrix (Fin n) (Fin m) ℂ)
    (A22 : Fin d → Matrix (Fin m) (Fin m) ℂ) (w : List (Fin d)) :
    (1 - sumProj n m) * _root_.evalWord (upperSum A11 A12 A22) w * sumProj n m = 0 := by
  let e : (Fin n ⊕ Fin m) ≃ Fin (n + m) := finSumFinEquiv
  have h := Kraus.lowerZero_evalWord (upperFin A11 A12 A22) (coordProj n m)
    coordProj_isOrthogonalProjection (lowerZero_upperFin A11 A12 A22) w
  have hEval := MPSTensor.evalWord_reindex e (upperSum A11 A12 A22) w
  change (1 - (Matrix.reindexRingEquiv ℂ e) (sumProj n m)) *
      Kraus.evalWord (fun i => Matrix.reindex e e (upperSum A11 A12 A22 i)) w *
      (Matrix.reindexRingEquiv ℂ e) (sumProj n m) = 0 at h
  rw [hEval] at h
  change (1 - (Matrix.reindexRingEquiv ℂ e) (sumProj n m)) *
      (Matrix.reindexRingEquiv ℂ e) (_root_.evalWord (upperSum A11 A12 A22) w) *
      (Matrix.reindexRingEquiv ℂ e) (sumProj n m) = 0 at h
  apply (Matrix.reindexRingEquiv ℂ e).injective
  simpa only [map_sub, map_one, map_mul, map_zero] using h

private lemma evalWord_diagPart_upperSum
    (A11 : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (A12 : Fin d → Matrix (Fin n) (Fin m) ℂ)
    (A22 : Fin d → Matrix (Fin m) (Fin m) ℂ) (w : List (Fin d)) :
    _root_.evalWord (diagSum A11 A22) w =
      sumProj n m * _root_.evalWord (upperSum A11 A12 A22) w * sumProj n m +
        (1 - sumProj n m) * _root_.evalWord (upperSum A11 A12 A22) w *
          (1 - sumProj n m) := by
  let e : (Fin n ⊕ Fin m) ≃ Fin (n + m) := finSumFinEquiv
  have h := Kraus.evalWord_diagPart_eq (upperFin A11 A12 A22) (coordProj n m)
    coordProj_isOrthogonalProjection (lowerZero_upperFin A11 A12 A22) w
  rw [diagPart_upperFin] at h
  have hUpper := MPSTensor.evalWord_reindex e (upperSum A11 A12 A22) w
  have hDiag := MPSTensor.evalWord_reindex e
    (diagSum A11 A22) w
  change Kraus.evalWord (fun i => Matrix.reindex e e (diagSum A11 A22 i)) w =
    (Matrix.reindexRingEquiv ℂ e) (sumProj n m) *
        Kraus.evalWord (fun i => Matrix.reindex e e (upperSum A11 A12 A22 i)) w *
        (Matrix.reindexRingEquiv ℂ e) (sumProj n m) +
      (1 - (Matrix.reindexRingEquiv ℂ e) (sumProj n m)) *
        Kraus.evalWord (fun i => Matrix.reindex e e (upperSum A11 A12 A22 i)) w *
        (1 - (Matrix.reindexRingEquiv ℂ e) (sumProj n m)) at h
  rw [hUpper, hDiag] at h
  change (Matrix.reindexRingEquiv ℂ e)
      (_root_.evalWord (diagSum A11 A22) w) =
    (Matrix.reindexRingEquiv ℂ e) (sumProj n m) *
        (Matrix.reindexRingEquiv ℂ e) (_root_.evalWord (upperSum A11 A12 A22) w) *
        (Matrix.reindexRingEquiv ℂ e) (sumProj n m) +
      (1 - (Matrix.reindexRingEquiv ℂ e) (sumProj n m)) *
        (Matrix.reindexRingEquiv ℂ e) (_root_.evalWord (upperSum A11 A12 A22) w) *
        (1 - (Matrix.reindexRingEquiv ℂ e) (sumProj n m)) at h
  apply (Matrix.reindexRingEquiv ℂ e).injective
  simpa only [map_sub, map_one, map_mul, map_add] using h

private lemma evalWord_upperSumAux
    (A11 : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (A12 : Fin d → Matrix (Fin n) (Fin m) ℂ)
    (A22 : Fin d → Matrix (Fin m) (Fin m) ℂ) (w : List (Fin d)) :
    ∃ UR : Matrix (Fin n) (Fin m) ℂ,
      _root_.evalWord (upperSum A11 A12 A22) w =
        Matrix.fromBlocks (_root_.evalWord A11 w) UR 0 (_root_.evalWord A22 w) := by
  let M := _root_.evalWord (upperSum A11 A12 A22) w
  have hLower := lowerZero_evalWord_upperSum A11 A12 A22 w
  rw [sumProj_lowerCompression] at hLower
  have h21 : Matrix.toBlocks₂₁ M = 0 := by
    have h := congrArg Matrix.toBlocks₂₁ hLower
    change Matrix.toBlocks₂₁ M = (0 : Matrix (Fin m) (Fin n) ℂ) at h
    exact h
  have hDiag := evalWord_diagPart_upperSum A11 A12 A22 w
  rw [evalWord_diagSumAux A11 A22 w, sumProj_compressions] at hDiag
  have h11 : Matrix.toBlocks₁₁ M = _root_.evalWord A11 w := by
    simpa using congrArg Matrix.toBlocks₁₁ hDiag.symm
  have h22 : Matrix.toBlocks₂₂ M = _root_.evalWord A22 w := by
    simpa using congrArg Matrix.toBlocks₂₂ hDiag.symm
  refine ⟨Matrix.toBlocks₁₂ M, ?_⟩
  calc
    M = Matrix.fromBlocks (Matrix.toBlocks₁₁ M) (Matrix.toBlocks₁₂ M)
        (Matrix.toBlocks₂₁ M) (Matrix.toBlocks₂₂ M) := (Matrix.fromBlocks_toBlocks M).symm
    _ = Matrix.fromBlocks (_root_.evalWord A11 w) (Matrix.toBlocks₁₂ M) 0
        (_root_.evalWord A22 w) := by rw [h11, h21, h22]


/-- Trace of a block upper-triangular `2×2` matrix is the sum of the traces of its diagonal blocks.

The strict upper-right block does not contribute to the trace. -/
lemma trace_fromBlocks_upper (X : Matrix (Fin n) (Fin n) ℂ)
    (Y : Matrix (Fin n) (Fin m) ℂ) (Z : Matrix (Fin m) (Fin m) ℂ) :
    Matrix.trace (Matrix.fromBlocks X Y 0 Z) = Matrix.trace X + Matrix.trace Z := by
  classical
  let e : (Fin n ⊕ Fin m) ≃ Fin (n + m) := finSumFinEquiv
  let M := Matrix.fromBlocks X Y 0 Z
  have h := Matrix.trace_eq_trace_diag_of_proj (coordProj n m)
    coordProj_isOrthogonalProjection (Matrix.reindex e e M)
  change Matrix.trace ((Matrix.reindexRingEquiv ℂ e) M) =
      Matrix.trace ((Matrix.reindexRingEquiv ℂ e) (sumProj n m) *
        (Matrix.reindexRingEquiv ℂ e) M * (Matrix.reindexRingEquiv ℂ e) (sumProj n m)) +
      Matrix.trace ((1 - (Matrix.reindexRingEquiv ℂ e) (sumProj n m)) *
        (Matrix.reindexRingEquiv ℂ e) M *
          (1 - (Matrix.reindexRingEquiv ℂ e) (sumProj n m))) at h
  have hTransport : Matrix.trace ((Matrix.reindexRingEquiv ℂ e) M) =
      Matrix.trace ((Matrix.reindexRingEquiv ℂ e) (sumProj n m * M * sumProj n m)) +
        Matrix.trace ((Matrix.reindexRingEquiv ℂ e)
          ((1 - sumProj n m) * M * (1 - sumProj n m))) := by
    simpa only [map_mul, map_sub, map_one] using h
  change Matrix.trace (Matrix.reindex e e M) =
      Matrix.trace (Matrix.reindex e e (sumProj n m * M * sumProj n m)) +
        Matrix.trace (Matrix.reindex e e ((1 - sumProj n m) * M * (1 - sumProj n m)))
    at hTransport
  have h' : Matrix.trace M =
      Matrix.trace (sumProj n m * M * sumProj n m) +
        Matrix.trace ((1 - sumProj n m) * M * (1 - sumProj n m)) := by
    simpa only [Matrix.trace_reindex] using hTransport
  calc
    Matrix.trace M =
        Matrix.trace (sumProj n m * M * sumProj n m) +
          Matrix.trace ((1 - sumProj n m) * M * (1 - sumProj n m)) := h'
    _ = Matrix.trace (Matrix.fromBlocks X 0 0 Z) := by
      rw [← Matrix.trace_add, diagPart_upperBlocks]
    _ = Matrix.trace X + Matrix.trace Z := by
      simp [Matrix.trace, Fintype.sum_sum_type]

/-- For any word `w`, evaluating `upperSum` gives an upper-triangular block matrix.

The (inessential) upper-right block is carried by an auxiliary recursion `UR`. -/
lemma evalWord_upperSum_is_fromBlocks
    (A11 : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (A12 : Fin d → Matrix (Fin n) (Fin m) ℂ)
    (A22 : Fin d → Matrix (Fin m) (Fin m) ℂ) :
    ∀ w : List (Fin d),
      ∃ UR : Matrix (Fin n) (Fin m) ℂ,
        _root_.evalWord (upperSum (d := d) (n := n) (m := m) A11 A12 A22) w =
          Matrix.fromBlocks (_root_.evalWord A11 w) UR 0 (_root_.evalWord A22 w) :=
  evalWord_upperSumAux A11 A12 A22

/-- Word evaluation of `diagSum` stays block diagonal. -/
lemma evalWord_diagSum_is_fromBlocks
    (A11 : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (A22 : Fin d → Matrix (Fin m) (Fin m) ℂ) :
    ∀ w : List (Fin d),
      _root_.evalWord (diagSum (d := d) (n := n) (m := m) A11 A22) w =
        Matrix.fromBlocks (_root_.evalWord A11 w) 0 0 (_root_.evalWord A22 w) :=
  evalWord_diagSumAux A11 A22

/-- The strict upper-right blocks of an upper-triangular tensor do not affect word traces. -/
lemma trace_evalWord_upperSum_eq_trace_evalWord_diagSum
    (A11 : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (A12 : Fin d → Matrix (Fin n) (Fin m) ℂ)
    (A22 : Fin d → Matrix (Fin m) (Fin m) ℂ) :
    ∀ w : List (Fin d),
      Matrix.trace (_root_.evalWord (upperSum (d := d) (n := n) (m := m) A11 A12 A22) w)
        = Matrix.trace (_root_.evalWord (diagSum (d := d) (n := n) (m := m) A11 A22) w) := by
  intro w
  let e : (Fin n ⊕ Fin m) ≃ Fin (n + m) := finSumFinEquiv
  have h := Kraus.trace_evalWord_diagPart_eq (upperFin A11 A12 A22) (coordProj n m)
    coordProj_isOrthogonalProjection (lowerZero_upperFin A11 A12 A22) w
  rw [diagPart_upperFin] at h
  have hUpper := MPSTensor.evalWord_reindex e (upperSum A11 A12 A22) w
  have hDiag := MPSTensor.evalWord_reindex e (diagSum A11 A22) w
  change Matrix.trace (Kraus.evalWord
      (fun i => Matrix.reindex e e (upperSum A11 A12 A22 i)) w) =
    Matrix.trace (Kraus.evalWord (fun i => Matrix.reindex e e (diagSum A11 A22 i)) w) at h
  rw [hUpper, hDiag, Matrix.trace_reindex, Matrix.trace_reindex] at h
  exact h

/-- Deleting the strict upper-right blocks of a block upper-triangular tensor does not change MPVs
(after reindexing from `Fin n ⊕ Fin m` to `Fin (n+m)`). -/
lemma mpv_upperFin_eq_mpv_diagFin
    (A11 : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (A12 : Fin d → Matrix (Fin n) (Fin m) ℂ)
    (A22 : Fin d → Matrix (Fin m) (Fin m) ℂ)
    {N : ℕ} (σ : Fin N → Fin d) :
    mpv (upperFin (d := d) (n := n) (m := m) A11 A12 A22) σ =
      mpv (diagFin (d := d) (n := n) (m := m) A11 A22) σ := by
  have h := sameMPV_diagPart_of_lowerZero (upperFin A11 A12 A22) (coordProj n m)
    coordProj_isOrthogonalProjection (lowerZero_upperFin A11 A12 A22)
  rw [diagPart_upperFin] at h
  exact h N σ

/-- Final `SameMPV` statement: upper-triangular off-diagonal blocks are irrelevant for MPVs. -/
theorem sameMPV_upperFin_diagFin
    (A11 : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (A12 : Fin d → Matrix (Fin n) (Fin m) ℂ)
    (A22 : Fin d → Matrix (Fin m) (Fin m) ℂ) :
    SameMPV (upperFin (d := d) (n := n) (m := m) A11 A12 A22)
      (diagFin (d := d) (n := n) (m := m) A11 A22) := by
  rw [← diagPart_upperFin A11 A12 A22]
  exact sameMPV_diagPart_of_lowerZero (upperFin A11 A12 A22) (coordProj n m)
    coordProj_isOrthogonalProjection (lowerZero_upperFin A11 A12 A22)

end BlockTriangular

end MPSTensor
