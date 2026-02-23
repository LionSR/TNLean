import TNLean.MPS.Defs
import TNLean.MPS.MultiBlock

import Mathlib.Data.Matrix.Block
import Mathlib.Logic.Equiv.Fin.Basic

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


/-- Trace of a block upper-triangular `2×2` matrix is the sum of the traces of its diagonal blocks.

The strict upper-right block does not contribute to the trace. -/
lemma trace_fromBlocks_upper (X : Matrix (Fin n) (Fin n) ℂ)
    (Y : Matrix (Fin n) (Fin m) ℂ) (Z : Matrix (Fin m) (Fin m) ℂ) :
    Matrix.trace (Matrix.fromBlocks X Y 0 Z) = Matrix.trace X + Matrix.trace Z := by
  classical
  -- Expand `trace` as a sum over the diagonal and split the `Sum` index.
  simp [Matrix.trace, Fintype.sum_sum_type]


/-- For any word `w`, evaluating `upperSum` gives an upper-triangular block matrix.

We package the (inessential) upper-right block into an auxiliary recursion `UR`. -/
lemma evalWord_upperSum_is_fromBlocks
    (A11 : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (A12 : Fin d → Matrix (Fin n) (Fin m) ℂ)
    (A22 : Fin d → Matrix (Fin m) (Fin m) ℂ) :
    ∀ w : List (Fin d),
      ∃ UR : Matrix (Fin n) (Fin m) ℂ,
        _root_.evalWord (upperSum (d := d) (n := n) (m := m) A11 A12 A22) w =
          Matrix.fromBlocks (_root_.evalWord A11 w) UR 0 (_root_.evalWord A22 w) := by
  classical
  intro w
  induction w with
  | nil =>
      refine ⟨0, ?_⟩
      simp [_root_.evalWord]
  | cons i w ih =>
      rcases ih with ⟨URw, hURw⟩
      -- Multiply two block-upper-triangular matrices; the lower-left block stays `0`.
      refine ⟨A11 i * URw + A12 i * _root_.evalWord A22 w, ?_⟩
      simp [upperSum, _root_.evalWord, hURw, Matrix.fromBlocks_multiply]


/-- Word evaluation of `diagSum` stays block diagonal. -/
lemma evalWord_diagSum_is_fromBlocks
    (A11 : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (A22 : Fin d → Matrix (Fin m) (Fin m) ℂ) :
    ∀ w : List (Fin d),
      _root_.evalWord (diagSum (d := d) (n := n) (m := m) A11 A22) w =
        Matrix.fromBlocks (_root_.evalWord A11 w) 0 0 (_root_.evalWord A22 w) := by
  classical
  intro w
  induction w with
  | nil =>
      simp [_root_.evalWord]
  | cons i w ih =>
      simp [diagSum, _root_.evalWord, ih, Matrix.fromBlocks_multiply]


/-- The strict upper-right blocks of an upper-triangular tensor do not affect word traces. -/
lemma trace_evalWord_upperSum_eq_trace_evalWord_diagSum
    (A11 : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (A12 : Fin d → Matrix (Fin n) (Fin m) ℂ)
    (A22 : Fin d → Matrix (Fin m) (Fin m) ℂ) :
    ∀ w : List (Fin d),
      Matrix.trace (_root_.evalWord (upperSum (d := d) (n := n) (m := m) A11 A12 A22) w)
        = Matrix.trace (_root_.evalWord (diagSum (d := d) (n := n) (m := m) A11 A22) w) := by
  classical
  intro w
  rcases evalWord_upperSum_is_fromBlocks (d := d) (n := n) (m := m) A11 A12 A22 w with
    ⟨UR, hUR⟩
  have hDiag := evalWord_diagSum_is_fromBlocks (d := d) (n := n) (m := m) A11 A22 w
  -- Now take traces; the upper-right block is irrelevant.
  simp [hUR, hDiag, trace_fromBlocks_upper]


/-- Deleting the strict upper-right blocks of a block upper-triangular tensor does not change MPVs
(after reindexing from `Fin n ⊕ Fin m` to `Fin (n+m)`). -/
lemma mpv_upperFin_eq_mpv_diagFin
    (A11 : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (A12 : Fin d → Matrix (Fin n) (Fin m) ℂ)
    (A22 : Fin d → Matrix (Fin m) (Fin m) ℂ)
    {N : ℕ} (σ : Fin N → Fin d) :
    mpv (upperFin (d := d) (n := n) (m := m) A11 A12 A22) σ =
      mpv (diagFin (d := d) (n := n) (m := m) A11 A22) σ := by
  classical
  let e : (Fin n ⊕ Fin m) ≃ Fin (n + m) := finSumFinEquiv (m := n) (n := m)
  set w : List (Fin d) := List.ofFn σ with hw
  -- Expand the MPV coefficients.
  simp only [MPSTensor.mpv, MPSTensor.coeff, hw.symm]
  -- Commute `evalWord` with reindexing, then drop the reindexing inside `trace`.
  have hUpperEval :
      MPSTensor.evalWord (upperFin (d := d) (n := n) (m := m) A11 A12 A22) w =
        Matrix.reindex e e
          (_root_.evalWord (upperSum (d := d) (n := n) (m := m) A11 A12 A22) w) := by
    simpa [upperFin, e] using
      (MPSTensor.evalWord_reindex (d := d) (D := n + m) (e := e)
        (A := upperSum (d := d) (n := n) (m := m) A11 A12 A22) w)
  have hDiagEval :
      MPSTensor.evalWord (diagFin (d := d) (n := n) (m := m) A11 A22) w =
        Matrix.reindex e e
          (_root_.evalWord (diagSum (d := d) (n := n) (m := m) A11 A22) w) := by
    simpa [diagFin, e] using
      (MPSTensor.evalWord_reindex (d := d) (D := n + m) (e := e)
        (A := diagSum (d := d) (n := n) (m := m) A11 A22) w)
  -- Reduce to the Sum-index trace identity.
  --
  -- `trace (reindex e e M) = trace M`, so the reindexing from `Fin n ⊕ Fin m` to `Fin (n+m)`
  -- does not affect the coefficient.
  calc
    Matrix.trace (MPSTensor.evalWord (upperFin (d := d) (n := n) (m := m) A11 A12 A22) w)
        = Matrix.trace (Matrix.reindex e e
            (_root_.evalWord (upperSum (d := d) (n := n) (m := m) A11 A12 A22) w)) := by
          simp [hUpperEval]
    _ = Matrix.trace
          (_root_.evalWord (upperSum (d := d) (n := n) (m := m) A11 A12 A22) w) := by
          simpa using (Matrix.trace_reindex e
            (_root_.evalWord (upperSum (d := d) (n := n) (m := m) A11 A12 A22) w))
    _ = Matrix.trace
          (_root_.evalWord (diagSum (d := d) (n := n) (m := m) A11 A22) w) := by
          simpa using
            trace_evalWord_upperSum_eq_trace_evalWord_diagSum
              (d := d) (n := n) (m := m) A11 A12 A22 w
    _ = Matrix.trace (Matrix.reindex e e
          (_root_.evalWord (diagSum (d := d) (n := n) (m := m) A11 A22) w)) := by
          simpa using (Matrix.trace_reindex e
            (_root_.evalWord (diagSum (d := d) (n := n) (m := m) A11 A22) w)).symm
    _ = Matrix.trace (MPSTensor.evalWord (diagFin (d := d) (n := n) (m := m) A11 A22) w) := by
          simp [hDiagEval]


/-- Final `SameMPV` statement: upper-triangular off-diagonal blocks are irrelevant for MPVs. -/
theorem sameMPV_upperFin_diagFin
    (A11 : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (A12 : Fin d → Matrix (Fin n) (Fin m) ℂ)
    (A22 : Fin d → Matrix (Fin m) (Fin m) ℂ) :
    SameMPV (upperFin (d := d) (n := n) (m := m) A11 A12 A22)
      (diagFin (d := d) (n := n) (m := m) A11 A22) := by
  intro N σ
  simpa using
    mpv_upperFin_eq_mpv_diagFin (d := d) (n := n) (m := m) A11 A12 A22 (N := N) σ

end BlockTriangular

end MPSTensor
