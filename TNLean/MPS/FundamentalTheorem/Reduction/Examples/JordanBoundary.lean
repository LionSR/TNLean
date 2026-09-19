/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.Word
import QICLean.Algebra.TraceReindex
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# A Jordan extension detected by a virtual boundary

For any tensor `A`, put `Bⁱ = [[Aⁱ, Aⁱ], [0, Aⁱ]]` and
`Q = [[0, 0], [I, 0]]`. Every word, including the empty word, satisfies
`Bʷ = [[Aʷ, |w| Aʷ], [0, Aʷ]]`. Its periodic trace equals the trace of
`A ⊕ A`, whereas its `Q`-boundary trace is `|w| tr(Aʷ)` and the split
boundary trace is zero. A nonempty word with nonzero trace therefore
separates the two boundary families. No normality assumption is needed.

Source: *The asymmetric fundamental theorem and boundary matrices*, in
`Notes/OpenProblemsTN/followup/asymmetric_mpoa/sections/rfp_symmetry_bridge.tex`.
-/

open scoped Matrix

noncomputable section

namespace MPSTensor.JordanBoundary

variable {d D : ℕ}

/-- Two-by-two blocks in the standard order on `Fin (D + D)`. -/
def blocks (X Y Z W : Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin (D + D)) (Fin (D + D)) ℂ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks X Y Z W)

private theorem blocks_mul (X Y Z W X' Y' Z' W' : Matrix (Fin D) (Fin D) ℂ) :
    blocks X Y Z W * blocks X' Y' Z' W' =
      blocks (X * X' + Y * Z') (X * Y' + Y * W')
        (Z * X' + W * Z') (Z * Y' + W * W') := by
  unfold blocks
  rw [← Matrix.fromBlocks_multiply]
  exact Matrix.reindexLinearEquiv_mul ℂ ℂ finSumFinEquiv finSumFinEquiv
    finSumFinEquiv _ _

private theorem blocks_one : blocks (1 : Matrix (Fin D) (Fin D) ℂ) 0 0 1 = 1 := by
  simp [blocks, Matrix.fromBlocks_one]

private theorem trace_blocks (X Y Z W : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.trace (blocks X Y Z W) = Matrix.trace X + Matrix.trace W := by
  rw [blocks, Matrix.trace_reindex]
  simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type]

/-- The tensor with a Jordan block on the multiplicity space at every letter. -/
def tensor (A : MPSTensor d D) : MPSTensor d (D + D) :=
  fun i => blocks (A i) (A i) 0 (A i)

/-- The split tensor `A ⊕ A` in the same coordinates. -/
def splitTensor (A : MPSTensor d D) : MPSTensor d (D + D) :=
  fun i => blocks (A i) 0 0 (A i)

/-- The boundary with identity in the lower-left block. -/
def boundary (D : ℕ) : Matrix (Fin (D + D)) (Fin (D + D)) ℂ :=
  blocks 0 0 1 0

/-- The upper-right word block counts every letter, including repeated letters. -/
theorem evalWord_tensor (A : MPSTensor d D) (w : List (Fin d)) :
    Kraus.evalWord (tensor A) w =
      blocks (Kraus.evalWord A w) ((w.length : ℂ) • Kraus.evalWord A w)
        0 (Kraus.evalWord A w) := by
  induction w with
  | nil => simp [blocks_one]
  | cons i w ih =>
    simp only [Kraus.evalWord_cons, tensor, ih, blocks_mul, List.length_cons,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_smul,
      Nat.cast_add, Nat.cast_one, add_smul, one_smul, smul_zero]

/-- Evaluation of the split tensor has zero off-diagonal blocks, also at length zero. -/
theorem evalWord_splitTensor (A : MPSTensor d D) (w : List (Fin d)) :
    Kraus.evalWord (splitTensor A) w =
      blocks (Kraus.evalWord A w) 0 0 (Kraus.evalWord A w) := by
  induction w with
  | nil => simp [blocks_one]
  | cons i w ih =>
    simp [Kraus.evalWord_cons, splitTensor, ih, blocks_mul]

/-- Periodic traces count the two copies and do not see the upper-right block. -/
theorem trace_evalWord_tensor (A : MPSTensor d D) (w : List (Fin d)) :
    Matrix.trace (Kraus.evalWord (tensor A) w) =
      2 * Matrix.trace (Kraus.evalWord A w) := by
  rw [evalWord_tensor, trace_blocks, two_mul]

/-- The Jordan extension and the split tensor have equal periodic traces. -/
theorem periodic_trace_eq (A : MPSTensor d D) (w : List (Fin d)) :
    Matrix.trace (Kraus.evalWord (tensor A) w) =
      Matrix.trace (Kraus.evalWord (splitTensor A) w) := by
  rw [evalWord_tensor, evalWord_splitTensor, trace_blocks, trace_blocks]

/-- The lower-left boundary reads the upper-right word block. -/
theorem boundary_trace_tensor (A : MPSTensor d D) (w : List (Fin d)) :
    Matrix.trace (boundary D * Kraus.evalWord (tensor A) w) =
      (w.length : ℂ) * Matrix.trace (Kraus.evalWord A w) := by
  rw [evalWord_tensor, boundary, blocks_mul, trace_blocks]
  simp

/-- The same boundary vanishes on every split word. -/
theorem boundary_trace_splitTensor (A : MPSTensor d D) (w : List (Fin d)) :
    Matrix.trace (boundary D * Kraus.evalWord (splitTensor A) w) = 0 := by
  rw [evalWord_splitTensor, boundary, blocks_mul, trace_blocks]
  simp

/-- A nonempty word with nonzero trace distinguishes the boundary coefficients. -/
theorem boundary_trace_ne (A : MPSTensor d D) (w : List (Fin d))
    (hw : w ≠ []) (htr : Matrix.trace (Kraus.evalWord A w) ≠ 0) :
    Matrix.trace (boundary D * Kraus.evalWord (tensor A) w) ≠
      Matrix.trace (boundary D * Kraus.evalWord (splitTensor A) w) := by
  rw [boundary_trace_tensor, boundary_trace_splitTensor]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (by simpa using hw)) htr

/-- Equal periodic trace families can have different families at a fixed boundary.
The detection hypothesis supplies an explicit nonempty word with nonzero trace. -/
theorem periodic_eq_boundary_ne (A : MPSTensor d D) (w : List (Fin d))
    (hw : w ≠ []) (htr : Matrix.trace (Kraus.evalWord A w) ≠ 0) :
    (∀ v, Matrix.trace (Kraus.evalWord (tensor A) v) =
      Matrix.trace (Kraus.evalWord (splitTensor A) v)) ∧
    (fun v => Matrix.trace (boundary D * Kraus.evalWord (tensor A) v)) ≠
      (fun v => Matrix.trace (boundary D * Kraus.evalWord (splitTensor A) v)) := by
  refine ⟨periodic_trace_eq A, ?_⟩
  intro h
  exact boundary_trace_ne A w hw htr (congrFun h w)

end MPSTensor.JordanBoundary
