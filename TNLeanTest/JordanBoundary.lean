/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.JordanBoundary

/-!
# Signature and axiom tests for the Jordan boundary example

The formulas hold for arbitrary tensors and all words. Boundary detection
requires both a nonempty word and a nonzero trace at that word.
-/

open MPSTensor.JordanBoundary

variable {d D : ℕ}

example (A : MPSTensor d D) (i : Fin d) :
    tensor A i = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (A i) (A i) 0 (A i)) := rfl

example (A : MPSTensor d D) (i : Fin d) :
    splitTensor A i = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (A i) 0 0 (A i)) := rfl

example : boundary D = Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (0 : Matrix (Fin D) (Fin D) ℂ) 0 1 0) := rfl

example (A : MPSTensor d D) (w : List (Fin d)) :
    Kraus.evalWord (tensor A) w =
      blocks (Kraus.evalWord A w) ((w.length : ℂ) • Kraus.evalWord A w)
        0 (Kraus.evalWord A w) :=
  evalWord_tensor A w

example (A : MPSTensor d D) (w : List (Fin d)) :
    Kraus.evalWord (splitTensor A) w =
      blocks (Kraus.evalWord A w) 0 0 (Kraus.evalWord A w) :=
  evalWord_splitTensor A w

example (A : MPSTensor d D) (w : List (Fin d)) :
    Matrix.trace (Kraus.evalWord (tensor A) w) =
      2 * Matrix.trace (Kraus.evalWord A w) :=
  trace_evalWord_tensor A w

example (A : MPSTensor d D) (w : List (Fin d)) :
    Matrix.trace (Kraus.evalWord (tensor A) w) =
      Matrix.trace (Kraus.evalWord (splitTensor A) w) :=
  periodic_trace_eq A w

example (A : MPSTensor d D) (w : List (Fin d)) :
    Matrix.trace (boundary D * Kraus.evalWord (tensor A) w) =
      (w.length : ℂ) * Matrix.trace (Kraus.evalWord A w) :=
  boundary_trace_tensor A w

example (A : MPSTensor d D) (w : List (Fin d)) :
    Matrix.trace (boundary D * Kraus.evalWord (splitTensor A) w) = 0 :=
  boundary_trace_splitTensor A w

example (A : MPSTensor d D) (w : List (Fin d))
    (hw : w ≠ []) (htr : Matrix.trace (Kraus.evalWord A w) ≠ 0) :
    Matrix.trace (boundary D * Kraus.evalWord (tensor A) w) ≠
      Matrix.trace (boundary D * Kraus.evalWord (splitTensor A) w) :=
  boundary_trace_ne A w hw htr

example (A : MPSTensor d D) (w : List (Fin d))
    (hw : w ≠ []) (htr : Matrix.trace (Kraus.evalWord A w) ≠ 0) :
    (∀ v, Matrix.trace (Kraus.evalWord (tensor A) v) =
      Matrix.trace (Kraus.evalWord (splitTensor A) v)) ∧
    (fun v => Matrix.trace (boundary D * Kraus.evalWord (tensor A) v)) ≠
      (fun v => Matrix.trace (boundary D * Kraus.evalWord (splitTensor A) v)) :=
  periodic_eq_boundary_ne A w hw htr

-- At length zero the boundary vanishes, even for a tensor with nonzero identity trace.
example (A : MPSTensor d D) :
    Matrix.trace (boundary D * Kraus.evalWord (tensor A) []) = 0 := by
  rw [boundary_trace_tensor]
  simp

-- Zero bond dimension is admitted by the unconditional formulas.
example (A : MPSTensor d 0) (w : List (Fin d)) :
    Matrix.trace (boundary 0 * Kraus.evalWord (tensor A) w) = 0 := by
  rw [boundary_trace_tensor]
  simp [Matrix.trace]

-- The scalar identity tensor supplies a concrete detection witness.
example :
    Matrix.trace (boundary 1 * Kraus.evalWord (tensor (fun _ : Fin 1 => 1)) [0]) ≠
      Matrix.trace (boundary 1 * Kraus.evalWord (splitTensor (fun _ : Fin 1 => 1)) [0]) := by
  apply boundary_trace_ne (fun _ : Fin 1 => 1) [0] (by simp)
  simp

section AxiomChecks
set_option linter.hashCommand false

/-- info: 'MPSTensor.JordanBoundary.evalWord_tensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPSTensor.JordanBoundary.evalWord_tensor

/-- info: 'MPSTensor.JordanBoundary.evalWord_splitTensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPSTensor.JordanBoundary.evalWord_splitTensor

/-- info: 'MPSTensor.JordanBoundary.trace_evalWord_tensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPSTensor.JordanBoundary.trace_evalWord_tensor

/-- info: 'MPSTensor.JordanBoundary.periodic_trace_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPSTensor.JordanBoundary.periodic_trace_eq

/-- info: 'MPSTensor.JordanBoundary.boundary_trace_tensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPSTensor.JordanBoundary.boundary_trace_tensor

/-- info: 'MPSTensor.JordanBoundary.boundary_trace_splitTensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPSTensor.JordanBoundary.boundary_trace_splitTensor

/-- info: 'MPSTensor.JordanBoundary.boundary_trace_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPSTensor.JordanBoundary.boundary_trace_ne

/-- info: 'MPSTensor.JordanBoundary.periodic_eq_boundary_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPSTensor.JordanBoundary.periodic_eq_boundary_ne

end AxiomChecks
