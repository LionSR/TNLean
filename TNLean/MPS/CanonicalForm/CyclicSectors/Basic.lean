/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Peripheral.CyclicDecomposition
import TNLean.Channel.Peripheral.Conjugation
import TNLean.MPS.Irreducible.FormII
import TNLean.MPS.Structure.InvariantSubspaceDecomp
import TNLean.MPS.Core.BlockingInfrastructure

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Logic.Equiv.Sum
import Mathlib.Tactic.NoncommRing

/-!
# Basic projection word lemmas for cyclic-sector decompositions

This file contains the projection-word identities used throughout the
cyclic-sector normalization pipeline.

## Main declarations

* `leftSectorTensor`
* `commutes_evalWord_of_commutes_letters`
* `left_mul_evalWord_leftSectorTensor_of_commutes`
* `leftSectorTensor_supported`

## References

* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608, Appendix A]
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Matrix Finset Complex KadisonSchwarz

namespace MPSTensor

variable {d D : ℕ}

section BasicProjectionWordLemmas

/-- Left-multiply every letter by `P`. -/
noncomputable def leftSectorTensor (P : MatrixAlg D) (A : MPSTensor d D) : MPSTensor d D :=
  fun i => P * A i

/-- If `P` commutes with every letter of `A`, then it commutes with every evaluated word. -/
lemma commutes_evalWord_of_commutes_letters
    (P : MatrixAlg D) (A : MPSTensor d D)
    (hComm : ∀ i : Fin d, P * A i = A i * P) :
    ∀ w : List (Fin d), P * evalWord A w = evalWord A w * P := by
  intro w
  induction w with
  | nil =>
      simp only [evalWord, Matrix.one_mul, Matrix.mul_one]
  | cons i w ih =>
      simp only [evalWord]
      calc P * (A i * evalWord A w)
          = A i * (evalWord A w * P) := by
            rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hComm i, Matrix.mul_assoc,
              Matrix.mul_assoc, ih]
        _ = A i * evalWord A w * P := by rw [← Matrix.mul_assoc]

lemma left_mul_evalWord_leftSectorTensor_of_commutes
    (P : MatrixAlg D) (A : MPSTensor d D)
    (hPidem : P * P = P)
    (hComm : ∀ i : Fin d, P * A i = A i * P) :
    ∀ w : List (Fin d),
      P * evalWord (leftSectorTensor P A) w = P * evalWord A w := by
  intro w
  induction w with
  | nil =>
      simp only [evalWord]
  | cons i w ih =>
      simp only [leftSectorTensor, evalWord]
      calc P * (P * A i * evalWord (leftSectorTensor P A) w)
          = P * P * A i * evalWord (leftSectorTensor P A) w := by
            simp only [Matrix.mul_assoc]
        _ = P * A i * evalWord (leftSectorTensor P A) w := by rw [hPidem]
        _ = A i * (P * evalWord (leftSectorTensor P A) w) := by
            rw [← Matrix.mul_assoc, hComm i, Matrix.mul_assoc]
        _ = A i * (P * evalWord A w) := by rw [ih]
        _ = P * (A i * evalWord A w) := by
            rw [← Matrix.mul_assoc, ← hComm i, Matrix.mul_assoc]

/-- A left-sector tensor is supported on the sector projection. -/
lemma leftSectorTensor_supported
    (P : MatrixAlg D) (A : MPSTensor d D)
    (hPidem : P * P = P)
    (hComm : ∀ i : Fin d, P * A i = A i * P) :
    ∀ i : Fin d, P * leftSectorTensor P A i * P = leftSectorTensor P A i := by
  intro i
  simp only [leftSectorTensor]
  calc
    P * (P * A i) * P = P * P * A i * P := by
      simp only [Matrix.mul_assoc]
    _ = P * A i * P := by rw [hPidem]
    _ = P * A i := by rw [hComm i, Matrix.mul_assoc, hPidem]

end BasicProjectionWordLemmas

end MPSTensor
