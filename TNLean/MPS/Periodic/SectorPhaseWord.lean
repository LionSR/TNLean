/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.Word
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Products of cyclically rephased tensor letters

The first equality in arXiv:1708.00029, `eq:Aprime-is-cPA`, expresses a word
of the rephased tensor as a sum over cyclic sectors. Its coefficient is the
product of the phases encountered along the word. We use the source's
projector convention `P u * A i = A i * P (u + 1)`.

## Main statements

* `MPSTensor.mul_evalWord_sectorPhaseTensor`: the phase product in one sector.
* `MPSTensor.evalWord_sectorPhaseTensor`: the sum over all sectors.

These identities allow arbitrary complex coefficients. Choosing unit phases
with the prescribed products on step-`p` orbits is a separate part of the
root construction in Theorem 4.1; it is not assumed or proved here.
-/

open scoped BigOperators

namespace MPSTensor

variable {d D m : ℕ}

/-- Rephase each outgoing cyclic sector, as in arXiv:1708.00029, the definition
of `A'_j` immediately before `eq:Aprime-is-cPA`. -/
noncomputable def sectorPhaseTensor (A : MPSTensor d D)
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ) (c : Fin m → ℂ) : MPSTensor d D :=
  fun i => ∑ u, c u • (P u * A i)

/-- A projection extracts one letter's phase from the sector sum in
arXiv:1708.00029, `eq:Aprime-is-cPA`. -/
theorem mul_sectorPhaseTensor (A : MPSTensor d D)
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ) (c : Fin m → ℂ)
    (hP : ∀ u v, P u * P v = if u = v then P u else 0)
    (u : Fin m) (i : Fin d) :
    P u * sectorPhaseTensor A P c i = c u • (P u * A i) := by
  simp [sectorPhaseTensor, Matrix.mul_sum, ← Matrix.mul_assoc, hP]

/-- The phase accumulated along a word is the product of its successive sector
phases (arXiv:1708.00029, first equality of `eq:Aprime-is-cPA`). -/
theorem mul_evalWord_sectorPhaseTensor [NeZero m] (A : MPSTensor d D)
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ) (c : Fin m → ℂ)
    (hP : ∀ u v, P u * P v = if u = v then P u else 0)
    (hShift : ∀ u i, P u * A i = A i * P (u + 1))
    (w : List (Fin d)) (u : Fin m) :
    P u * Kraus.evalWord (sectorPhaseTensor A P c) w =
      (∏ k ∈ Finset.range w.length, c (u + k • (1 : Fin m))) • (P u * Kraus.evalWord A w) := by
  induction w generalizing u with
  | nil => simp
  | cons i w ih =>
    rw [Kraus.evalWord_cons, ← Matrix.mul_assoc, mul_sectorPhaseTensor A P c hP,
      Matrix.smul_mul, hShift, Matrix.mul_assoc, ih]
    simp only [Matrix.mul_smul, ← Matrix.mul_assoc, ← hShift, smul_smul,
      Kraus.evalWord_cons, List.length_cons, Finset.prod_range_succ',
      add_nsmul, one_nsmul, zero_nsmul, add_zero, add_assoc,
      add_comm, mul_comm]

/-- Summing the sector identities gives the first equality of
arXiv:1708.00029, `eq:Aprime-is-cPA`, for an arbitrary word. -/
theorem evalWord_sectorPhaseTensor [NeZero m] (A : MPSTensor d D)
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ) (c : Fin m → ℂ)
    (hP : ∀ u v, P u * P v = if u = v then P u else 0)
    (hSum : ∑ u, P u = 1)
    (hShift : ∀ u i, P u * A i = A i * P (u + 1))
    (w : List (Fin d)) :
    Kraus.evalWord (sectorPhaseTensor A P c) w =
      ∑ u, (∏ k ∈ Finset.range w.length, c (u + k • (1 : Fin m))) •
        (P u * Kraus.evalWord A w) := by
  simp only [← mul_evalWord_sectorPhaseTensor A P c hP hShift,
    ← Finset.sum_mul, hSum, Matrix.one_mul]

end MPSTensor
