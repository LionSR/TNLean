/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.Word
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Complex.Circle
import TNLean.Algebra.FinStepOrbit
import TNLean.MPS.Core.CanonicalNormalization

/-!
# Products of cyclically rephased tensor letters

The first equality in arXiv:1708.00029, `eq:Aprime-is-cPA`, expresses a word
of the rephased tensor as a sum over cyclic sectors. Its coefficient is the
product of the phases encountered along the word. We use the source's
projector convention `P u * A i = A i * P (u + 1)`.

## Main statements

* `MPSTensor.mul_evalWord_sectorPhaseTensor`: the phase product in one sector.
* `MPSTensor.evalWord_sectorPhaseTensor`: the sum over all sectors.
* `MPSTensor.isLeftCanonical_sectorPhaseTensor`: unit phases preserve left canonicality.
* `MPSTensor.exists_isLeftCanonical_evalWord_eq_sum_orbit_phases`: prescribed roots on
  step orbits are realized by a left-canonical rephasing.

The word identities allow arbitrary complex coefficients. The final existence theorem
constructs unit phases from the prescribed roots on the step-`p` orbits. Canonicalization
and the blocked equal-case theorem are separate parts of the root construction in
Theorem 4.1.
-/

open scoped BigOperators Matrix

open Fin.NatCast

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

/-- Unit-modulus sector phases preserve left-canonical normalization. This supplies
trace preservation for the rephasing before `eq:Aprime-is-cPA` in arXiv:1708.00029,
Theorem 4.1, when the original block is left canonical. -/
theorem isLeftCanonical_sectorPhaseTensor (A : MPSTensor d D)
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ) (c : Fin m → ℂ)
    (hP : ∀ u v, P u * P v = if u = v then P u else 0)
    (hHerm : ∀ u, (P u)ᴴ = P u) (hSum : ∑ u, P u = 1)
    (hc : ∀ u, ‖c u‖ = 1) (hA : IsLeftCanonical A) :
    IsLeftCanonical (sectorPhaseTensor A P c) := by
  have hc' (u) : (starRingEnd ℂ) (c u) * c u = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hc u]
    norm_num
  have hU : (∑ u, c u • P u)ᴴ * (∑ u, c u • P u) = 1 := by
    simp [mul_comm _ ((starRingEnd ℂ) _), Matrix.conjTranspose_sum,
      Matrix.conjTranspose_smul, hHerm, Matrix.sum_mul, Matrix.mul_sum,
      smul_smul, hP, hc', hSum]
  have heq (i) : sectorPhaseTensor A P c i = (∑ u, c u • P u) * A i := by
    simp [sectorPhaseTensor, Matrix.sum_mul]
  have hi (i) : (sectorPhaseTensor A P c i)ᴴ * sectorPhaseTensor A P c i =
      (A i)ᴴ * A i := by
    rw [heq, Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (∑ u, c u • P u)ᴴ, hU, Matrix.one_mul]
  simpa only [IsLeftCanonical, Kraus.IsTP, hi] using hA

/-- Redistribute a root of unity on each step orbit into unit phases on the individual
cyclic sectors, preserving left canonicality and realizing the required blocked tensor.
Source: arXiv:1708.00029, `eq:Aprime-is-cPA` and its preceding construction. -/
theorem exists_isLeftCanonical_evalWord_eq_sum_orbit_phases [NeZero m]
    (A : MPSTensor d D) (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hP : ∀ u v, P u * P v = if u = v then P u else 0)
    (hHerm : ∀ u, (P u)ᴴ = P u) (hSum : ∑ u, P u = 1)
    (hShift : ∀ u i, P u * A i = A i * P (u + 1)) (hA : IsLeftCanonical A)
    (p : ℕ) (c : Fin (m.gcd p) → ℂ) (hc : ∀ a, c a ^ (m / m.gcd p) = 1) :
    ∃ A' : MPSTensor d D, IsLeftCanonical A' ∧ ∀ w : List (Fin d), w.length = p →
      Kraus.evalWord A' w = ∑ u,
        c ((Fin.stepOrbitEquiv m p (Nat.pos_of_ne_zero (NeZero.ne m))).symm u).1 •
          (P u * Kraus.evalWord A w) := by
  have hq : 0 < m / m.gcd p :=
    Nat.div_gcd_pos_of_pos_left p (Nat.pos_of_ne_zero (NeZero.ne m))
  let cc : Fin (m.gcd p) → Circle := fun a =>
    ⟨c a, by
      simpa [Submonoid.unitSphere] using
        Complex.norm_eq_one_of_pow_eq_one (hc a) (Nat.ne_of_gt hq)⟩
  have hcc (a) : cc a ^ (m / m.gcd p) = 1 := by
    apply Circle.coe_injective
    change c a ^ (m / m.gcd p) = 1
    exact hc a
  obtain ⟨b, hb⟩ := Fin.exists_stepOrbit_phases m p cc hcc
  refine ⟨sectorPhaseTensor A P (fun u => (b u : ℂ)),
    isLeftCanonical_sectorPhaseTensor A P _ hP hHerm hSum (fun u => Circle.norm_coe _) hA, ?_⟩
  intro w hw
  rw [evalWord_sectorPhaseTensor A P _ hP hSum hShift]
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  have hp := congrArg Circle.coeHom (hb u)
  simp only [map_prod] at hp
  change (∏ k ∈ Finset.range p, (b (u + (↑k : Fin m)) : ℂ)) =
    c ((Fin.stepOrbitEquiv m p (Nat.pos_of_ne_zero (NeZero.ne m))).symm u).1 at hp
  simpa only [nsmul_one, hw] using hp

end MPSTensor
