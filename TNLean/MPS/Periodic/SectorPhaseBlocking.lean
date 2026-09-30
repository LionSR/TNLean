/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.SectorPhaseWord
import TNLean.MPS.Periodic.StepOrbitSectors

/-!
# Absorbing an orbitwise phase into a blocked tensor root

The orbit phases in arXiv:1708.00029, `eq:ZPA-is-cPA`, can be redistributed
among the original cyclic sectors to obtain `A'` with `A'^(p) = Z A^(p)`.
This is `eq:Aprime-is-cPA` and the comparison following it, lines 778–807.
Unitary conjugation then gives the target blocked tensor while preserving
left canonicality, as in lines 807–810.

These results take the displayed orbit action as input. They do not construct
the periodic decomposition of a blocked tensor or its equal-case multiplicity
gauge; those are the preceding steps of the corrected forward theorem.
-/

open scoped BigOperators Matrix
namespace MPSTensor

variable {d D m : ℕ} [NeZero m]

private theorem sum_orbit_weighted (P : Fin m → Matrix (Fin D) (Fin D) ℂ) (p : ℕ)
    (c : Fin (m.gcd p) → ℂ) (X : Matrix (Fin D) (Fin D) ℂ) :
    (∑ u, c ((Fin.stepOrbitEquiv m p (Nat.pos_of_ne_zero (NeZero.ne m))).symm u).1 •
      (P u * X)) = ∑ a, c a • (stepOrbitProjection P p a * X) := by
  rw [← (Fin.stepOrbitEquiv m p (Nat.pos_of_ne_zero (NeZero.ne m))).sum_comp
    (fun u ↦ c ((Fin.stepOrbitEquiv m p (Nat.pos_of_ne_zero (NeZero.ne m))).symm u).1 •
      (P u * X))]
  simp [stepOrbitProjection, Fintype.sum_prod_type, Finset.sum_mul, Finset.smul_sum]

/-- Absorb the orbitwise action of `Z` into unit phases on the original letters.
The resulting tensor remains left-canonical and blocks to `Z A^(p)`.
Source: arXiv:1708.00029, `eq:ZPA-is-cPA`, `eq:Aprime-is-cPA`, lines 778–807. -/
theorem exists_isLeftCanonical_blockTensor_eq_of_orbit_action
    (A : MPSTensor d D) (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hP : ∀ u v, P u * P v = if u = v then P u else 0)
    (hHerm : ∀ u, (P u)ᴴ = P u) (hSum : ∑ u, P u = 1)
    (hShift : ∀ u i, P u * A i = A i * P (u + 1)) (hA : IsLeftCanonical A)
    (p : ℕ) (c : Fin (m.gcd p) → ℂ) (hc : ∀ a, c a ^ (m / m.gcd p) = 1)
    (Z : Matrix (Fin D) (Fin D) ℂ)
    (hZ : ∀ a i, Z * (stepOrbitProjection P p a * blockTensor A p i) =
      c a • (stepOrbitProjection P p a * blockTensor A p i)) :
    ∃ A' : MPSTensor d D, IsLeftCanonical A' ∧
      blockTensor A' p = fun i ↦ Z * blockTensor A p i := by
  obtain ⟨A', hA', hword⟩ := exists_isLeftCanonical_evalWord_eq_sum_orbit_phases
    A P hP hHerm hSum hShift hA p c hc
  refine ⟨A', hA', ?_⟩
  funext i
  change Kraus.evalWord A' (wordOfBlock d p i) = _
  rw [hword _ (length_wordOfBlock d p i)]
  change (∑ u, c ((Fin.stepOrbitEquiv m p (Nat.pos_of_ne_zero (NeZero.ne m))).symm u).1 •
    (P u * blockTensor A p i)) = _
  rw [sum_orbit_weighted]
  simp only [← hZ, ← Finset.mul_sum, ← Finset.sum_mul, sum_stepOrbitProjection,
    hSum, Matrix.one_mul]

/-- Unitary conjugation of a blocked tensor lifts to a left-canonical root at the
original physical dimension. Source: arXiv:1708.00029, lines 807–810,
where the final root is `Uᴴ A′ U`. -/
theorem exists_isLeftCanonical_blockTensor_eq_of_unitary_conj
    (A : MPSTensor d D) (p : ℕ) (hA : IsLeftCanonical A)
    (C : MPSTensor (blockPhysDim d p) D)
    (U : Matrix (Fin D) (Fin D) ℂ) (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (he : ∀ i, blockTensor A p i = U * C i * Uᴴ) :
    ∃ B : MPSTensor d D, IsLeftCanonical B ∧ blockTensor B p = C := by
  let B : MPSTensor d D := fun i ↦ Uᴴ * A i * U
  have hnorm : IsLeftCanonical B := by
    change (∑ i, (Uᴴ * A i * U)ᴴ * (Uᴴ * A i * U)) = 1
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
    simp only [← Matrix.mul_assoc, hU', Matrix.one_mul]
    calc
      ∑ i, Uᴴ * (A i)ᴴ * A i * U = Uᴴ * (∑ i, (A i)ᴴ * A i) * U := by
        rw [Matrix.mul_sum, Matrix.sum_mul]
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hA, Matrix.mul_one, hU]
  have hw (w : List (Fin d)) : Kraus.evalWord B w = Uᴴ * Kraus.evalWord A w * U := by
    induction w with
    | nil => simp [Kraus.evalWord_nil, hU]
    | cons i w ih =>
      rw [Kraus.evalWord_cons, Kraus.evalWord_cons, ih]
      dsimp only [B]
      simp only [Matrix.mul_assoc]
      simp only [← Matrix.mul_assoc, hU', Matrix.one_mul]
  refine ⟨B, hnorm, ?_⟩
  funext i
  change Kraus.evalWord B (wordOfBlock d p i) = _
  rw [hw]
  change Uᴴ * blockTensor A p i * U = _
  rw [he]
  simp only [← Matrix.mul_assoc, hU, Matrix.one_mul]
  rw [Matrix.mul_assoc, hU, Matrix.mul_one]
end MPSTensor
