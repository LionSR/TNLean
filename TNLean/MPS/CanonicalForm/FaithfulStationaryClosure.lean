/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.ProjectorClosure
import TNLean.MPS.Core.CanonicalNormalization
import QICLean.Channel.FixedPoint.Algebra
import QICLean.Channel.KrausMap

/-!
# Invariant-projector closure from a faithful stationary density

A left-canonical tensor whose transfer map has a positive-definite fixed point
has no one-way invariant subspace: every invariant orthogonal projection reduces
all tensor letters. This supplies a sufficient hypothesis for the invariant-
projector closure condition of CPSV16, lines 253--254. The hypothesis is stated
explicitly and is not inferred from periodic equality.

The proof is the finite-dimensional stationary-weight argument behind Wolf,
Proposition 6.11 (subharmonic projections), followed by Theorem 6.13 (fixed
projections commute with the Kraus operators).
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- A right-invariant projection reduces a left-canonical tensor with a faithful
stationary density. This is the stationary-weight specialization of Wolf
Proposition 6.11 and the projection case of Wolf Theorem 6.13. -/
theorem commutes_of_leftCanonical_of_posDef_fixedPoint_of_lowerZero
    (A : MPSTensor d D) (hA : IsLeftCanonical A)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef)
    (hFix : Kraus.map A ρ = ρ)
    {P : Matrix (Fin D) (Fin D) ℂ} (hP : IsOrthogonalProjection P)
    (hLower : ∀ i : Fin d, (1 - P) * A i * P = 0) :
    ∀ i : Fin d, P * A i = A i * P := by
  have hAP (i : Fin d) : A i * P = P * A i * P := by
    apply eq_of_sub_eq_zero
    calc
      A i * P - P * A i * P = (1 - P) * A i * P := by noncomm_ring
      _ = 0 := hLower i
  have hPstar : Pᴴ = P := hP.1.eq
  have hPAstar (i : Fin d) : P * (A i)ᴴ = P * (A i)ᴴ * P := by
    have h := congrArg Matrix.conjTranspose (hAP i)
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hPstar, Matrix.mul_assoc] using h
  have hPadj : P * Kraus.adjointMap A P = P := by
    calc
      P * Kraus.adjointMap A P = ∑ i : Fin d, P * (A i)ᴴ * P * A i := by
        simp only [Kraus.adjointMap, Matrix.mul_sum, Matrix.mul_assoc]
      _ = ∑ i : Fin d, P * (A i)ᴴ * A i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← hPAstar i]
      _ = P * (∑ i : Fin d, (A i)ᴴ * A i) := by
        simp only [Matrix.mul_sum, Matrix.mul_assoc]
      _ = P := by rw [hA, Matrix.mul_one]
  have hadjPstar : (Kraus.adjointMap A P)ᴴ = Kraus.adjointMap A P := by
    simp only [Kraus.adjointMap, Matrix.conjTranspose_sum,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hPstar,
      Matrix.mul_assoc]
  have hadjP : Kraus.adjointMap A P * P = P := by
    have h := congrArg Matrix.conjTranspose hPadj
    simpa only [Matrix.conjTranspose_mul, hPstar, hadjPstar] using h
  have hgapEq : Kraus.adjointMap A P - P =
      (1 - P) * Kraus.adjointMap A P * (1 - P) := by
    have hPP : P * P = P := hP.2
    noncomm_ring [hPadj, hadjP, hPP]
  have hgap : (Kraus.adjointMap A P - P).PosSemidef := by
    rw [hgapEq]
    have hPos : (Kraus.adjointMap A P).PosSemidef := by
      have hPos' := Kraus.isPositiveMap_mapLM (fun i => (A i)ᴴ)
        P (isOrthogonalProjection_posSemidef hP)
      simpa only [Kraus.mapLM_apply, Kraus.adjointMap, Kraus.map,
        Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc] using hPos'
    have hQstar : (1 - P : Matrix (Fin D) (Fin D) ℂ)ᴴ = 1 - P := by
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPstar]
    have hc : ((1 - P)ᴴ * Kraus.adjointMap A P * (1 - P)).PosSemidef :=
      Matrix.PosSemidef.conjTranspose_mul_mul_same hPos
        (1 - P : Matrix (Fin D) (Fin D) ℂ)
    rw [hQstar] at hc
    exact hc
  have htrace : Matrix.trace (ρ * (Kraus.adjointMap A P - P)) = 0 := by
    rw [Matrix.mul_sub, Matrix.trace_sub]
    have ht := Kraus.trace_mul_map_eq_trace_adjointMap_mul A P ρ
    rw [hFix] at ht
    rw [Matrix.trace_mul_comm ρ (Kraus.adjointMap A P), ← ht,
      Matrix.trace_mul_comm P ρ, sub_self]
  have hAdjFix : Kraus.adjointMap A P = P :=
    sub_eq_zero.mp (Matrix.posSemidef_eq_zero_of_posDef_trace_mul_eq_zero hgap hρ htrace)
  apply Kraus.fixedPoint_commutes_kraus A hA
  · exact hAdjFix
  · change Kraus.adjointMap A (Pᴴ * P) = Pᴴ * P
    simpa only [hPstar, hP.2] using hAdjFix

/-- Left-canonical normalization and a faithful stationary density imply the
invariant-projector closure condition used in CPSV16, lines 253--254.
This is a sufficient criterion with the stationary-density hypothesis stated
explicitly, rather than a restatement of the source's unrestricted criterion. -/
theorem hasInvariantProjectorClosure_of_leftCanonical_of_posDef_fixedPoint
    (A : MPSTensor d D) (hA : IsLeftCanonical A)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef)
    (hFix : Kraus.map A ρ = ρ) : HasInvariantProjectorClosure A := by
  intro P hP hLeft i
  have hLower : ∀ j : Fin d, (1 - (1 - P)) * A j * (1 - P) = 0 := by
    intro j
    have h := hLeft j
    have hPAP : P * A j * P = P * A j := h.symm
    noncomm_ring [hPAP]
  have hComm := commutes_of_leftCanonical_of_posDef_fixedPoint_of_lowerZero
    A hA hρ hFix hP.one_sub hLower i
  have hPA : P * A i = A i * P := by
    apply sub_right_inj.mp
    simpa only [sub_mul, mul_sub, one_mul, mul_one] using hComm
  calc
    A i * P = P * A i := hPA.symm
    _ = P * A i * P := hLeft i

end MPSTensor
