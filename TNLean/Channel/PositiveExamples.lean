/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.HermitianHelpers
import TNLean.Algebra.TracePairing
import TNLean.Channel.Basic
import TNLean.Channel.ChoiJamiolkowski

/-!
# Examples of positive maps

This file records elementary positive maps from Wolf Chapter 3.

## Main declarations

* `Matrix.reductionMap`: the reduction map
  \(X \mapsto \operatorname{tr}(X) I - k^{-1}X\).
* `Matrix.reductionMap_one_isPositiveMap`: the case \(k=1\) is positive.
* `Matrix.traceAdjointMap_reductionMap`: the reduction map is self-dual for
  the trace pairing.
* `ChoiJamiolkowski.choiMatrix_reductionMap`: Choi matrix of the reduction map.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 3,
  Example 3.1][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

namespace Matrix

/-- **Wolf Chapter 3, Example 3.1.** The reduction map
\(T_k(X)=\operatorname{tr}(X)I-k^{-1}X\) on \(M_D(\mathbb C)\). -/
noncomputable def reductionMap (D k : ℕ) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ where
  toFun X := Matrix.trace X • (1 : Matrix (Fin D) (Fin D) ℂ) - ((k : ℂ)⁻¹) • X
  map_add' := by
    intro X Y
    ext i j
    simp [Matrix.trace_add, add_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  map_smul' := by
    intro c X
    ext i j
    simp [Matrix.trace_smul, smul_smul, mul_comm, mul_left_comm, mul_assoc]
    ring

@[simp]
theorem reductionMap_apply (D k : ℕ) (X : Matrix (Fin D) (Fin D) ℂ) :
    reductionMap D k X =
      Matrix.trace X • (1 : Matrix (Fin D) (Fin D) ℂ) - ((k : ℂ)⁻¹) • X :=
  rfl

/-- The reduction map \(T_1(X)=\operatorname{tr}(X)I-X\) is positive. -/
theorem reductionMap_one_isPositiveMap {D : ℕ} [NeZero D] :
    IsPositiveMap (reductionMap D 1) := by
  haveI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero (NeZero.ne D))
  intro X hX
  simpa [reductionMap] using
    (Matrix.PosSemidef.trace_smul_one_sub_self_posSemidef hX)

/-- **Wolf Chapter 3, Example 3.1, equation (3.18).** The reduction map is
self-dual for the bilinear trace pairing:
\[
  \operatorname{tr}(T_k(\rho)X)=\operatorname{tr}(\rho T_k(X)).
\]
-/
theorem traceAdjointMap_reductionMap (D k : ℕ) :
    Matrix.traceAdjointMap (reductionMap D k) = reductionMap D k := by
  classical
  apply LinearMap.ext
  intro ρ
  refine sub_eq_zero.mp ((Matrix.trace_mul_right_eq_zero_iff
    (M := Matrix.traceAdjointMap (reductionMap D k) ρ - reductionMap D k ρ)).1 ?_)
  intro X
  rw [Matrix.sub_mul, Matrix.trace_sub]
  have hleft :
      Matrix.trace (Matrix.traceAdjointMap (reductionMap D k) ρ * X) =
        Matrix.trace (ρ * reductionMap D k X) :=
    Matrix.trace_traceAdjointMap_mul (reductionMap D k) ρ X
  rw [hleft, sub_eq_zero]
  simp [reductionMap, Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub,
    Matrix.trace_smul, mul_comm]

end Matrix

namespace ChoiJamiolkowski

variable {D : ℕ}

/-- The Choi matrix of the reduction map
\(T_k(X)=\operatorname{tr}(X)I-k^{-1}X\) is
\(D^{-1}I-k^{-1}|\Omega\rangle\langle\Omega|\). -/
theorem choiMatrix_reductionMap [NeZero D] (k : ℕ) :
    choiMatrix (Matrix.reductionMap D k) =
      ((D : ℂ)⁻¹) • (1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) -
        ((k : ℂ)⁻¹) • Matrix.omegaProj D := by
  classical
  have hDpos : (0 : ℝ) < D := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne D)
  have hcoeff :
      (D : ℂ)⁻¹ = (((D : ℝ).sqrt : ℂ)⁻¹ * (((D : ℝ).sqrt : ℂ)⁻¹)) := by
    rw [← _root_.mul_inv_rev]
    congr
    have hsqrt : (D : ℝ) = (D : ℝ).sqrt * (D : ℝ).sqrt := by
      exact (by
        nth_rw 1 [← Real.sq_sqrt hDpos.le]
        ring)
    exact_mod_cast hsqrt
  ext x y
  rcases x with ⟨i, a⟩
  rcases y with ⟨j, b⟩
  by_cases hij : i = j <;> by_cases hab : a = b <;>
    by_cases hia : i = a <;> by_cases hjb : j = b <;>
      simp_all [choiMatrix_apply, Matrix.reductionMap, omegaSlice_eq_single,
        Matrix.omegaProj_apply, Matrix.omegaVec_apply, eq_comm]

end ChoiJamiolkowski
