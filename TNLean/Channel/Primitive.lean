/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.OperatorNormConvergence
import TNLean.Analysis.SpectralRadiusPowerDecay
import TNLean.Channel.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Primitive Quantum Channels

This file contains basic formalization toward the theory of **primitive** quantum channels
(Wolf Section 6.3, Theorem 6.7: equivalent characterizations of primitivity).

We formalize the **rank-one projection** onto a fixed point and the algebraic decomposition
\[
  E^n = P + (E-P)^n \qquad (n \ge 1)
\]
where `P` is the fixed-point projection. This decomposition is the algebraic core
of Wolf Theorem 6.7 item 3 → item 1: a complementary transfer-map gap for
`E - P` ensures `(E - P)^n → 0`, so `E^n → P`, giving convergence to the
unique fixed state.

## Main definitions

* `fixedPointProj`: rank-one projection `X ↦ (tr X / tr ρ) • ρ` onto a fixed state `ρ`

## Main results

* `fixedPointProj_idempotent`: `P ∘ P = P`
* `pow_succ_eq_fixedPointProj_add_compl_pow`: `E^(n+1) = P + (E-P)^(n+1)` for all `n`
* `pow_eq_fixedPointProj_add_compl_pow`: same for all `n ≥ 1`
* `MPSTensor.linearMap_trace_pow_tendsto_one_of_spectralRadius_compl_lt_one`:
  convergence of the traces to one under a complementary spectral-radius gap

## Notation

Within `section ComplementaryDecomposition`, we use local notation:
* `P` for `fixedPointProj ρ htr`
* `N` for `E - P` (the complementary part)

## References
* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Section 6.3
  Theorem 6.7][Wolf2012QChannels]
-/

open Matrix
open scoped Matrix ComplexOrder NNReal ENNReal Topology Matrix.Norms.Operator

variable {D : ℕ}

section FixedPointProjection

/-- The rank-one projection onto `ρ`, normalized by `trace ρ`.

We keep the hypothesis `trace ρ ≠ 0` as a parameter so later lemmas can use it to
cancel denominators. -/
noncomputable def fixedPointProj (ρ : Matrix (Fin D) (Fin D) ℂ) (_htr : trace ρ ≠ 0) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ where
  toFun X := (trace X / trace ρ) • ρ
  map_add' X Y := by simp only [Matrix.trace_add, add_div, add_smul]
  map_smul' c X := by
    simp only [Matrix.trace_smul, smul_eq_mul, mul_div_assoc, smul_smul, RingHom.id_apply]

/-- The fixed-point projection is idempotent. -/
theorem fixedPointProj_idempotent (ρ : Matrix (Fin D) (Fin D) ℂ) (htr : trace ρ ≠ 0)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    fixedPointProj ρ htr (fixedPointProj ρ htr X) = fixedPointProj ρ htr X := by
  simp [fixedPointProj, div_eq_mul_inv, htr]

/-- The trace of `fixedPointProj ρ` as a linear endomorphism is 1.

The proof expresses `fixedPointProj ρ htr` as the rank-one map `X ↦ f(X) • ρ`
for `f := (trace ρ)⁻¹ • traceLinearMap`, then applies the rank-one trace formula. -/
theorem fixedPointProj_trace (ρ : Matrix (Fin D) (Fin D) ℂ) (htr : trace ρ ≠ 0) :
    LinearMap.trace ℂ (Matrix (Fin D) (Fin D) ℂ) (fixedPointProj ρ htr) = (1 : ℂ) := by
  have hP : fixedPointProj ρ htr =
      ((trace ρ)⁻¹ • Matrix.traceLinearMap (Fin D) ℂ ℂ).smulRight ρ := by
    ext X
    simp [fixedPointProj, Matrix.traceLinearMap_apply, div_eq_mul_inv, mul_comm]
  simp [hP, Matrix.traceLinearMap_apply, htr]

end FixedPointProjection

section ComplementaryDecomposition

variable (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
variable {ρ : Matrix (Fin D) (Fin D) ℂ} (htr : trace ρ ≠ 0)

-- `P` is the rank-one fixed-point projection; `N = E - P` is the complementary part.
local notation "P" => fixedPointProj (D := D) ρ htr
local notation "N" => E - P

/-- The fixed-point projection is idempotent as an endomorphism: `P * P = P`. -/
theorem fixedPointProj_mul_self : P * P = P := by
  ext X
  simp [Module.End.mul_apply, fixedPointProj_idempotent]

/-- For `P := fixedPointProj ρ` and `N := E - P`, we have `E^(n+1) = P + N^(n+1)`.

This is the algebraic core of primitive convergence: the dynamics splits into the fixed-point
part `P` and a complementary part `N` that decays under a complementary transfer-map
gap hypothesis. -/
theorem pow_succ_eq_fixedPointProj_add_compl_pow
    (hTP : IsTracePreservingMap E) (hρ : E ρ = ρ) (n : ℕ) :
    E ^ (n + 1) = P + N ^ (n + 1) := by
  induction n with
  | zero => simp only [Nat.zero_add, pow_one, add_sub_cancel]
  | succ n ih =>
      have hPP : P * P = P := fixedPointProj_mul_self (ρ := ρ) (htr := htr)
      have hPN : P * N = 0 := by
        ext X
        have hPE : P (E X) = P X := by
          simp [fixedPointProj, hTP X]
        simp [Module.End.mul_apply, hPE, fixedPointProj_idempotent]
      have hNpowP : N ^ (n + 1) * P = 0 :=
        have hNP : N * P = 0 := by
          ext X
          have hEP : E (P X) = P X := by
            simp [fixedPointProj, hρ]
          simp [Module.End.mul_apply, hEP, fixedPointProj_idempotent]
        by
          simp only [pow_succ, mul_assoc, hNP, mul_zero]
      -- Rewrite E^(n+2) = (P + N^(n+1)) * E, then substitute E = P + N on the right factor.
      rw [pow_succ, ih]
      conv_lhs => rhs; rw [show E = P + N from (add_sub_cancel P E).symm]
      simp only [add_mul, mul_add, hPP, hPN, hNpowP, add_zero, zero_add, ← pow_succ]

/-- For `P := fixedPointProj ρ` and `N := E - P`, we have `E^n = P + N^n` for all `n ≥ 1`. -/
theorem pow_eq_fixedPointProj_add_compl_pow
    (hTP : IsTracePreservingMap E) (hρ : E ρ = ρ) {n : ℕ} (hn : 1 ≤ n) :
    E ^ n = P + N ^ n := by
  cases n with
  | zero => omega
  | succ n =>
      simpa using
        pow_succ_eq_fixedPointProj_add_compl_pow (E := E) (ρ := ρ) (htr := htr) hTP hρ n

end ComplementaryDecomposition

namespace MPSTensor

open Filter

attribute [local instance]
  ContinuousLinearMap.toNormedAddCommGroup
  ContinuousLinearMap.toNormedRing
  ContinuousLinearMap.toSeminormedRing
  ContinuousLinearMap.toNormedAlgebra

section TraceConvergence

local notation "V" => Matrix (Fin D) (Fin D) ℂ

/-- Let `P` be the rank-one projection onto a fixed point `ρ` and let `N := E - P`.
If the spectral radius of `N` is less than one, then `trace(E ^ n)` converges to one. -/
theorem linearMap_trace_pow_tendsto_one_of_spectralRadius_compl_lt_one
    [NeZero D]
    (E : V →ₗ[ℂ] V) (ρ : V) (htr : trace ρ ≠ 0)
    (hTP : IsTracePreservingMap E) (hρ : E ρ = ρ)
    (hSpect :
      spectralRadius ℂ
          ((Module.End.toContinuousLinearMap V) (E - fixedPointProj (D := D) ρ htr)) < 1) :
    Tendsto (fun n ↦ (LinearMap.trace ℂ V) (E ^ n)) atTop (𝓝 (1 : ℂ)) := by
  classical
  let : FiniteDimensional ℂ V := by infer_instance
  let : CompleteSpace V := FiniteDimensional.complete ℂ V
  let : Nontrivial V := by infer_instance
  let Φ : (V →ₗ[ℂ] V) ≃ₐ[ℂ] (V →L[ℂ] V) := Module.End.toContinuousLinearMap V
  let : NormedAddCommGroup (V →L[ℂ] V) := ContinuousLinearMap.toNormedAddCommGroup
  let : SeminormedRing (V →L[ℂ] V) := ContinuousLinearMap.toSeminormedRing
  let : NormedRing (V →L[ℂ] V) := ContinuousLinearMap.toNormedRing
  let : NormedSpace ℂ (V →L[ℂ] V) := ContinuousLinearMap.toNormedSpace
  let : NormedAlgebra ℂ (V →L[ℂ] V) := ContinuousLinearMap.toNormedAlgebra
  have : FiniteDimensional ℂ (V →L[ℂ] V) := Φ.toLinearEquiv.finiteDimensional
  have hComplete : CompleteSpace (V →L[ℂ] V) := FiniteDimensional.complete ℂ (V →L[ℂ] V)
  let : CompleteSpace (V →L[ℂ] V) := hComplete
  let P : V →ₗ[ℂ] V := fixedPointProj (D := D) ρ htr
  let N : V →ₗ[ℂ] V := E - P
  have hSpectN : spectralRadius ℂ (Φ N) < 1 := by
    change spectralRadius ℂ
      ((Module.End.toContinuousLinearMap V) (E - fixedPointProj (D := D) ρ htr)) < 1
    simpa [N, P] using hSpect
  have hNpow_clm : Tendsto (fun n ↦ (Φ N) ^ n) atTop (𝓝 0) :=
    @_root_.pow_tendsto_zero_of_spectralRadius_lt_one (V →L[ℂ] V)
      (ContinuousLinearMap.toNormedRing : NormedRing (V →L[ℂ] V)) hComplete
      (ContinuousLinearMap.toNormedAlgebra : NormedAlgebra ℂ (V →L[ℂ] V)) (Φ N) hSpectN
  have hNtrace0' :
      Tendsto (fun n ↦ LinearMap.trace ℂ V ((Φ N) ^ n : V →L[ℂ] V))
        atTop (𝓝 (0 : ℂ)) :=
    ContinuousLinearMap.tendsto_trace_pow_of_tendsto_zero (Φ N) hNpow_clm
  have hNtrace0 : Tendsto (fun n ↦ LinearMap.trace ℂ V (N ^ n)) atTop (𝓝 (0 : ℂ)) := by
    refine Tendsto.congr (fun n ↦ ?_) hNtrace0'
    have hlin : N ^ n = ((Φ N) ^ n : V →L[ℂ] V) :=
      (show ((Φ (N ^ n) : V →L[ℂ] V) : V →ₗ[ℂ] V) = N ^ n from rfl).symm.trans
        (congrArg (fun F : V →L[ℂ] V ↦ (F : V →ₗ[ℂ] V)) (map_pow Φ N n))
    exact (congrArg (LinearMap.trace ℂ V) hlin).symm
  have h_decomp : ∀ᶠ n in atTop, E ^ n = P + N ^ n := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact pow_eq_fixedPointProj_add_compl_pow (E := E) (ρ := ρ) (htr := htr) hTP hρ hn
  have hP_tr : (LinearMap.trace ℂ V) P = (1 : ℂ) := by
    simpa [P] using fixedPointProj_trace (D := D) ρ htr
  have h_main' :
      Tendsto (fun n ↦ (LinearMap.trace ℂ V) P + (LinearMap.trace ℂ V) (N ^ n))
        atTop (𝓝 (1 : ℂ)) := by
    have h := (tendsto_const_nhds :
        Tendsto (fun _ : ℕ ↦ (LinearMap.trace ℂ V) P) atTop
          (𝓝 ((LinearMap.trace ℂ V) P))).add hNtrace0
    simpa [hP_tr] using h
  refine Tendsto.congr' ?_ h_main'
  filter_upwards [h_decomp] with n hn
  simp [hn, hP_tr]

end TraceConvergence

end MPSTensor
