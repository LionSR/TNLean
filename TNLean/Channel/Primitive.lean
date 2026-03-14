/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Primitive Quantum Channels

This file contains basic infrastructure toward the theory of **primitive** quantum channels
(Wolf §6.3, Theorem 6.7: equivalent characterizations of primitivity).

We formalize the **rank-one projection** onto a fixed point and the algebraic decomposition
\[
  E^n = P + (E-P)^n \qquad (n \ge 1)
\]
where `P` is the fixed-point projection. This decomposition is the algebraic core
of Wolf Thm 6.7 item 3 → item 1: the spectral gap `‖E - P‖ < 1` ensures
`(E - P)^n → 0`, so `E^n → P`, giving convergence to the unique fixed state.

## Main definitions

* `fixedPointProj`: rank-one projection `X ↦ (tr X / tr ρ) • ρ` onto a fixed state `ρ`

## Main results

* `fixedPointProj_idempotent`: `P ∘ P = P`
* `pow_succ_eq_fixedPointProj_add_compl_pow`: `E^(n+1) = P + (E-P)^(n+1)` for all `n`
* `pow_eq_fixedPointProj_add_compl_pow`: same for all `n ≥ 1`

## Notation

Within `section SpectralGapDecomposition`, we use local notation:
* `P` for `fixedPointProj ρ htr`
* `N` for `E - P` (the complementary part)

## References
* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, §6.3 Thm 6.7][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix Finset Filter

variable {D : ℕ}

section FixedPointProjection

/-- The rank-one projection onto `ρ`, normalized by `trace ρ`.

We keep the hypothesis `trace ρ ≠ 0` as a parameter so later lemmas can use it to
cancel denominators. -/
noncomputable def fixedPointProj (ρ : Matrix (Fin D) (Fin D) ℂ) (_htr : trace ρ ≠ 0) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ where
  toFun X := (trace X / trace ρ) • ρ
  map_add' X Y := by simp [add_div, add_smul]
  map_smul' c X := by simp [mul_div_assoc, smul_smul]

theorem fixedPointProj_idempotent (ρ : Matrix (Fin D) (Fin D) ℂ) (htr : trace ρ ≠ 0)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    fixedPointProj ρ htr (fixedPointProj ρ htr X) = fixedPointProj ρ htr X := by
  simp [fixedPointProj, div_eq_mul_inv, htr]

theorem fixedPointProj_apply_rho (ρ : Matrix (Fin D) (Fin D) ℂ) (htr : trace ρ ≠ 0) :
    fixedPointProj ρ htr ρ = ρ := by
  simp [fixedPointProj, htr]

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

section TracePreservingInteraction

variable (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
variable {ρ : Matrix (Fin D) (Fin D) ℂ} (htr : trace ρ ≠ 0)

/-- If `E(ρ) = ρ`, then `E ∘ fixedPointProj(ρ) = fixedPointProj(ρ)`.

This does not use trace-preservation. -/
theorem E_comp_fixedPointProj (hρ : E ρ = ρ) :
    E.comp (fixedPointProj ρ htr) = fixedPointProj ρ htr := by
  ext X
  simp [fixedPointProj, hρ]

/-- If `E` is trace-preserving, then `fixedPointProj(ρ) ∘ E = fixedPointProj(ρ)`. -/
theorem fixedPointProj_comp_E (hTP : IsTracePreservingMap E) :
    (fixedPointProj ρ htr).comp E = fixedPointProj ρ htr := by
  ext X
  simp [fixedPointProj, hTP X]

end TracePreservingInteraction

section SpectralGapDecomposition

variable (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
variable {ρ : Matrix (Fin D) (Fin D) ℂ} (htr : trace ρ ≠ 0)

-- `P` is the rank-one fixed-point projection; `N = E - P` is the complementary part.
local notation "P" => fixedPointProj (D := D) ρ htr
local notation "N" => E - P

lemma fixedPointProj_mul_self : P * P = P := by
  ext X
  simp [Module.End.mul_apply, fixedPointProj_idempotent]

/-- `P ∘ N = 0` for `P := fixedPointProj ρ` and `N := E - P`. -/
lemma fixedPointProj_mul_compl (hTP : IsTracePreservingMap E) : P * N = 0 := by
  ext X
  have hPE : P (E X) = P X :=
    LinearMap.congr_fun (fixedPointProj_comp_E (E := E) (ρ := ρ) (htr := htr) hTP) X
  simp [Module.End.mul_apply, hPE, fixedPointProj_idempotent]

/-- `N ∘ P = 0` for `P := fixedPointProj ρ` and `N := E - P`. -/
lemma compl_mul_fixedPointProj (hρ : E ρ = ρ) : N * P = 0 := by
  ext X
  have hEP : E (P X) = P X :=
    LinearMap.congr_fun (E_comp_fixedPointProj (E := E) (ρ := ρ) (htr := htr) hρ) X
  simp [Module.End.mul_apply, hEP, fixedPointProj_idempotent]

/-- `N^(n+1) ∘ P = 0` for all `n`. -/
lemma compl_pow_succ_mul_fixedPointProj (hρ : E ρ = ρ) (n : ℕ) : N ^ (n + 1) * P = 0 := by
  have hNP : N * P = 0 := compl_mul_fixedPointProj (E := E) (ρ := ρ) (htr := htr) hρ
  simp only [pow_succ, mul_assoc, hNP, mul_zero]

/-- For `P := fixedPointProj ρ` and `N := E - P`, we have `E^(n+1) = P + N^(n+1)`.

This is the algebraic core of primitive convergence: the dynamics splits into the fixed-point
part `P` and a complementary part `N` that decays under a spectral gap hypothesis. -/
theorem pow_succ_eq_fixedPointProj_add_compl_pow
    (hTP : IsTracePreservingMap E) (hρ : E ρ = ρ) (n : ℕ) :
    E ^ (n + 1) = P + N ^ (n + 1) := by
  induction n with
  | zero => simp [pow_one]
  | succ n ih =>
      have hPP : P * P = P := fixedPointProj_mul_self (ρ := ρ) (htr := htr)
      have hPN : P * N = 0 := fixedPointProj_mul_compl (E := E) (ρ := ρ) (htr := htr) hTP
      have hNpowP : N ^ (n + 1) * P = 0 :=
        compl_pow_succ_mul_fixedPointProj (E := E) (ρ := ρ) (htr := htr) hρ n
      -- Rewrite E^(n+2) = (P + N^(n+1)) * E, then substitute E = P + N on the right factor only.
      -- We must target the outermost E precisely, as `N = E - P` also contains E.
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

end SpectralGapDecomposition
