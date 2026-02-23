import TNLean.Channel.PositiveMap
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Primitive Quantum Channels

This file contains basic infrastructure toward the theory of **primitive** quantum channels.

At the moment, we formalize the **rank-one projection** onto a fixed point and the
algebraic decomposition
\[
  E^n = P + (E-P)^n \qquad (n \ge 1)
\]
where `P` is the fixed-point projection.

## References
* Wolf, *Quantum Channels & Operations*, Chapter 6
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators NNReal ENNReal
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
  -- `trace (P X) = trace X` uses `htr` to cancel `(trace ρ)⁻¹ * trace ρ`.
  simp [fixedPointProj, div_eq_mul_inv, htr]

theorem fixedPointProj_apply_rho (ρ : Matrix (Fin D) (Fin D) ℂ) (htr : trace ρ ≠ 0) :
    fixedPointProj ρ htr ρ = ρ := by
  simp [fixedPointProj, htr]

theorem fixedPointProj_trace (ρ : Matrix (Fin D) (Fin D) ℂ) (htr : trace ρ ≠ 0) :
    LinearMap.trace ℂ (Matrix (Fin D) (Fin D) ℂ) (fixedPointProj ρ htr) = (1 : ℂ) := by
  let f : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] ℂ :=
    (trace ρ)⁻¹ • Matrix.traceLinearMap (Fin D) ℂ ℂ
  have hP : fixedPointProj ρ htr = f.smulRight ρ := by
    ext X
    simp [fixedPointProj, f, Matrix.traceLinearMap_apply, div_eq_mul_inv, mul_comm]
  rw [hP]
  -- For a rank-one map `X ↦ f(X) • ρ`, the trace is `f(ρ)`.
  simp [f, Matrix.traceLinearMap_apply, htr]

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

/-- `N^n ∘ P = 0` for all `n ≥ 1`. -/
lemma compl_pow_succ_mul_fixedPointProj (hρ : E ρ = ρ) (n : ℕ) : N ^ (n + 1) * P = 0 := by
  -- N^(n+1) * P = (N^n * N) * P = N^n * (N * P) = N^n * 0 = 0
  have hNP : N * P = 0 := compl_mul_fixedPointProj (E := E) (ρ := ρ) (htr := htr) hρ
  simp only [pow_succ, mul_assoc, hNP, mul_zero]

/-- For `P := fixedPointProj ρ` and `N := E - P`, we have `E^(n+1) = P + N^(n+1)`.

This is the algebraic core of primitive convergence: the dynamics splits into the fixed-point
part `P` and a complementary part `N` that decays under a spectral gap hypothesis. -/
theorem pow_succ_eq_fixedPointProj_add_compl_pow
    (hTP : IsTracePreservingMap E) (hρ : E ρ = ρ) (n : ℕ) :
    E ^ (n + 1) = P + N ^ (n + 1) := by
  induction n with
  | zero =>
      -- `E = P + (E - P)`
      simp [pow_one]
  | succ n ih =>
      have hPP : P * P = P := fixedPointProj_mul_self (ρ := ρ) (htr := htr)
      have hPN : P * N = 0 := fixedPointProj_mul_compl (E := E) (ρ := ρ) (htr := htr) hTP
      have hNpowP : N ^ (n + 1) * P = 0 :=
        compl_pow_succ_mul_fixedPointProj (E := E) (ρ := ρ) (htr := htr) hρ n
      have hE : E = P + N := (add_sub_cancel P E).symm
      calc
        E ^ (n + 2) = E ^ (n + 1) * E := by simp [pow_succ]
        _ = (P + N ^ (n + 1)) * E := by simp [ih]
        _ = (P + N ^ (n + 1)) * (P + N) := by
              -- Rewrite only the *right* `E` (do not rewrite the `E` hidden inside `N = E - P`).
              conv_lhs =>
                congr
                · skip
                · rw [hE]
        _ = P + N ^ (n + 2) := by
              -- Expand without simplifying `P + N` back to `E`.
              rw [mul_add, add_mul, add_mul]
              -- Now use `P*P = P`, `P*N = 0`, and `N^(n+1)*P = 0`.
              simp [hPP, hPN, hNpowP]
              simp [pow_succ, mul_assoc]

/-- For `P := fixedPointProj ρ` and `N := E - P`, we have `E^n = P + N^n` for all `n ≥ 1`. -/
theorem pow_eq_fixedPointProj_add_compl_pow
    (hTP : IsTracePreservingMap E) (hρ : E ρ = ρ) {n : ℕ} (hn : 1 ≤ n) :
    E ^ n = P + N ^ n := by
  cases n with
  | zero =>
      cases (Nat.not_succ_le_zero 0 hn)
  | succ n =>
      simpa using
        pow_succ_eq_fixedPointProj_add_compl_pow (E := E) (ρ := ρ) (htr := htr) hTP hρ n

end SpectralGapDecomposition
