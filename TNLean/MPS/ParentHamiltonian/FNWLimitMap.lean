/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.FNWTransferConvention
import TNLean.MPS.Structure.PrimitiveFixedPoint

/-!
# FNW limiting rank-one map

Fannes--Nachtergaele--Werner, *Communications in Mathematical Physics* 144
(1992), 443--490, equations (5.1)--(5.3), define the transfer map
\(E(B)=\sum_\mu v_\mu Bv_\mu^*\). In the proof of Lemma 5.2, after the
boundary formula (5.5), its rank-one limit is
\(E_\infty(B)=\operatorname{Tr}(\rho B)\,1\) for a trace-one stationary
matrix \(\rho\). We retain the source-normalized formula
\(\operatorname{Tr}(\rho B)/\operatorname{Tr}(\rho)\) so the definition does
not require trace-one normalization.

This module proves the algebraic projection and absorption identities used
before the rho-weighted Hilbert-space estimate. It does not define the
weighted inner product of equation (5.6) or any quantitative decay bound.
-/

open scoped Matrix

namespace MPSTensor

noncomputable section

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- The normalized rank-one limiting map associated with a matrix `ρ` of
nonzero trace. For the trace-one stationary density used by FNW after equation
(5.5), this is exactly \(E_\infty(B)=\operatorname{Tr}(\rho B)\,1\). -/
def fnwLimitMap (ρ : Mat) (_htr : Matrix.trace ρ ≠ 0) : Mat →ₗ[ℂ] Mat where
  toFun B := (Matrix.trace (ρ * B) / Matrix.trace ρ) • 1
  map_add' B C := by
    simp only [Matrix.mul_add, Matrix.trace_add, add_div, add_smul]
  map_smul' c B := by
    simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, mul_div_assoc,
      smul_smul, RingHom.id_apply]

/-- Application formula for the normalized FNW limiting map. -/
@[simp]
theorem fnwLimitMap_apply (ρ B : Mat) (htr : Matrix.trace ρ ≠ 0) :
    fnwLimitMap ρ htr B =
      (Matrix.trace (ρ * B) / Matrix.trace ρ) • 1 := rfl

/-- For the trace-one normalization used in FNW Lemma 5.2, following equations
(5.1)--(5.5), the limiting map is
\(E_\infty(B)=\operatorname{Tr}(\rho B)\,1\). -/
theorem fnwLimitMap_apply_of_trace_eq_one (ρ B : Mat)
    (htr : Matrix.trace ρ = 1) :
    fnwLimitMap ρ (by simp [htr]) B = Matrix.trace (ρ * B) • 1 := by
  simp [fnwLimitMap, htr]

/-- The normalized FNW limiting map is the bilinear trace-pairing adjoint of
the fixed-point projection \(X\mapsto
(\operatorname{Tr}X/\operatorname{Tr}\rho)\rho\). -/
theorem fnwLimitMap_eq_traceAdjointMap_fixedPointProj (ρ : Mat)
    (htr : Matrix.trace ρ ≠ 0) :
    fnwLimitMap ρ htr = Matrix.traceAdjointMap (fixedPointProj ρ htr) := by
  apply LinearMap.ext
  intro B
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  rw [Matrix.trace_traceAdjointMap_mul]
  simp only [fnwLimitMap_apply, fixedPointProj, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.one_mul,
    smul_eq_mul]
  rw [Matrix.trace_mul_comm ρ B, Matrix.trace_mul_comm B ρ]
  field_simp

/-- The normalized FNW limiting map is idempotent on every observable. -/
theorem fnwLimitMap_idempotent (ρ B : Mat) (htr : Matrix.trace ρ ≠ 0) :
    fnwLimitMap ρ htr (fnwLimitMap ρ htr B) = fnwLimitMap ρ htr B := by
  simp [fnwLimitMap, htr]

/-- The normalized FNW limiting map is an idempotent endomorphism. -/
theorem fnwLimitMap_mul_self (ρ : Mat) (htr : Matrix.trace ρ ≠ 0) :
    fnwLimitMap ρ htr * fnwLimitMap ρ htr = fnwLimitMap ρ htr := by
  apply LinearMap.ext
  intro B
  simpa [Module.End.mul_apply] using fnwLimitMap_idempotent ρ B htr

/-- Under left-canonical normalization, the FNW transfer map absorbs its
limiting rank-one map on the left: \(E E_\infty=E_\infty\). This is the
unital identity from FNW equations (5.2)--(5.3). -/
theorem fnwTransferMap_mul_fnwLimitMap (A : MPSTensor d D) (ρ : Mat)
    (htr : Matrix.trace ρ ≠ 0) (hA : IsLeftCanonical A) :
    fnwTransferMap A * fnwLimitMap ρ htr = fnwLimitMap ρ htr := by
  ext B
  simp [Module.End.mul_apply, fnwLimitMap, fnwTransferMap_one A hA]

/-- If `ρ` is stationary for TNLean's transfer map, then the FNW limiting map
absorbs the FNW transfer map on the left:
\(E_\infty E=E_\infty\). Under the convention bridge of equations
(5.1)--(5.3), this is exactly stationarity of `ρ`. -/
theorem fnwLimitMap_mul_fnwTransferMap (A : MPSTensor d D) (ρ : Mat)
    (htr : Matrix.trace ρ ≠ 0)
    (hρ : Kraus.transferMap A ρ = ρ) :
    fnwLimitMap ρ htr * fnwTransferMap A = fnwLimitMap ρ htr := by
  ext B
  simp only [Module.End.mul_apply, fnwLimitMap_apply]
  rw [trace_mul_fnwTransferMap, hρ]

/-- For every positive power, the FNW remainder satisfies
\((E-E_\infty)^n=E^n-E_\infty\). The proof uses only unitality, stationarity,
and the rank-one projection identities, before the weighted norm of FNW
equation (5.6) enters. -/
theorem fnwTransferMap_sub_fnwLimitMap_pow (A : MPSTensor d D) (ρ : Mat)
    (htr : Matrix.trace ρ ≠ 0) (hA : IsLeftCanonical A)
    (hρ : Kraus.transferMap A ρ = ρ) {n : ℕ} (hn : 1 ≤ n) :
    (fnwTransferMap A - fnwLimitMap ρ htr) ^ n =
      fnwTransferMap A ^ n - fnwLimitMap ρ htr := by
  let E := fnwTransferMap A
  let P := fnwLimitMap ρ htr
  have hEP : E * P = P := fnwTransferMap_mul_fnwLimitMap A ρ htr hA
  have hPE : P * E = P := fnwLimitMap_mul_fnwTransferMap A ρ htr hρ
  have hPP : P * P = P := fnwLimitMap_mul_self ρ htr
  have hpowP : ∀ k : ℕ, E ^ k * P = P := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, mul_assoc, hEP, ih]
  change (E - P) ^ n = E ^ n - P
  cases n with
  | zero => omega
  | succ n =>
      induction n with
      | zero => simp
      | succ n ih =>
          rw [pow_succ, ih (by omega), pow_succ]
          simp only [sub_mul, mul_sub, ← pow_succ, hpowP, hPE, hPP]
          abel

/-- A primitive MPS tensor supplies the trace nonvanishing, left-canonical
normalization, and stationarity hypotheses for the FNW remainder identity. -/
theorem IsPrimitiveMPS.fnwTransferMap_sub_fnwLimitMap_pow [NeZero D]
    {A : MPSTensor d D} {ρ : Mat} (hP : IsPrimitiveMPS A ρ)
    {n : ℕ} (hn : 1 ≤ n) :
    (fnwTransferMap A - fnwLimitMap ρ hP.trace_ne_zero) ^ n =
      fnwTransferMap A ^ n - fnwLimitMap ρ hP.trace_ne_zero :=
  MPSTensor.fnwTransferMap_sub_fnwLimitMap_pow
    (A := A) (ρ := ρ) hP.trace_ne_zero hP.norm hP.fixedPoint_is_fixed hn

end

end MPSTensor
