/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.RescalingStableChiAttachment

/-!
# Uniform trace-power form for an explicit one-label coefficient model

**Scope: auxiliary coefficient model.** This file continues
`TNLean.MPS.MPDO.RescalingStableChiAttachment`. It proves a uniform
trace-power identity for the hand-defined one-label family `oneLabelCoeffs`
and connects that scalar identity to the local factor `wMat` of the
rescaling-stable example. It does not identify this family with the
coefficients of the existential tensor-attached BNT clause for `R`.

The paper-general form of this statement,
`MPOTensor.PositiveBNTLabelChiTracePowerForm` (`TNLean.MPS.MPDO.BNTCoefficients`),
is a positive length-independent diagonal `χ`-family together with the
positive-length trace-power identity for a BNT-label coefficient family.
It is already same-length and BNT-label-uniform by construction; it is not
the length-dependent blocked-basis analogue
`MPOTensor.AlgebraStructureData.HasBlockedStructureChiTracePowerForm`
(`TNLean.MPS.MPDO.AlgebraStructure`), whose diagonal matrix may depend on the
blocked length. This file instantiates the general predicate for the
explicit family `oneLabelCoeffs`, with `χ = oneLabelChi`, and connects the
resulting trace-power coefficient to the local factor `wMat`.

## Main results

* `oneLabelChiTracePowerForm` — the uniform BNT-label `χ` trace-power witness
  for `oneLabelCoeffs`, with `χ = oneLabelChi`.
* `wMat_pow_trace_eq_oneLabelChi_matrix_pow_trace` — `tr(wMat^L) = tr(χ^L)`
  for every length `L`, since `wMat` is the Walsh–Hadamard conjugate of `χ`
  (`wMat_eq_conj_diagonal_oneLabelChi`).
* `oneLabelCoeffs_coeff_eq_wMat_pow_trace` — the explicit one-label
  coefficient equals `tr(wMat^L) = 1 + (7/25)^L` for every positive length
  `L`.

**Scope restriction (coefficient level only).** These results identify the
trace-power *coefficient* `oneLabelCoeffs.coeff L 0 0 0` with `tr(wMat^L)`,
the trace of the `L`-fold ORDINARY matrix power of the fixed `2x2` matrix
`wMat`. This is a different matrix power from the `N`-fold Kronecker
(tensor) power `wN N` appearing inside `R`'s own closed-operator formula
`mpo_R_eq_B_mul_wN_mul_transpose`; the two agree only at `L = N = 1`. This
file alone does not establish the operator-multiplication closure law of
arXiv:1606.00608, Theorem 4.14(ii). The module
`TNLean.MPS.MPDO.RescalingStableExplicitVerticalBNT` proves that law for the
normalized vertical component and identifies its attached data with
`oneLabelCoeffs` and `oneLabelChi`. The component operator is not the original
horizontal operator `mpo R L`, and no arbitrary rescaling is attached to a
tensor presentation. See `docs/paper-gaps/cpgsv17_blocked_chi_uniformity.tex`.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Theorem 4.14(ii) and lines 995--1010
-/

noncomputable section

namespace MPOTensor.RescalingStableLengthDependentRFP

/-! ### The Hadamard change of basis is a two-sided inverse up to `1/2` -/

/-- `hadamard2` times its own half is the identity. -/
lemma hadamard2_mul_half_hadamard2 :
    hadamard2 * ((1 / 2 : ℂ) • hadamard2) = 1 := by
  rw [Matrix.mul_smul, hadamard2_mul_self, smul_smul, show (1 / 2 : ℂ) * 2 = 1 by norm_num,
    one_smul]

/-- Half of `hadamard2` times `hadamard2` is the identity. -/
lemma half_hadamard2_mul_hadamard2 :
    ((1 / 2 : ℂ) • hadamard2) * hadamard2 = 1 := by
  rw [Matrix.smul_mul, hadamard2_mul_self, smul_smul, show (1 / 2 : ℂ) * 2 = 1 by norm_num,
    one_smul]

/-! ### `wMat` and `oneLabelChi` intertwine the Hadamard change of basis -/

/-- The `Fin 2`-indexed diagonal matrix of `oneLabelChi`'s single block, as
a concretely typed `2x2` matrix (the same term as in
`hadamard2_mul_diagonal_oneLabelChi_mul_hadamard2`). This avoids working
directly with the dependently-typed `oneLabelChi.matrix 0 0 0`
(`Matrix (Fin (oneLabelChi.dim 0 0 0)) (Fin (oneLabelChi.dim 0 0 0)) ℂ`) in
arithmetic with `wMat` and `hadamard2`. -/
def oneLabelChiMatrix2 : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun k : Fin 2 => oneLabelChi.entry 0 0 0 k)

/-- `oneLabelChiMatrix2` is `oneLabelChi.matrix 0 0 0`, at the concrete index
type `Fin 2`. -/
theorem oneLabelChi_matrix_eq_oneLabelChiMatrix2 :
    oneLabelChi.matrix 0 0 0 = oneLabelChiMatrix2 := rfl

/-- The Hadamard change of basis intertwines `χ` and `wMat`:
`hadamard2 * χ = wMat * hadamard2`. Derived from
`hadamard2_mul_diagonal_oneLabelChi_mul_hadamard2` by cancelling one factor
of `hadamard2` using `hadamard2_mul_half_hadamard2`. -/
theorem hadamard2_mul_oneLabelChiMatrix2_eq_wMat_mul_hadamard2 :
    hadamard2 * oneLabelChiMatrix2 = wMat * hadamard2 := by
  have h : hadamard2 * oneLabelChiMatrix2 * hadamard2 = (2 : ℂ) • wMat :=
    hadamard2_mul_diagonal_oneLabelChi_mul_hadamard2
  have step : (hadamard2 * oneLabelChiMatrix2 * hadamard2) * ((1 / 2 : ℂ) • hadamard2) =
      hadamard2 * oneLabelChiMatrix2 := by
    rw [Matrix.mul_assoc, hadamard2_mul_half_hadamard2, Matrix.mul_one]
  rw [h, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    show (2 : ℂ) * (1 / 2 : ℂ) = 1 by norm_num, one_smul] at step
  exact step.symm

/-- The intertwining relation lifts to every power:
`hadamard2 * χ^L = wMat^L * hadamard2`. -/
theorem hadamard2_mul_oneLabelChiMatrix2_pow_eq_wMat_pow_mul_hadamard2 (L : ℕ) :
    hadamard2 * oneLabelChiMatrix2 ^ L = wMat ^ L * hadamard2 := by
  induction L with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc,
        hadamard2_mul_oneLabelChiMatrix2_eq_wMat_mul_hadamard2, ← Matrix.mul_assoc]

/-- **`R`'s local factor and `χ` have the same trace powers at every length.**
The intertwining relation, conjugated back through the Hadamard change of
basis and its half-inverse, shows `tr(wMat^L) = tr(χ^L)` for every `L`
(including `L = 0`). -/
theorem wMat_pow_trace_eq_oneLabelChiMatrix2_pow_trace (L : ℕ) :
    (wMat ^ L).trace = (oneLabelChiMatrix2 ^ L).trace := by
  have h := hadamard2_mul_oneLabelChiMatrix2_pow_eq_wMat_pow_mul_hadamard2 L
  have hχ : oneLabelChiMatrix2 ^ L =
      ((1 / 2 : ℂ) • hadamard2) * wMat ^ L * hadamard2 := by
    have h2 : ((1 / 2 : ℂ) • hadamard2) * (hadamard2 * oneLabelChiMatrix2 ^ L) =
        ((1 / 2 : ℂ) • hadamard2) * (wMat ^ L * hadamard2) := by rw [h]
    simp only [← Matrix.mul_assoc] at h2
    rwa [half_hadamard2_mul_hadamard2, one_mul] at h2
  rw [hχ, Matrix.trace_mul_cycle, hadamard2_mul_half_hadamard2, one_mul]

/-- **`R`'s local factor and `oneLabelChi` have the same trace powers at
every length.** Restatement of
`wMat_pow_trace_eq_oneLabelChiMatrix2_pow_trace` at the dependently-typed
`oneLabelChi.matrix 0 0 0` used by the `DiagonalChiFamily`/
`PositiveBNTLabelChiTracePowerForm` interface. This ties the abstract diagonal
family `oneLabelChi` to `R`'s own closed-operator local factor `wMat`
(`wMat_eq_conj_diagonal_oneLabelChi`). -/
theorem wMat_pow_trace_eq_oneLabelChi_matrix_pow_trace (L : ℕ) :
    (wMat ^ L).trace = (oneLabelChi.matrix 0 0 0 ^ L).trace :=
  wMat_pow_trace_eq_oneLabelChiMatrix2_pow_trace L

/-! ### The explicit one-label model realizes a uniform χ-trace-power witness -/

/-- **The uniform χ-trace-power witness for the explicit one-label model.**
`oneLabelCoeffs`, defined canonically from `oneLabelChi` by
`BNTLabelCoefficientFamily.ofChi`, satisfies the positive-length trace-power
form: the same diagonal matrix gives
`oneLabelCoeffs.coeff L 0 0 0 = tr(oneLabelChi_{0,0,0}^L)` at every positive
length. This declaration does not identify the model with the coefficient
family of the existential tensor-attached clause for `R`. -/
noncomputable def oneLabelChiTracePowerForm :
    PositiveBNTLabelChiTracePowerForm oneLabelCoeffs :=
  PositiveBNTLabelChiTracePowerForm.ofChi oneLabelChi oneLabelChi_posEntries

/-- **The explicit one-label coefficient equals the trace of `wMat^L`.**
For every positive length `L`,
`oneLabelCoeffs.coeff L 0 0 0 = tr(wMat^L)`. The closed form
`tr(wMat^L) = 1 + (7/25)^L` follows from the Walsh–Hadamard diagonalization
and the trace of powers of `oneLabelChi`. This connects the auxiliary
coefficient model to the local factor in the closed-operator formula for `R`;
it does not identify the model with a tensor-attached BNT coefficient family. -/
theorem oneLabelCoeffs_coeff_eq_wMat_pow_trace (L : ℕ) (hL : 0 < L) :
    oneLabelCoeffs.coeff L 0 0 0 = (wMat ^ L).trace := by
  have heq : oneLabelCoeffs.coeff L 0 0 0 = (oneLabelChi.matrix 0 0 0 ^ L).trace :=
    oneLabelChiTracePowerForm.eq_trace_pow L hL 0 0 0
  rw [heq, ← wMat_pow_trace_eq_oneLabelChi_matrix_pow_trace]

end MPOTensor.RescalingStableLengthDependentRFP
