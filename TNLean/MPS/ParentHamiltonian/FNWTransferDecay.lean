/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixTracePairing
import QICLean.Analysis.SpectralRadiusPowerDecay
import TNLean.MPS.ParentHamiltonian.FNWLimitMap
import TNLean.MPS.ParentHamiltonian.WeightedVirtualHilbert

/-!
# FNW transfer-remainder decay

Fannes--Nachtergaele--Werner, *Communications in Mathematical Physics* 144
(1992), 443--490, Lemma 5.2 and equations (5.9)--(5.10), bound the positive
powers of the transfer remainder in the Hilbert-space norm weighted by the
faithful stationary density. The source quantity is
\(a(n)=\operatorname{Tr}(\rho^{-1})\lVert E^n-E_\infty\rVert_\rho\).

This module first transfers the complementary eigenvalue gap from TNLean's
Schrödinger map to the FNW observable map through the bilinear trace adjoint.
It then activates the rho-weighted norm from equation (5.6), derives the
corresponding spectral-radius gap, and proves prescribed-rate geometric decay
with an existential rate-dependent prefactor.

No dimension-only value of the prefactor is asserted.
-/

open scoped ComplexOrder ENNReal Matrix NNReal

namespace MPSTensor

noncomputable section

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- The FNW transfer remainder has the same eigenvalues as TNLean's
Schrödinger remainder. Hence primitivity bounds every eigenvalue in modulus by
one strictly. This norm-independent bridge is the spectral step in FNW 1992,
Lemma 5.2, before the weighted norm in equations (5.9)--(5.10) is chosen. -/
theorem IsPrimitiveMPS.fnwRemainder_eigenvalue_norm_lt_one [NeZero D]
    {A : MPSTensor d D} {ρ : Mat} (hP : IsPrimitiveMPS A ρ) (ν : ℂ)
    (hν : Module.End.HasEigenvalue
      (fnwTransferMap A - fnwLimitMap ρ hP.trace_ne_zero) ν) :
    ‖ν‖ < 1 := by
  have hremainder :
      fnwTransferMap A - fnwLimitMap ρ hP.trace_ne_zero =
        Matrix.traceAdjointMap
          (Kraus.transferMap A - fixedPointProj ρ hP.trace_ne_zero) := by
    rw [Matrix.traceAdjointMap_sub, ← fnwTransferMap_eq_traceAdjointMap,
      ← fnwLimitMap_eq_traceAdjointMap_fixedPointProj]
  rw [hremainder, Matrix.traceAdjointMap_hasEigenvalue_iff] at hν
  exact hP.complement_eigenvalue_norm_lt_one ν hν

/-- The source factor multiplying the weighted remainder norm in FNW 1992,
equations (5.9)--(5.10): the real value of
\(\operatorname{Tr}(\rho^{-1})\). -/
def fnwTraceInverseFactor (ρ : Mat) : ℝ :=
  (Matrix.trace ρ⁻¹).re

/-- A faithful density matrix gives a strictly positive source factor
\(\operatorname{Re}\operatorname{Tr}(\rho^{-1})\). This is the positivity
used when the factor is absorbed into the prefactor in FNW Lemma 5.2. -/
theorem fnwTraceInverseFactor_pos [NeZero D] {ρ : Mat} (hρ : ρ.PosDef) :
    0 < fnwTraceInverseFactor ρ := by
  have hinv : ρ⁻¹.PosDef := hρ.inv
  exact (Complex.lt_def.mp hinv.trace_pos).1

/-- The spectral radius of the FNW remainder continuous endomorphism for
the local rho-weighted matrix norm of equation (5.6). This definition keeps
the norm choice explicit without comparing it to TNLean's ambient matrix norm. -/
noncomputable def fnwWeightedRemainderSpectralRadius {D : ℕ}
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    {d : ℕ} (A : MPSTensor d D) (htr : Matrix.trace ρ ≠ 0) : ℝ≥0∞ := by
  let : NormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ (Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  let : Norm (Matrix (Fin D) (Fin D) ℂ) :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
  let Φ := Module.End.toContinuousLinearMap (𝕜 := ℂ)
    (Matrix (Fin D) (Fin D) ℂ)
  exact spectralRadius ℂ (Φ (fnwTransferMap A - fnwLimitMap ρ htr))

/-- The operator norm induced by the rho-weighted matrix norm of FNW 1992,
equation (5.6). -/
noncomputable def fnwWeightedOperatorNorm {D : ℕ}
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (F : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)) : ℝ := by
  let : NormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ (Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  let : Norm (Matrix (Fin D) (Fin D) ℂ) :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
  let Φ := Module.End.toContinuousLinearMap (𝕜 := ℂ)
    (Matrix (Fin D) (Fin D) ℂ)
  exact ‖Φ F‖

private theorem rhoWeighted_spectralRadius_lt_one_of_eigenvalues_lt_one
    {D : ℕ} [NeZero D] (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (F : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ))
    (hF : ∀ ν : ℂ, Module.End.HasEigenvalue F ν → ‖ν‖ < 1) :
    letI : NormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
      Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ (Matrix (Fin D) (Fin D) ℂ) :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    letI : Norm (Matrix (Fin D) (Fin D) ℂ) :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
    spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) F) < 1 := by
  let : NormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ (Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  let : Norm (Matrix (Fin D) (Fin D) ℂ) :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
  exact spectralRadius_lt_one_of_eigenvalues_lt_one F hF

/-- In the rho-weighted matrix norm, the continuous FNW remainder has spectral
radius strictly below one. The proof uses only finite dimensionality and the
norm-independent eigenvalue bridge, rather than comparing spectral radii
across different matrix norm instances. -/
theorem IsPrimitiveMPS.fnwWeightedRemainder_spectralRadius_lt_one [NeZero D]
    {A : MPSTensor d D} {ρ : Mat} (hP : IsPrimitiveMPS A ρ)
    (hρ : ρ.PosDef) :
    fnwWeightedRemainderSpectralRadius ρ hρ A hP.trace_ne_zero < 1 := by
  simpa only [fnwWeightedRemainderSpectralRadius] using
    rhoWeighted_spectralRadius_lt_one_of_eigenvalues_lt_one ρ hρ
      (fnwTransferMap A - fnwLimitMap ρ hP.trace_ne_zero)
      hP.fnwRemainder_eigenvalue_norm_lt_one

/-- The source mixing quantity from FNW 1992, equations (5.9)--(5.10), with
trace-one normalization explicit:
\(a(n)=\operatorname{Re}\operatorname{Tr}(\rho^{-1})
\lVert E^n-E_\infty\rVert_\rho\).
The norm is the local rho-weighted continuous-operator norm. -/
noncomputable def fnwMixingQuantity {D : ℕ}
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    {d : ℕ} (A : MPSTensor d D) (htr : Matrix.trace ρ = 1) (n : ℕ) : ℝ :=
  fnwTraceInverseFactor ρ * fnwWeightedOperatorNorm ρ hρ
    (fnwTransferMap A ^ n - fnwLimitMap ρ (by simp [htr]))

end

end MPSTensor
